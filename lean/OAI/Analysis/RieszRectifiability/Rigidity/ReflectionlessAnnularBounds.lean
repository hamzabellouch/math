import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalizedBumpPairings
import OAI.Analysis.RieszRectifiability.Kernel.RieszPairingMeanCorrection

namespace OAI

/-!
# Annular bounds from scalar reflectionlessness

Scalar reflectionlessness annihilates localized pairings against mean-zero test
functions. Comparing normalized bumps at two radii bounds centered annular kernel
integrals, first in each scalar direction and then in the ambient Euclidean norm.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

def ScalarReflectionlessAt {d : ℕ} (m : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) : Prop :=
  ∀ (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (H R : ℝ),
    LipschitzWith L φ → 0 ≤ H → 0 < R → 2 * H ≤ R →
    (∀ x, φ x ≠ 0 → dist x a ≤ H) → (∫ x, φ x ∂μ) = 0 →
      rieszScalarPairing m μ a R e φ = 0

theorem reflectionless_centered_annular_scalar_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal (c * t ^ (p + 1)) ≤ μ (ball a t))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (e : Ambient d) :
    |∫ y in ball a R \ ball a r, inner ℝ e (kernel (p + 1) a y) ∂μ| ≤
      2 * ‖e‖ * normalizedBumpPairingBound p C c := by
  have hR : 0 < R := hr.trans_le hrR
  let := hg.finite_on_compacts
  let : IsFiniteMeasure (μ.restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  obtain ⟨φ, L, hcφ, hφ, _hnφ, hsφ, hmφ, hbφ⟩ :=
    exists_uniformly_bounded_normalized_bump p C c μ hg hc a (r / 4) (by positivity)
      (hlower _ (by positivity))
  obtain ⟨ψ, K, hcψ, hψ, _hnψ, hsψ, hmψ, hbψ⟩ :=
    exists_uniformly_bounded_normalized_bump p C c μ hg hc a (R / 4) (by positivity)
      (hlower _ (by positivity))
  have hsmall : ∀ x, φ x ≠ 0 → dist x a ≤ R / 2 := by
    intro x hx
    have ht := hsφ x hx
    linarith
  have hlarge : ∀ x, ψ x ≠ 0 → dist x a ≤ R / 2 := by
    intro x hx
    have ht := hsψ x hx
    linarith
  have hdiffsupport : ∀ x, φ x - ψ x ≠ 0 → dist x a ≤ R / 2 := by
    intro x hx
    by_cases hφx : φ x = 0
    · apply hlarge x
      intro hψx
      exact hx (by rw [hφx, hψx, sub_self])
    · exact hsmall x hφx
  have hiφ : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hiψ : Integrable ψ μ := hψ.continuous.integrable_of_hasCompactSupport hcψ
  have hmean : (∫ x, φ x - ψ x ∂μ) = 0 := by
    rw [integral_sub hiφ hiψ, hmφ, hmψ, sub_self]
  have hz := hreflect e (fun x => φ x - ψ x) (L + K) (R / 2) R
    (hφ.sub hψ) (by positivity) hR (by linarith) hdiffsupport hmean
  have hIφ := rieszInteriorIntegrand_integrable_of_lipschitz p C (μ.restrict (ball a R))
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) e φ L hφ (2 * R) (by positivity)
    (ball_restriction_pair_diameter μ a R)
  have hIψ := rieszInteriorIntegrand_integrable_of_lipschitz p C (μ.restrict (ball a R))
    (globalGrowth_restrict (p + 1) C μ hg (ball a R)) e ψ K hψ (2 * R) (by positivity)
    (ball_restriction_pair_diameter μ a R)
  have hFφ := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e φ L hφ
    a (R / 2) R (by positivity) hR (by linarith) hsmall
  have hFψ := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg e ψ K hψ
    a (R / 2) R (by positivity) hR (by linarith) hlarge
  rw [rieszScalarPairing_sub_of_integrable (p + 1) μ a R e φ ψ hIφ hIψ hFφ hFψ] at hz
  have hequal : rieszScalarPairing (p + 1) μ a R e φ =
      rieszScalarPairing (p + 1) μ a R e ψ := sub_eq_zero.mp hz
  have hid := rieszScalarPairing_radius_difference p C μ hg e φ L hφ a (2 * (r / 4))
    r R (by positivity) hr (by linarith) hrR hsφ
  rw [hmφ, one_mul, hequal] at hid
  have hbsmall := hbφ e
  have hbbig := hbψ e
  rw [show 4 * (r / 4) = r by ring] at hbsmall
  rw [show 4 * (R / 4) = R by ring] at hbbig
  rw [← hid]
  calc
    _ ≤ |rieszScalarPairing (p + 1) μ a R e ψ| +
        |rieszScalarPairing (p + 1) μ a r e φ| := by
      simpa only [sub_zero, zero_sub, abs_neg] using!
        abs_sub_le (rieszScalarPairing (p + 1) μ a R e ψ) 0
          (rieszScalarPairing (p + 1) μ a r e φ)
    _ ≤ ‖e‖ * normalizedBumpPairingBound p C c +
        ‖e‖ * normalizedBumpPairingBound p C c := add_le_add hbbig hbsmall
    _ = _ := by ring

theorem reflectionless_centered_annular_vector_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal (c * t ^ (p + 1)) ≤ μ (ball a t))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ‖∫ y in ball a R \ ball a r, kernel (p + 1) a y ∂μ‖ ≤
      2 * normalizedBumpPairingBound p C c := by
  have hR : 0 < R := hr.trans_le hrR
  let : IsFiniteMeasure (μ.restrict (ball a R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hk : IntegrableOn (kernel (p + 1) a) (ball a R \ ball a r) μ := by
    have h := center_kernel_integrable_finite_exterior (p + 1) (μ.restrict (ball a R)) a r hr
    have hset : closedExterior a r ∩ ball a R = ball a R \ ball a r := by
      ext y
      simp only [closedExterior_eq_compl_ball, mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rwa [IntegrableOn, Measure.restrict_restrict (closedExterior_measurable a r), hset] at h
  let v := ∫ y in ball a R \ ball a r, kernel (p + 1) a y ∂μ
  have hb := reflectionless_centered_annular_scalar_bound p C c μ hg hc a hlower hreflect r R hr hrR v
  have heq : (∫ y in ball a R \ ball a r, inner ℝ v (kernel (p + 1) a y) ∂μ) =
      inner ℝ v v := integral_inner (𝕜 := ℝ) hk v
  rw [heq, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hb
  have hD := normalizedBumpPairingBound_nonneg p C c hg.1 hc
  by_cases hv : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv]
    positivity
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    change ‖v‖ ≤ _
    nlinarith

end

end RieszRectifiability

end OAI
