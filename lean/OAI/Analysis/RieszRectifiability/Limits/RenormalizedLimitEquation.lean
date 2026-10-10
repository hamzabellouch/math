import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.InheritedHeightTail
import OAI.Analysis.RieszRectifiability.Kernel.HeightPairingExhaustion
import OAI.Analysis.RieszRectifiability.Kernel.LocalTestMoments

namespace OAI

/-!
# Renormalized equation from source moments

Local square-integrability and inherited source-moment tail bounds make the
renormalized height pairing integrable. Exhaustion by bounded projection regions
then turns the vanishing limiting bilinear pairings into a zero ball pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem renormalized_limit_equation_from_source_moments {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ℕ) (e : (ι → ℝ) → Ambient d) (π : Ambient d → ι → ℝ)
    (K Q : ℝ≥0) (hπ : LipschitzWith Q π) (hleft : LeftInverse π e)
    (H₀ R : ℝ) (hH₀ : 0 ≤ H₀) (hR : 0 < R) (hHR : 2 * H₀ ≤ R)
    (M : ℕ) (hM : 2 * R * ((Q : ℝ) + 1) ≤ M)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (C B : ℝ) (hg : GlobalUpperGrowth (p + 1) C ν) (hCB : C * 2 ^ (p + 1) ≤ B)
    (w : ℕ → Ambient d → ℝ) (f : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ H, MemLp f 2 (ν.restrict (boundedProjectionRegion π (e 0) K H)))
    (hlimit : ∀ H, Tendsto (fun j => ∫ x, w j x ^ 2
      ∂(μ j).restrict (boundedProjectionRegion π (e 0) K H)) atTop
      (𝓝 (∫ x, f x ^ 2 ∂ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (hw : ∀ k j, MemLp (w j) 2 ((μ j).restrict
      (ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k))))
    (b : ℝ) (hb0 : 0 ≤ b) (hb2 : b < 2)
    (hbound : ∀ k, ∀ᶠ j in atTop,
      (∫ x in ball (e 0) ((((K : ℝ) + 1) * ((M : ℝ) + 1)) * (2 : ℝ) ^ k), w j x ^ 2 ∂μ j) ≤
        (B * (R * 2 ^ k) ^ (p + 1)) * ((R * 2 ^ k) * b ^ k) ^ 2)
    (henergy : ∀ H, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
      ((ν.restrict (boundedProjectionRegion π (e 0) K H)).prod
        (ν.restrict (boundedProjectionRegion π (e 0) K H))))
    (φ : Ambient d → ℝ) (L D : ℝ≥0) (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hD : ∀ x, |φ x| ≤ (D : ℝ)) (hsupport : ∀ x, φ x ≠ 0 → dist x (e 0) ≤ H₀)
    (hmean : (∫ x, φ x ∂ν) = 0)
    (hzero : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) f φ q.1 q.2
        ∂(ν.restrict (boundedProjectionRegion π (e 0) K H)).prod
          (ν.restrict (boundedProjectionRegion π (e 0) K H)))) atTop (𝓝 0)) :
    heightPairingOn (p + 1) ν (e 0) (ball (e 0) R) f φ = 0 := by
  let s := fun H => boundedProjectionRegion π (e 0) K H
  let (H : ℕ) : IsFiniteMeasure (ν.restrict (s H)) :=
    boundedProjectionRegion_finite ν π (e 0) K H
  let : IsFiniteMeasure (ν.restrict (ball (e 0) R)) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C ν hg (e 0) R hR
  have hcontain := eventually_ball_subset_boundedProjectionRegion e π K Q hπ hleft
  obtain ⟨J, hJ⟩ := (hcontain R).exists
  have hfball : MemLp f 2 (ν.restrict (ball (e 0) R)) :=
    MemLp.mono_measure (Measure.restrict_mono hJ le_rfl) (hf J)
  have hφI : Integrable φ ν := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hφf : Integrable (fun x => φ x * f x) (ν.restrict (ball (e 0) R)) := by
    have hprod : MemLp (fun x => φ x * f x) 1 (ν.restrict (ball (e 0) R)) :=
      (lipschitz_height_memLp_on_ball (p + 1) C ν hg φ L hφ (e 0) R hR).mul hfball
    exact memLp_one_iff_integrable.mp hprod
  have htail := inherited_height_tail_bound (p + 1) e π K Q hπ hleft R hR M hM μ ν
    C B hg hCB w f hfm hf hlimit hw b hb0 hb2 hbound 0
  simp only [pow_zero, mul_one] at htail
  have hfar := (renormalized_far_pairing_integrable_and_bound (p + 1) C ν
    (ν.restrict (ball (e 0) R)) hg f φ hfm hφ.continuous.measurable hφI.restrict hφf
    (e 0) H₀ R hH₀ hR hHR (Eventually.of_forall hsupport) htail.1 _ htail.2).1
  have hfar' : Integrable (renormalizedNormalIntegrand (p + 1) f φ (e 0))
      ((ν.restrict (ball (e 0) R)).prod (ν.restrict (ball (e 0) R)ᶜ)) := by
    rwa [← closedExterior_eq_compl_ball]
  have hφzero : ∀ x ∉ ball (e 0) R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H₀ < R))
  apply heightPairingOn_zero_of_exhaustion (p + 1) ν (e 0) (ball (e 0) R)
    measurableSet_ball R R hR subset_rfl subset_rfl s
    (fun H => (boundedProjectionRegion_isOpen π hπ.continuous (e 0) K H).measurableSet)
    hcontain f φ hφI hφzero hmean (fun H => (hf H).integrable (by norm_num))
    _ hfar' hzero
  intro H
  exact (fractional_bilinear_integrable_and_cap_error p C (ν.restrict (s H))
    (globalGrowth_restrict (p + 1) C ν hg (s H)) f φ hfm ((hf H).integrable (by norm_num))
    L D hφ hD (henergy H) 1 (by norm_num)).1

end

end RieszRectifiability

end OAI
