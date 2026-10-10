import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PairingLocalizationIndependence

namespace OAI

/-!
# Mean corrections for localized Riesz pairings

Subtracting the center kernel separates a far-field pairing into its renormalized
part and a correction proportional to the test function's integral. Comparing
localization radii expresses their difference through this mean and a shell integral.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

theorem riesz_far_integral_with_mean_correction {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν η : Measure (Ambient d)) [SFinite ν] [SFinite η]
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν)
    (a : Ambient d) (hk : Integrable (fun y => inner ℝ e (kernel m a y)) η)
    (hraw : Integrable (rieszRawCrossIntegrand m e φ) (ν.prod η)) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod η) ∧
      (∫ q, rieszRawCrossIntegrand m e φ q ∂ν.prod η) =
        (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod η) +
          (∫ x, φ x ∂ν) * (∫ y, inner ℝ e (kernel m a y) ∂η) := by
  have hcorrection := hφ.mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q =>
      rieszRawCrossIntegrand m e φ q - φ q.1 * inner ℝ e (kernel m a q.2) := by
    funext q
    unfold rieszFarIntegrand rieszRawCrossIntegrand
    rw [inner_sub_right]
    ring
  rw [heq]
  refine ⟨hraw.sub hcorrection, ?_⟩
  rw [integral_sub hraw hcorrection,
    integral_prod_mul φ (fun y => inner ℝ e (kernel m a y))]
  ring

theorem finite_pairing_eq_renormalized_with_mean {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν] (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν) (hφzero : ∀ x ∉ ball a R, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) =
      rieszScalarPairing m ν a R e φ +
        (∫ x, φ x ∂ν) * (∫ y in closedExterior a R, inner ℝ e (kernel m a y) ∂ν) := by
  obtain ⟨hraw, hsplit⟩ := riesz_pairing_split m e ν (ball a R) measurableSet_ball φ hφzero hF
  rw [← closedExterior_eq_compl_ball a R] at hraw hsplit
  have hk := Integrable.const_inner (𝕜 := ℝ) e
    (center_kernel_integrable_finite_exterior m ν a R hR)
  have heq := (riesz_far_integral_with_mean_correction m e
    (ν.restrict (ball a R)) (ν.restrict (closedExterior a R)) φ hφ.restrict a hk hraw).2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hφzero] at heq
  rw [hsplit, heq]
  unfold rieszScalarPairing
  dsimp only
  ring

theorem finite_rieszScalarPairing_radius_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (φ : Ambient d → ℝ) (hφ : Integrable φ ν)
    (hφzero : ∀ x ∉ ball a r, φ x = 0)
    (hF : Integrable (rieszInteriorIntegrand m e φ) (ν.prod ν)) :
    rieszScalarPairing m ν a R e φ - rieszScalarPairing m ν a r e φ =
      (∫ x, φ x ∂ν) * (∫ y in ball a R \ ball a r, inner ℝ e (kernel m a y) ∂ν) := by
  have hR : 0 < R := hr.trans_le hrR
  have hφzeroR : ∀ x ∉ ball a R, φ x = 0 :=
    fun x hx => hφzero x (fun hin => hx ((ball_subset_ball hrR) hin))
  have hs := finite_pairing_eq_renormalized_with_mean m e ν a r hr φ hφ hφzero hF
  have ht := finite_pairing_eq_renormalized_with_mean m e ν a R hR φ hφ hφzeroR hF
  have hk := Integrable.const_inner (𝕜 := ℝ) e
    (center_kernel_integrable_finite_exterior m ν a r hr)
  have hsub : closedExterior a R ⊆ closedExterior a r := fun _ hy => hrR.trans hy
  have hdiff := setIntegral_sdiff (closedExterior_measurable a R) hk hsub
  have hset : closedExterior a r \ closedExterior a R = ball a R \ ball a r := by
    ext y
    simp only [closedExterior_eq_compl_ball, Set.mem_sdiff, mem_compl_iff, not_not]
    tauto
  rw [hset] at hdiff
  rw [hdiff]
  nlinarith [hs, ht]

theorem rieszScalarPairing_radius_difference {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H r R : ℝ) (hH : 0 ≤ H) (hr : 0 < r)
    (hHr : 2 * H ≤ r) (hrR : r ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    rieszScalarPairing (p + 1) μ a R e φ - rieszScalarPairing (p + 1) μ a r e φ =
      (∫ x, φ x ∂μ) *
        (∫ y in ball a R \ ball a r, inner ℝ e (kernel (p + 1) a y) ∂μ) := by
  have hR : 0 < R := hr.trans_le hrR
  have hφzero : ∀ x ∉ ball a r, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H < r))
  have hfarR := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg
    e φ L hφ a H R hH hR (hHr.trans hrR) hsupport
  have hfarr := rieszFarIntegrand_integrable_of_compact_lipschitz (p + 1) C μ hg
    e φ L hφ a H r hH hr hHr hsupport
  have hlimR := rieszScalarPairing_outer_limit (p + 1) μ a R e φ hfarR
  have hlimr := rieszScalarPairing_outer_limit_at_center (p + 1) μ a a r R
    (by simpa only [dist_self, add_zero] using! hrR) e φ hfarr
  have ht := hlimR.sub hlimr
  have heq : (fun k : ℕ =>
      rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius R k))) a R e φ -
        rieszScalarPairing (p + 1) (μ.restrict (ball a (outerPairRadius R k))) a r e φ) =
      fun _ => (∫ x, φ x ∂μ) *
        (∫ y in ball a R \ ball a r, inner ℝ e (kernel (p + 1) a y) ∂μ) := by
    funext k
    let T := outerPairRadius R k
    let ν := μ.restrict (ball a T)
    have hRT : R ≤ T := outerPairRadius_ge R k
    have hT : 0 < T := hR.trans_le hRT
    let : IsFiniteMeasure ν :=
      finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T hT
    have hφI : Integrable φ ν :=
      (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a T hT).integrable (by norm_num)
    have hF := rieszInteriorIntegrand_integrable_of_lipschitz p C ν
      (globalGrowth_restrict (p + 1) C μ hg (ball a T)) e φ L hφ (2 * T) (by positivity)
      (ball_restriction_pair_diameter μ a T)
    have hid := finite_rieszScalarPairing_radius_difference (p + 1) e ν a r R hr hrR
      φ hφI hφzero hF
    have hm : (∫ x, φ x ∂ν) = ∫ x, φ x ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hφzero x (fun hin => hx ((ball_subset_ball (hrR.trans hRT)) hin)))
    have hμshell : ν.restrict (ball a R \ ball a r) = μ.restrict (ball a R \ ball a r) := by
      rw [show ν = μ.restrict (ball a T) from rfl,
        Measure.restrict_restrict (measurableSet_ball.diff measurableSet_ball),
        inter_eq_left.mpr (sdiff_subset.trans (ball_subset_ball hRT))]
    rw [hm, hμshell] at hid
    exact hid
  rw [heq] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

theorem rieszScalarPairing_sub_of_integrable {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (a : Ambient d) (R : ℝ) (e : Ambient d)
    (φ ψ : Ambient d → ℝ)
    (hIφ : Integrable (rieszInteriorIntegrand m e φ)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))))
    (hIψ : Integrable (rieszInteriorIntegrand m e ψ)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R))))
    (hFφ : Integrable (rieszFarIntegrand m e φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))))
    (hFψ : Integrable (rieszFarIntegrand m e ψ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    rieszScalarPairing m μ a R e (fun x => φ x - ψ x) =
      rieszScalarPairing m μ a R e φ - rieszScalarPairing m μ a R e ψ := by
  have hi : rieszInteriorIntegrand m e (fun x => φ x - ψ x) =
      fun q => rieszInteriorIntegrand m e φ q - rieszInteriorIntegrand m e ψ q := by
    funext q
    unfold rieszInteriorIntegrand
    ring
  have hf : rieszFarIntegrand m e (fun x => φ x - ψ x) a =
      fun q => rieszFarIntegrand m e φ a q - rieszFarIntegrand m e ψ a q := by
    funext q
    unfold rieszFarIntegrand
    ring
  unfold rieszScalarPairing
  dsimp only
  rw [hi, hf, integral_sub hIφ hIψ, integral_sub hFφ hFψ]
  ring

end

end RieszRectifiability

end OAI
