import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.OscillationTests
import OAI.Analysis.RieszRectifiability.Limits.HeightPairingOuterLimit
import OAI.Analysis.RieszRectifiability.Kernel.SupportedExteriorPairing

namespace OAI

/-!
# Oscillation bounds on localized regions

Lipschitz height functions give integrable far pairings on regions containing a
ball. Localization identifies each such height pairing with the scalar Riesz
pairing, transferring its oscillation estimate to the normalized height.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem region_far_integrable_of_lipschitz_height {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (A s : Set (Ambient d)) (hA : MeasurableSet A) [IsFiniteMeasure (μ.restrict A)]
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hAR : A ⊆ ball a R) (hcontain : ball a R ⊆ s)
    (u φ : Ambient d → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u) (hφm : Measurable φ)
    (hφ : Integrable φ (μ.restrict A)) (hφu : Integrable (fun x => φ x * u x) (μ.restrict A))
    (hzero : ∀ x ∉ A, φ x = 0) (hnear : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    Integrable (renormalizedNormalIntegrand m u φ a) ((μ.restrict s).prod (μ.restrict sᶜ)) := by
  obtain ⟨hi, hb⟩ := weighted_height_closed_tail_bound m C μ hg u K hu a R hR
  have houter := (renormalized_far_pairing_integrable_and_bound m C μ (μ.restrict A) hg u φ
    hu.continuous.measurable hφm hφ hφu a H R hH hR hHR
    (Eventually.of_forall hnear) hi _ hb).1
  exact (renormalized_pairing_complement_bound m μ a R A s hA (hAR.trans hcontain)
    hcontain u φ hzero houter).1

theorem heightPairingOn_region_eq_riesz {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (hg : GlobalUpperGrowth (p + 1) C μ) (e : Ambient d) (u φ : Ambient d → ℝ)
    (K L : ℝ≥0) (hu : LipschitzWith K u) (hφ : LipschitzWith L φ)
    (hdiff : ∀ x y, u x - u y = inner ℝ e (x - y))
    (a : Ambient d) (H R T : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hRT : R ≤ T) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (hins : ball a R ⊆ s) (hout : s ⊆ ball a T)
    (hφI : Integrable φ μ) (hzero : (∫ x, φ x ∂μ) = 0)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hfar : Integrable (renormalizedNormalIntegrand (p + 1) u φ a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    heightPairingOn (p + 1) μ a s u φ = rieszScalarPairing (p + 1) μ a R e φ := by
  have hφball : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra h
    exact hx ((hsupport x h).trans_lt (by linarith : H < R))
  have hφs : ∀ x ∉ s, φ x = 0 := fun x hx => hφball x (fun hin => hx (hins hin))
  have hmean : (∫ x in ball a R, φ x ∂μ) = 0 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hφball).trans hzero
  let ν := μ.restrict (ball a R)
  let : IsFiniteMeasure ν := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have huφ : Integrable (fun x => φ x * u x) ν := by
    have hprod : MemLp (fun x => φ x * u x) 1 ν :=
      (lipschitz_height_memLp_on_ball (p + 1) C μ hg φ L hφ a R hR).mul
        (lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a R hR)
    exact memLp_one_iff_integrable.mp hprod
  obtain ⟨hweight, hweightBound⟩ := weighted_height_closed_tail_bound (p + 1) C μ hg u K hu a R hR
  have hballFar := (renormalized_far_pairing_integrable_and_bound (p + 1) C μ ν hg u φ
    hu.continuous.measurable hφ.continuous.measurable hφI.restrict huφ a H R hH hR hHR
    (Eventually.of_forall hsupport) hweight _ hweightBound).1
  have hw : ∀ k, Integrable u (μ.restrict (ball a (outerPairRadius T k))) := by
    intro k
    have hT : 0 < outerPairRadius T k := hR.trans_le (hRT.trans (outerPairRadius_ge T k))
    let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a _ hT
    exact (lipschitz_height_memLp_on_ball (p + 1) C μ hg u K hu a _ hT).integrable (by norm_num)
  have hF : ∀ k, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) u φ q.1 q.2)
      ((μ.restrict (ball a (outerPairRadius T k))).prod (μ.restrict (ball a (outerPairRadius T k)))) := by
    intro k
    let T' := outerPairRadius T k
    have hT' : 0 < T' := hR.trans_le (hRT.trans (outerPairRadius_ge T k))
    let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a T' hT'
    have hi := rieszInteriorIntegrand_integrable_of_lipschitz p C (μ.restrict (ball a T'))
      (globalGrowth_restrict (p + 1) C μ hg (ball a T')) e φ L hφ (2 * T') (by positivity)
      (ball_restriction_pair_diameter μ a T')
    have heq : rieszInteriorIntegrand (p + 1) e φ =
        fun q : Ambient d × Ambient d => fractionalBilinear (p + 1) u φ q.1 q.2 :=
      funext (rieszInteriorIntegrand_eq_fractionalBilinear (p + 1) e u φ hdiff)
    rwa [heq] at hi
  have hballFar' : Integrable (renormalizedNormalIntegrand (p + 1) u φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R)ᶜ)) := by
    rwa [← closedExterior_eq_compl_ball]
  have heq := heightPairingOn_localization_independent (p + 1) μ a s (ball a R)
    hs measurableSet_ball R T hR hins subset_rfl hout (ball_subset_ball hRT)
    u φ hφI hφs hφball hzero hw hF hfar hballFar'
  exact heq.trans (heightPairingOn_ball_eq_rieszScalarPairing (p + 1) C μ hg e u φ hdiff
    a R hR hφI.restrict hmean hballFar)

theorem normalized_region_pairing_oscillation_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    (hg : GlobalUpperGrowth (p + 1) C μ) (e : Ambient d) (he : ‖e‖ ≤ 1)
    (u φ : Ambient d → ℝ) (K L : ℝ≥0) (hu : LipschitzWith K u) (hφ : LipschitzWith L φ)
    (hdiff : ∀ x y, u x - u y = inner ℝ e (x - y))
    (a : Ambient d) (H R T A v δ : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hRT : R ≤ T) (hHA : H < A) (hδ : 0 < δ)
    (hosc : ScalarOscillationBound (p + 1) μ a A v)
    (s : Set (Ambient d)) (hs : MeasurableSet s) (hins : ball a R ⊆ s) (hout : s ⊆ ball a T)
    (hφI : Integrable φ μ) (hzero : (∫ x, φ x ∂μ) = 0)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (hfar : Integrable (renormalizedNormalIntegrand (p + 1) u φ a)
      ((μ.restrict s).prod (μ.restrict sᶜ))) :
    |heightPairingOn (p + 1) μ a s (fun x => u x / δ) φ| ≤ ((L : ℝ) + 1) * (v / δ) := by
  rw [heightPairingOn_height_div, heightPairingOn_region_eq_riesz p C μ hg e u φ K L hu hφ
    hdiff a H R T hH hR hHR hRT s hs hins hout hφI hzero hsupport hfar,
    abs_div, abs_of_pos hδ]
  have hb := oscillation_bound_for_localized_test p C μ hg a A v (by linarith) hosc e he φ L hφ
    H R hH hR hHR hHA hsupport hzero
  exact (div_le_div_of_nonneg_right hb hδ.le).trans_eq (by ring)

end

end RieszRectifiability

end OAI
