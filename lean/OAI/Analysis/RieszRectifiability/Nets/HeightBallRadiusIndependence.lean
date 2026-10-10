import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearError
import OAI.Analysis.RieszRectifiability.Kernel.LocalHeightData
import OAI.Analysis.RieszRectifiability.Limits.HeightPairingOuterLimit

namespace OAI

/-!
# Independence of the height-pairing radius

Local square integrability and a weighted tail bound make the renormalized far
pairing integrable. Local fractional energy then permits comparison through common
outer balls, showing that a mean-zero compact test gives the same height pairing
for either admissible localization radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem renormalized_far_integrable_of_ball_L2 {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (a : Ambient d) (f φ : Ambient d → ℝ) (hfm : Measurable f)
    (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hf : MemLp f 2 (μ.restrict (ball a R))) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (hcφ : HasCompactSupport φ) (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (htail : IntegrableOn (fun x => |f x| * inverseDistancePow (m + 2) a x) (closedExterior a R) μ) :
    Integrable (renormalizedNormalIntegrand m f φ a)
      ((μ.restrict (ball a R)).prod (μ.restrict (ball a R)ᶜ)) := by
  let := hg.finite_on_compacts
  let := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hφI : Integrable φ μ := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hprod : MemLp (fun x => φ x * f x) 1 (μ.restrict (ball a R)) :=
    (lipschitz_height_memLp_on_ball m C μ hg φ L hφ a R hR).mul hf
  have h := (renormalized_far_pairing_integrable_and_bound m C μ (μ.restrict (ball a R)) hg
    f φ hfm hφ.continuous.measurable hφI.restrict (memLp_one_iff_integrable.mp hprod)
    a H R hH hR hHR (Eventually.of_forall hsupport) htail _ le_rfl).1
  rwa [closedExterior_eq_compl_ball] at h

theorem heightPairingOn_ball_independent_from_local_energy {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (a : Ambient d) (f φ : Ambient d → ℝ) (hfm : Measurable f)
    (hf : ∀ T : ℝ, 0 < T → MemLp f 2 (μ.restrict (ball a T)))
    (henergy : ∀ T : ℝ, 0 < T → Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) f q.1 q.2)
      ((μ.restrict (ball a T)).prod (μ.restrict (ball a T))))
    (L B : ℝ≥0) (hφ : LipschitzWith L φ) (hcφ : HasCompactSupport φ)
    (hB : ∀ x, |φ x| ≤ (B : ℝ)) (hmean : (∫ x, φ x ∂μ) = 0)
    (H R S : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hS : 0 < S)
    (hHR : 2 * H ≤ R) (hHS : 2 * H ≤ S) (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H)
    (htailR : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) a x) (closedExterior a R) μ)
    (htailS : IntegrableOn (fun x => |f x| * inverseDistancePow (p + 1 + 2) a x) (closedExterior a S) μ) :
    heightPairingOn (p + 1) μ a (ball a R) f φ = heightPairingOn (p + 1) μ a (ball a S) f φ := by
  let := hg.finite_on_compacts
  let T := max R S
  have hT : 0 < T := hR.trans_le (le_max_left _ _)
  have hpos : ∀ k, 0 < outerPairRadius T k := outerPairRadius_pos T hT
  let (k : ℕ) : IsFiniteMeasure (μ.restrict (ball a (outerPairRadius T k))) :=
    finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a (outerPairRadius T k) (hpos k)
  have hzR : ∀ x ∉ ball a R, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H < R))
  have hzS : ∀ x ∉ ball a S, φ x = 0 := by
    intro x hx
    by_contra hn
    exact hx ((hsupport x hn).trans_lt (by linarith : H < S))
  apply heightPairingOn_localization_independent (p + 1) μ a (ball a R) (ball a S)
    measurableSet_ball measurableSet_ball (min R S) T (lt_min hR hS)
    (ball_subset_ball (min_le_left _ _)) (ball_subset_ball (min_le_right _ _))
    (ball_subset_ball (le_max_left _ _)) (ball_subset_ball (le_max_right _ _))
    f φ (hφ.continuous.integrable_of_hasCompactSupport hcφ) hzR hzS hmean
    (fun k => (hf _ (hpos k)).integrable (by norm_num))
  · intro k
    exact (fractional_bilinear_integrable_and_cap_error p C (μ.restrict (ball a (outerPairRadius T k)))
      (globalGrowth_restrict (p + 1) C μ hg (ball a (outerPairRadius T k))) f φ hfm
      ((hf _ (hpos k)).integrable (by norm_num)) L B hφ hB (henergy _ (hpos k)) 1 (by norm_num)).1
  · exact renormalized_far_integrable_of_ball_L2 (p + 1) C μ hg a f φ hfm H R hH hR hHR
      (hf R hR) L hφ hcφ hsupport htailR
  · exact renormalized_far_integrable_of_ball_L2 (p + 1) C μ hg a f φ hfm H S hH hS hHS
      (hf S hS) L hφ hcφ hsupport htailS

end

end RieszRectifiability

end OAI
