import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.LocalInteriorRepresentative
import OAI.Analysis.RieszRectifiability.Kernel.FarRieszTransform

namespace OAI

/-!
# Local representatives of renormalized Riesz pairings

The far-field pairing is represented by the scalar far Riesz transform. Adding
this transform to a local interior representative gives the renormalized pairing
on supported Lipschitz tests and preserves local L² integrability.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem far_pairing_eq_scalarFarRieszTransform {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (φ : Ambient d → ℝ) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (a : Ambient d) (H R : ℝ) (hH : 0 ≤ H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hsupport : ∀ x, φ x ≠ 0 → dist x a ≤ H) :
    IntegrableOn (fun x => scalarFarRieszTransform m μ e a R x * φ x) (ball a R) μ ∧
      (∫ q, rieszFarIntegrand m e φ a q
        ∂(μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R))) =
        ∫ x in ball a R, scalarFarRieszTransform m μ e a R x * φ x ∂μ := by
  have hi := rieszFarIntegrand_integrable_of_compact_lipschitz m C μ hg e φ L hφ
    a H R hH hR hHR hsupport
  have heq (x : Ambient d) : (∫ y in closedExterior a R, rieszFarIntegrand m e φ a (x, y) ∂μ) =
      scalarFarRieszTransform m μ e a R x * φ x := by
    simp only [rieszFarIntegrand, integral_const_mul, scalarFarRieszTransform, mul_comm]
  refine ⟨?_, ?_⟩
  · simpa only [heq] using! hi.integral_prod_left
  · rw [integral_prod _ hi]
    simp only [heq]

theorem local_renormalized_pairing_representation {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (e a : Ambient d) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (v : Lp ℝ 2 (μ.restrict (ball a R)))
    (hv : ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
      (∀ x, |φ x| ≤ (B : ℝ)) → (∫ x in ball a R, v x * φ x ∂μ) =
        (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand (p + 1) e φ q
          ∂(μ.restrict (ball a R)).prod (μ.restrict (ball a R)))) :
    MemLp (fun x => v x + scalarFarRieszTransform (p + 1) μ e a R x) 2 (μ.restrict (ball a H)) ∧
      ∀ (φ : Ambient d → ℝ) (L B : ℝ≥0), LipschitzWith L φ →
        (∀ x, |φ x| ≤ (B : ℝ)) → (∀ x, φ x ≠ 0 → dist x a ≤ H) →
        rieszScalarPairing (p + 1) μ a R e φ =
          ∫ x, (v x + scalarFarRieszTransform (p + 1) μ e a R x) * φ x ∂μ := by
  have hsubset : ball a H ⊆ ball a R := ball_subset_ball (by linarith)
  have hvH : MemLp (fun x => v x) 2 (μ.restrict (ball a H)) :=
    MemLp.mono_measure (Measure.restrict_mono_set μ hsubset) (Lp.memLp v)
  refine ⟨hvH.add (scalarFarRieszTransform_memLp_inner_ball (p + 1) C μ hg e a H R hH hR hHR), ?_⟩
  intro φ L B hφ hB hs
  let := finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
  have hφ₂ : MemLp φ 2 (μ.restrict (ball a R)) :=
    MemLp.of_bound hφ.continuous.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using! hB x)
  have hiv : IntegrableOn (fun x => v x * φ x) (ball a R) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp v).mul hφ₂)
  obtain ⟨hif, hfar⟩ := far_pairing_eq_scalarFarRieszTransform (p + 1) C μ hg e φ L hφ
    a H R hH.le hR hHR hs
  calc
    _ = (∫ x in ball a R, v x * φ x ∂μ) +
        ∫ x in ball a R, scalarFarRieszTransform (p + 1) μ e a R x * φ x ∂μ := by
      unfold rieszScalarPairing
      dsimp only
      rw [← hv φ L B hφ hB, hfar]
    _ = ∫ x in ball a R, (v x + scalarFarRieszTransform (p + 1) μ e a R x) * φ x ∂μ := by
      rw [← integral_add hiv hif]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : φ x = 0 := by
        by_contra hn
        exact hx ((hs x hn).trans_lt (by linarith : H < R))
      rw [hz, mul_zero]

end

end RieszRectifiability

end OAI
