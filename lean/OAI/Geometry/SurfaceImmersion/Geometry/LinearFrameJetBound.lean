import OAI.Geometry.SurfaceImmersion.Atlas.LinearPhaseTwoJetBounds
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseFrameMargins

namespace OAI

/-! Explicit two-jet bounds in linear coordinates, without compact-range
constants depending on the chosen phase. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4

namespace WeightedEstimates
open SmallModes

theorem WeightedBound.comp_linear_equiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set Base} (hU : UniqueDiffOn ℝ U)
    {f : Base → E} {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (L : Base ≃L[ℝ] Base) (hD : 1 ≤ D) (hL : ‖L.toContinuousLinearMap‖ ≤ D)
    (hb : WeightedBound U s m C f) :
    WeightedBound (L ⁻¹' U) s m (C*D^m) (f ∘ L) := by
  intro j hj x hx
  rw [L.iteratedFDerivWithin_comp_right f hU hx j]
  have hn := (iteratedFDerivWithin ℝ j f U (L x)).norm_compContinuousLinearMap_le
    (fun _ => L.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  calc
    _ ≤ s^j*(‖iteratedFDerivWithin ℝ j f U (L x)‖*‖L.toContinuousLinearMap‖^j) :=
      mul_le_mul_of_nonneg_left hn (pow_nonneg hs _)
    _ = (s^j*‖iteratedFDerivWithin ℝ j f U (L x)‖)*‖L.toContinuousLinearMap‖^j := by ring
    _ ≤ C*D^m := mul_le_mul (hb j hj (L x) hx)
      ((pow_le_pow_left₀ (norm_nonneg _) hL j).trans (pow_le_pow_right₀ hD hj))
      (pow_nonneg (norm_nonneg _) _) hC

end WeightedEstimates

namespace RealModes
open SmallModes WeightedEstimates

theorem realTwoJet_linear_prefix_bound {U : Set Base} (hU : IsOpen U)
    {F : RField 4} (hF : ContDiff ℝ ∞ F) {s C D : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (L : Base ≃L[ℝ] Base) (hD : 1 ≤ D) (hL : ‖L.toContinuousLinearMap‖ ≤ D)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) F) :
    WeightedBound (L ⁻¹' U) s m (C*D^(m+2)) (realTwoJet (F ∘ L)) := by
  apply realTwoJet_prefix_bound_on (hU.preimage L.continuous) (hF.comp L.contDiff) hs hs1
    (mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) _))
  intro j hj
  have hh := (hb j hj).comp_linear_equiv hU.uniqueDiffOn zero_le_one
    (div_nonneg hC (pow_nonneg hs.le _)) L hD hL
  apply hh.mono_const
  calc
    C/s^(j-2)*D^j = (C*D^j)/s^(j-2) := by ring
    _ ≤ (C*D^(m+2))/s^(j-2) := by
      gcongr

end RealModes
end ClosedSurfaceR4

end

end OAI
