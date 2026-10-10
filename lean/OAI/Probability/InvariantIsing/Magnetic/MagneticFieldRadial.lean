import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldInverseConvex
import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledSquareOrder
import OAI.Probability.InvariantIsing.Fields.FieldRadialCovariance

namespace OAI

/-! Radial monotonicity of the finite prescribed-magnetization overlap.
The root bias is chosen at the fixed prescribed magnetization at every scale. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma squareContinuation_congr_list {L M : List (ℝ × ℝ≥0)} (he : L = M)
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1)) (hij : i.val = j.val)
    (ζ v s : ℝ) :
    magneticScalarSlabContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ v s =
      magneticScalarSlabContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ v s := by
  subst M
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma magneticFieldLevel_eq_scaled (h : FieldStep) (c : ℝ≥0)
    (i : Fin (h.depth + 1)) {s : ℝ} (hs : |s| < 1) :
    magneticFieldLevel (fieldScaleCovariance h c) s i =
      magneticScaledSquareContinuation (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
        c (Fin.cast (by rw [scalarFieldIncrements_length]) i) 0 (h.height 0, s) := by
  rw [congrFun (magneticFieldLevel_eq_slab (fieldScaleCovariance h c) i) s]
  unfold magneticScaledSquareContinuation magneticScaledSquareJet
  rw [closedMagneticContinuation, ite_eq_left hs]
  exact squareContinuation_congr_list (scalarFieldIncrements_scale h c)
    (scalarFieldIncrements_positive (fieldScaleCovariance h c))
    (fieldScaleIncrements_positive c (scalarFieldIncrements h) (scalarFieldIncrements_positive h))
    _ _ rfl 0 ((c : ℝ) ^ 2 * h.height 0) s

theorem magneticFieldLevel_radial (h : FieldStep) {α β : ℝ≥0}
    (hα : 0 < α) (hαβ : α ≤ β) (i : Fin (h.depth + 1)) {s : ℝ} (hs : |s| < 1) :
    magneticFieldLevel (fieldScaleCovariance h α) s i ≤
      magneticFieldLevel (fieldScaleCovariance h β) s i := by
  rw [magneticFieldLevel_eq_scaled h α i hs, magneticFieldLevel_eq_scaled h β i hs]
  exact magneticScaledSquareContinuation_mono (scalarFieldIncrements h)
    (scalarFieldIncrements_positive h) (scalarFieldIncrements_exponent_le_one h)
    hα hαβ _ (by norm_num) (by norm_num) (h.nonneg 0)
    ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩

end InvariantIsing

end

end OAI
