import OAI.NumberTheory.DukePrimeDegree.Geometry.RowRootBox
import OAI.NumberTheory.DukePrimeDegree.Geometry.RowTimeSplit

namespace OAI

/-!
# Compatibility of row charts and one-root charts

Removing one coordinate from the row time space gives precisely the
transversal of the existing one-root chart. The parameterizations agree
pointwise, so their disintegrations refer to the same actual root leaves.
-/

noncomputable section
open Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rowReducedHomeomorph {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    RootSlice i j k ≃ₜ RowRootSlice i k × RowRemainingTime i j where
  toFun s := (rowSliceRepresentative ⟨s.val, s.prop.1⟩,
    ⟨rowRootParameter i k s.val, by
      change (if j = i then 0 else s.val.val k j / s.val.val k i) = 0
      simp [hij.symm, s.prop.2]⟩)
  invFun z := ⟨z.1.val * rowRoot i z.2.val, by
    constructor
    · simpa only [mul_rowRoot_entry, rowTime_self, mul_zero, add_zero] using z.1.prop.1
    · rw [mul_rowRoot_entry, z.1.prop.2 j hij.symm, rowRemainingTime_self, mul_zero, add_zero]⟩
  left_inv s := by
    apply Subtype.ext
    exact congrArg (fun p : RootPivot i k => p.val)
      ((rowPivotHomeomorph i k).left_inv ⟨s.val, s.prop.1⟩)
  right_inv z := by
    have h := (rowPivotHomeomorph i k).right_inv (z.1, z.2.val)
    apply Prod.ext
    · exact congrArg (fun p : RowRootSlice i k × RowTime i => p.1) h
    · apply Subtype.ext
      exact congrArg (fun p : RowRootSlice i k × RowTime i => p.2) h
  continuous_toFun := by
    have hb : Continuous (fun s : RootSlice i j k => (⟨s.val, s.prop.1⟩ : RootPivot i k)) :=
      continuous_subtype_val.subtype_mk _
    exact (continuous_rowSliceRepresentative.comp hb).prodMk
      ((continuous_rowRootParameter.comp hb).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rowRoot i).comp (continuous_subtype_val.comp continuous_snd))

/-- The single-root and simultaneous-row parameterizations agree, with
the selected real parameter occupying the last factor. -/
theorem row_one_root_parametrization {n : ℕ} {i j : Fin n} (hij : i ≠ j) (k : Fin n)
    (s : RowRootSlice i k) (w : RowRemainingTime i j) (t : ℝ) :
    rootQuotientParametrization hij ((rowReducedHomeomorph hij k).symm (s, w), t) =
      rowQuotientParametrization i k (s, w.val + t • rowUnit hij) := by
  change Quotient.mk _ ((s.val * rowRoot i w.val) *
      Matrix.SpecialLinearGroup.transvection hij t) =
    Quotient.mk _ (s.val * rowRoot i (w.val + t • rowUnit hij))
  rw [rowRoot_add, rowRoot_smul_unit, mul_assoc]

end DukePrimeDegree

end

end OAI
