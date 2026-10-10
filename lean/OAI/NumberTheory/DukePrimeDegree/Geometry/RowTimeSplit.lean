import OAI.NumberTheory.DukePrimeDegree.Geometry.RowRootChart

namespace OAI

/-!
# Separating one coordinate of the abelian row group

The row time space splits into the kernel of one coordinate and that
real coordinate. Under the row-group parametrization, the final factor
is exactly the corresponding elementary root transvection.
-/

noncomputable section
open Matrix
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rowUnit {n : ℕ} {i j : Fin n} (hij : i ≠ j) : RowTime i :=
  ⟨Pi.single j 1, by
    change (Pi.single j (1 : ℝ) : Fin n → ℝ) i = 0
    simp [hij]⟩

lemma rowUnit_apply_self {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (rowUnit hij).val j = 1 := by simp [rowUnit]

def rowRemainingTimeSpace {n : ℕ} (i j : Fin n) : Submodule ℝ (RowTime i) :=
  LinearMap.ker ((LinearMap.proj j).comp (rowTimeSpace i).subtype)

abbrev RowRemainingTime {n : ℕ} (i j : Fin n) := rowRemainingTimeSpace i j

lemma rowRemainingTime_self {n : ℕ} {i j : Fin n} (a : RowRemainingTime i j) :
    a.val.val j = 0 := a.prop

def rowTimeSplit {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    RowTime i ≃ₜ RowRemainingTime i j × ℝ where
  toFun a := (⟨a - a.val j • rowUnit hij, by
    change (a - a.val j • rowUnit hij).val j = 0
    simp [rowUnit_apply_self]⟩, a.val j)
  invFun z := z.1.val + z.2 • rowUnit hij
  left_inv a := by simp
  right_inv z := by
    have hj : (z.1.val + z.2 • rowUnit hij).val j = z.2 := by
      simp [rowRemainingTime_self, rowUnit_apply_self]
    apply Prod.ext
    · apply Subtype.ext
      change z.1.val + z.2 • rowUnit hij -
        (z.1.val + z.2 • rowUnit hij).val j • rowUnit hij = z.1.val
      rw [hj, add_sub_cancel_right]
    · exact hj
  continuous_toFun := by
    have hc : Continuous (fun a : RowTime i => a.val j) :=
      (continuous_apply j).comp continuous_subtype_val
    exact (Continuous.subtype_mk (continuous_id.sub (hc.smul continuous_const)) _).prodMk hc
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).add (continuous_snd.smul continuous_const)

lemma rowRoot_smul_unit {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    rowRoot i (t • rowUnit hij) = Matrix.SpecialLinearGroup.transvection hij t := by
  apply Subtype.ext
  ext r s
  change (rootRowElement i (t • rowUnit hij).val (rowTime_self _)).val r s = _
  rw [rootRowElement_entry]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply]
  by_cases hr : r = i
  · subst r
    by_cases hs : s = j
    · subst s
      simp [rowUnit]
    · have hjs : j ≠ s := Ne.symm hs
      simp [rowUnit, hs, hjs]
  · have hir : i ≠ r := Ne.symm hr
    simp [hr, hir]

lemma rowRoot_split {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : RowTime i) :
    rowRoot i a = rowRoot i (rowTimeSplit hij a).1.val *
      Matrix.SpecialLinearGroup.transvection hij (rowTimeSplit hij a).2 := by
  rw [← rowRoot_smul_unit, ← rowRoot_add]
  congr 1
  exact ((rowTimeSplit hij).symm_apply_apply a).symm

end DukePrimeDegree

end

end OAI
