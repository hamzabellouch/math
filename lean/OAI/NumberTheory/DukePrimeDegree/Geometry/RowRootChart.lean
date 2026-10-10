import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereCoordinates

namespace OAI

/-!
# Simultaneous coordinates for a full row of roots

The expanding group for a canonical diagonal flow is a full row (or,
after transposition, a column). A nonzero pivot provides a global chart
separating all its root coordinates simultaneously. This constructs the
ambient chart needed for the abelian case of the product theorem.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

def rowTimeSpace {n : ℕ} (i : Fin n) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (LinearMap.proj i)

abbrev RowTime {n : ℕ} (i : Fin n) := rowTimeSpace i

lemma rowTime_self {n : ℕ} {i : Fin n} (a : RowTime i) : a.val i = 0 := a.prop

def rowRoot {n : ℕ} (i : Fin n) (a : RowTime i) : G n :=
  rootRowElement i a.val (rowTime_self a)

lemma mul_rowRoot_entry {n : ℕ} (i : Fin n) (a : RowTime i) (g : G n)
    (r s : Fin n) : (g * rowRoot i a).val r s = g.val r s + g.val r i * a.val s := by
  change (g.val * (1 + Matrix.vecMulVec (Pi.single i 1) a.val)) r s = _
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec]
  simp [Matrix.vecMulVec_apply]

lemma rowRoot_add {n : ℕ} (i : Fin n) (a b : RowTime i) :
    rowRoot i (a + b) = rowRoot i a * rowRoot i b := by
  apply Subtype.ext
  ext r s
  rw [mul_rowRoot_entry]
  change (rootRowElement i (a + b).val _).val r s =
    (rootRowElement i a.val _).val r s + (rootRowElement i a.val _).val r i * b.val s
  simp only [rootRowElement_entry, Submodule.coe_add, Pi.add_apply, rowTime_self]
  by_cases hr : r = i
  · subst r
    simp only [ite_true, Matrix.one_apply_eq, add_zero]
    ring
  · simp [hr, Matrix.one_apply]

lemma rowRoot_zero {n : ℕ} (i : Fin n) : rowRoot i 0 = 1 := by
  apply Subtype.ext
  ext r s
  simp [rowRoot, rootRowElement_entry]

lemma continuous_rowRoot {n : ℕ} (i : Fin n) : Continuous (rowRoot i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  change Continuous (fun a : RowTime i => (rootRowElement i a.val (rowTime_self a)).val r s)
  simp only [rootRowElement_entry]
  split_ifs
  · exact continuous_const.add ((continuous_apply s).comp continuous_subtype_val)
  · exact continuous_const.add continuous_const

abbrev RowRootSlice {n : ℕ} (i k : Fin n) :=
  {g : G n // g.val k i ≠ 0 ∧ ∀ j : Fin n, j ≠ i → g.val k j = 0}

def rowRootParameter {n : ℕ} (i k : Fin n) (g : G n) : RowTime i :=
  ⟨fun j => if j = i then 0 else g.val k j / g.val k i, by
    change (if i = i then 0 else g.val k i / g.val k i) = 0
    simp⟩

def rowPivotTranslate {n : ℕ} {i k : Fin n}
    (g : RootPivot i k) (a : RowTime i) : RootPivot i k :=
  ⟨g.val * rowRoot i a, by simpa only [mul_rowRoot_entry, rowTime_self, mul_zero, add_zero] using g.prop⟩

lemma rowRootParameter_translate {n : ℕ} {i k : Fin n}
    (g : RootPivot i k) (a : RowTime i) :
    rowRootParameter i k (rowPivotTranslate g a).val = rowRootParameter i k g.val + a := by
  apply Subtype.ext
  ext j
  by_cases hji : j = i
  · subst j
    simp [rowRootParameter, rowTime_self]
  · simp only [rowRootParameter, rowPivotTranslate, hji, ite_false,
      Submodule.coe_add, Pi.add_apply]
    simp only [mul_rowRoot_entry, rowTime_self, mul_zero, add_zero]
    field_simp [g.prop]

def rowSliceRepresentative {n : ℕ} {i k : Fin n}
    (g : RootPivot i k) : RowRootSlice i k :=
  ⟨g.val * rowRoot i (-rowRootParameter i k g.val), by
    constructor
    · simpa only [mul_rowRoot_entry, rowTime_self, mul_zero, add_zero] using g.prop
    · intro j hji
      rw [mul_rowRoot_entry]
      change g.val.val k j + g.val.val k i *
        (-(if j = i then 0 else g.val.val k j / g.val.val k i)) = 0
      simp only [hji, ite_false]
      field_simp [g.prop]
      ring⟩

lemma rowSliceRepresentative_translate {n : ℕ} {i k : Fin n}
    (g : RootPivot i k) (a : RowTime i) :
    rowSliceRepresentative (rowPivotTranslate g a) = rowSliceRepresentative g := by
  apply Subtype.ext
  change (g.val * rowRoot i a) * rowRoot i
    (-rowRootParameter i k (rowPivotTranslate g a).val) =
      g.val * rowRoot i (-rowRootParameter i k g.val)
  rw [rowRootParameter_translate, mul_assoc, ← rowRoot_add]
  congr 2
  abel

lemma continuous_rowRootParameter {n : ℕ} {i k : Fin n} :
    Continuous (fun g : RootPivot i k => rowRootParameter i k g.val) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous (fun g : RootPivot i k => if j = i then 0 else g.val.val k j / g.val.val k i)
  split_ifs
  · exact continuous_const
  · exact continuous_rootParameter

lemma continuous_rowSliceRepresentative {n : ℕ} {i k : Fin n} :
    Continuous (rowSliceRepresentative (i := i) (k := k)) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.mul
    ((continuous_rowRoot i).comp continuous_rowRootParameter.neg)

def rowPivotHomeomorph {n : ℕ} (i k : Fin n) :
    RootPivot i k ≃ₜ RowRootSlice i k × RowTime i where
  toFun g := (rowSliceRepresentative g, rowRootParameter i k g.val)
  invFun z := rowPivotTranslate ⟨z.1.val, z.1.prop.1⟩ z.2
  left_inv g := by
    apply Subtype.ext
    change (g.val * rowRoot i (-rowRootParameter i k g.val)) *
      rowRoot i (rowRootParameter i k g.val) = g.val
    rw [mul_assoc, ← rowRoot_add, neg_add_cancel, rowRoot_zero, mul_one]
  right_inv z := by
    have hp : rowRootParameter i k z.1.val = 0 := by
      apply Subtype.ext
      ext j
      by_cases hji : j = i
      · simp [rowRootParameter, hji]
      · simp [rowRootParameter, hji, z.1.prop.2 j hji]
    apply Prod.ext
    · change rowSliceRepresentative (rowPivotTranslate ⟨z.1.val, z.1.prop.1⟩ z.2) = z.1
      rw [rowSliceRepresentative_translate]
      apply Subtype.ext
      change z.1.val * rowRoot i (-rowRootParameter i k z.1.val) = _
      rw [hp, neg_zero, rowRoot_zero, mul_one]
    · simpa only [hp, zero_add] using
        rowRootParameter_translate ⟨z.1.val, z.1.prop.1⟩ z.2
  continuous_toFun := continuous_rowSliceRepresentative.prodMk continuous_rowRootParameter
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_fst).mul
      ((continuous_rowRoot i).comp continuous_snd)

end DukePrimeDegree

end

end OAI
