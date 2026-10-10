import Mathlib
import OAI.Geometry.HyperbolicGroups.CyclicTriangleBoundary

namespace OAI

section


/-! Explicit obstruction cochains for every individual collared-fan triangle. -/
noncomputable section
namespace HyperbolicObstruction.CyclicTriangleBoundary
attribute [local instance] Classical.propDecidable
variable {B : Type*} [AddCommGroup B]

def cyclePrimitive {m : ℕ} (f : Fin m → B) (i : Fin m) : B :=
  -(∑ j ∈ Finset.Iio i, f j)

lemma cyclePrimitive_difference {m : ℕ} (f : Fin m → B) (hf : ∑ i, f i = 0)
    (i : Fin m) : cyclePrimitive f i - cyclePrimitive f (finRotate m i) = f i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    by_cases hi : i.val < m
    · have hn : (finRotate (m+1) i).val = i.val+1 := by
        simpa only using congrArg Fin.val (finRotate_of_lt hi)
      have he : Finset.Iio (finRotate (m+1) i) = insert i (Finset.Iio i) := by
        ext j
        simp only [Finset.mem_Iio,Finset.mem_insert,Fin.lt_def,Fin.ext_iff,hn]
        omega
      have hii : i ∉ Finset.Iio i := by simp
      simp only [cyclePrimitive,he,Finset.sum_insert hii]
      abel
    · have hil : i = Fin.last m := Fin.ext (by simp; omega)
      have he : Finset.univ = insert i (Finset.Iio i) := by
        ext j
        simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_Iio,Fin.lt_def,
          Fin.ext_iff,true_iff]
        have hj := j.isLt
        have hii := i.isLt
        omega
      have hh : f i + ∑ j ∈ Finset.Iio i, f j = 0 := by
        rw [he,Finset.sum_insert (by simp)] at hf
        exact hf
      have hz : finRotate (m+1) i = 0 := by rw [hil,finRotate_last]
      have he0 : Finset.Iio (0 : Fin (m+1)) = ∅ := by
        ext j; simp [Finset.mem_Iio]
      simp only [cyclePrimitive,hz,he0,Finset.sum_empty,neg_zero,sub_zero]
      exact (eq_neg_of_add_eq_zero_left hh).symm

variable {C E : Type*} (size : C → ℕ) (pos : ∀ c, 0 < size c)
  (edge : Corner size → E →₀ ℤ) (weight : Triangle size → B)
  (L : (E →₀ ℤ) →ₗ[ℤ] B)
  (hL : ∀ c, L (polygonBoundary size edge c) = ∑ i : Fin (size c), ∑ j : Fin 3, weight (⟨c,i⟩,j))

def triangleDiagonal (q : Corner size) : B := L (edge q) - weight (q,0)
def triangleOuter (q : Corner size) : B := triangleDiagonal size edge weight L q - weight (q,1)
def triangleIncrement (q : Corner size) : B :=
  weight (q,0) + weight (q,1) + weight (q,2) - L (edge q)
def triangleApex (q : Corner size) : B :=
  cyclePrimitive (fun i => triangleIncrement size edge weight L ⟨q.1,i⟩) q.2

include hL in
lemma triangleIncrement_sum (c : C) :
    ∑ i : Fin (size c), triangleIncrement size edge weight L ⟨c,i⟩ = 0 := by
  have hh := hL c
  simp only [polygonBoundary,map_sum] at hh
  simp only [triangleIncrement,Finset.sum_sub_distrib]
  rw [hh]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro i hi
  simp [Fin.sum_univ_succ,add_assoc]

include hL in
lemma triangleApex_difference (q : Corner size) :
    triangleApex size edge weight L q - triangleApex size edge weight L (next size q) =
      triangleIncrement size edge weight L q :=
  cyclePrimitive_difference _ (triangleIncrement_sum size edge weight L hL q.1) q.2

include hL in
/-- The literal oriented edge cochain has the given value on every triangle
boundary. Radial edges have zero value; all other edges are explicit. -/
theorem triangle_cochain_extension (q : Corner size) :
    L (edge q) - triangleDiagonal size edge weight L q = weight (q,0) ∧
    triangleDiagonal size edge weight L q - triangleOuter size edge weight L q = weight (q,1) ∧
    triangleOuter size edge weight L q + triangleApex size edge weight L q -
      triangleApex size edge weight L (next size q) = weight (q,2) := by
  constructor
  · simp only [triangleDiagonal]; abel
  constructor
  · simp only [triangleOuter]; abel
  · rw [add_sub_assoc,triangleApex_difference size edge weight L hL]
    simp only [triangleOuter,triangleDiagonal,triangleIncrement]
    abel

end HyperbolicObstruction.CyclicTriangleBoundary
end
end

section

end

end OAI
