import OAI.Analysis.Pureness.Comparison.SpatialTensorOperators
import OAI.Analysis.Pureness.Stabilization.CompactMatrixUnits
import OAI.Analysis.Pureness.Stabilization.MatrixSystem

namespace OAI
noncomputable section
open scoped TensorProduct InnerProductSpace CStarAlgebra
open UniformSpace.Completion
namespace CuntzComparison
open CuntzTrace
variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
abbrev StabilizationHilbert (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  SpatialHilbert H StandardHilbert
abbrev StabilizationOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  StabilizationHilbert H →L[ℂ] StabilizationHilbert H

def spatialEntry (i j : ℕ) (a : A) : StabilizationOperators H :=
  spatialTensorOp (π a) (compactMatrixUnit i j : StandardHilbert →L[ℂ] StandardHilbert)

@[simp] lemma spatialEntry_zero (i j : ℕ) : spatialEntry π i j 0 = 0 := by simp [spatialEntry]
@[simp] lemma spatialEntry_add (i j : ℕ) (a b : A) :
    spatialEntry π i j (a+b) = spatialEntry π i j a + spatialEntry π i j b := by
  simp [spatialEntry, spatialTensorOp_add_left]
@[simp] lemma spatialEntry_smul (i j : ℕ) (c : ℂ) (a : A) :
    spatialEntry π i j (c • a) = c • spatialEntry π i j a := by
  simp [spatialEntry, spatialTensorOp_smul_left]
@[simp] lemma spatialEntry_star (i j : ℕ) (a : A) :
    star (spatialEntry π i j a) = spatialEntry π j i (star a) := by
  rw [spatialEntry, ← spatialTensorOp_star, ← map_star]
  congr 1
  exact congrArg Subtype.val (compactMatrixUnit_star i j)
@[simp] lemma spatialEntry_mul (i j k l : ℕ) (a b : A) :
    spatialEntry π i j a * spatialEntry π k l b =
      if j=k then spatialEntry π i l (a*b) else 0 := by
  rw [spatialEntry, spatialEntry, ← spatialTensorOp_mul, ← map_mul]
  have h := congrArg Subtype.val (compactMatrixUnit_mul i j k l)
  change (compactMatrixUnit i j : StandardHilbert →L[ℂ] StandardHilbert) *
    (compactMatrixUnit k l : StandardHilbert →L[ℂ] StandardHilbert) = _ at h
  rw [h]
  split_ifs <;> simp_all [spatialEntry]

lemma spatialEntry_sum {ι : Type*} (s : Finset ι) (i j : ℕ) (f : ι → A) :
    spatialEntry π i j (∑ k ∈ s, f k) = ∑ k ∈ s, spatialEntry π i j (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp [hk,ih]

def spatialMatrixSum {n : ℕ} (M : Fin n → Fin n → A) : StabilizationOperators H :=
  ∑ i : Fin n, ∑ j : Fin n, spatialEntry π i.val j.val (M i j)
lemma spatialMatrixSum_star {n : ℕ} (M : Fin n → Fin n → A) :
    spatialMatrixSum π (fun i j => star (M j i)) = star (spatialMatrixSum π M) := by
  unfold spatialMatrixSum
  rw [_root_.star_sum (R := StabilizationOperators H)]
  simp only [_root_.star_sum, spatialEntry_star]
  exact Finset.sum_comm

lemma spatialMatrixSum_mul {n : ℕ} (M N : Fin n → Fin n → A) :
    spatialMatrixSum π (fun i j => ∑ k, M i k * N k j) = spatialMatrixSum π M * spatialMatrixSum π N := by
  simp only [spatialMatrixSum, spatialEntry_sum, Finset.sum_mul,
    Finset.mul_sum, spatialEntry_mul, Fin.val_inj]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

def spatialFiniteValue (n : ℕ) (M : FinMatrix A n) : StabilizationOperators H :=
  spatialMatrixSum π (fun i j => M i j)

lemma spatialFiniteValue_star (n : ℕ) (M : FinMatrix A n) :
    spatialFiniteValue π n (star M) = star (spatialFiniteValue π n M) :=
  spatialMatrixSum_star π (fun i j => M i j)

lemma spatialFiniteValue_mul (n : ℕ) (M N : FinMatrix A n) :
    spatialFiniteValue π n (M*N) = spatialFiniteValue π n M * spatialFiniteValue π n N :=
  spatialMatrixSum_mul π (fun i j => M i j) (fun i j => N i j)

def spatialFinite (n : ℕ) : FinMatrix A n →⋆ₙₐ[ℂ] StabilizationOperators H where
  toFun := spatialFiniteValue π n
  map_zero' := by simp [spatialFiniteValue, spatialMatrixSum]
  map_add' M N := by simp [spatialFiniteValue, spatialMatrixSum, Finset.sum_add_distrib]
  map_smul' c M := by simp [spatialFiniteValue, spatialMatrixSum, Finset.smul_sum]
  map_star' := spatialFiniteValue_star π n
  map_mul' := spatialFiniteValue_mul π n

lemma spatialFinite_coefficient (n : ℕ) (M : FinMatrix A n) (i j : Fin n) (x y : H) :
    inner ℂ (spatialFinite π n M (x ⊗ₜ[ℂ] standardVector j.val : H ⊗[ℂ] StandardHilbert))
      (y ⊗ₜ[ℂ] standardVector i.val : H ⊗[ℂ] StandardHilbert) = inner ℂ (π (M i j) x) y := by
  simp [spatialFinite, spatialFiniteValue, spatialMatrixSum, spatialEntry, compactMatrixUnit, InnerProductSpace.rankOne_apply,
    inner_standardVector, sum_inner, Fin.val_inj, apply_ite, coe_zero]

theorem spatialFinite_injective (hπ : Function.Injective π) (n : ℕ) :
    Function.Injective (spatialFinite π n) := by
  intro M N he
  apply CStarMatrix.ext; intro i j
  apply hπ
  apply ContinuousLinearMap.ext; intro x
  apply ext_inner_right ℂ
  intro y
  rw [← spatialFinite_coefficient π n M i j x y, ← spatialFinite_coefficient π n N i j x y, he]

 theorem spatialFinite_isometry [PartialOrder A] [StarOrderedRing A]
    (hπ : Function.Injective π) (n : ℕ) : Isometry (spatialFinite π n) :=
  NonUnitalStarAlgHom.isometry _ (spatialFinite_injective π hπ n)

lemma spatialFinite_successor (n : ℕ) (M : FinMatrix A n) :
    spatialFinite π (n+1) (matrixSuccessor n M) = spatialFinite π n M := by
  simp [spatialFinite, spatialFiniteValue, spatialMatrixSum, Fin.sum_univ_castSucc]

theorem spatialFinite_compatible {n m : ℕ} (h : n ≤ m) (M : FinMatrix A n) :
    spatialFinite π m (matrixInclusion h M) = spatialFinite π n M := by
  change spatialFinite π m (matrixPad h M) = _
  induction m,h using Nat.le_induction with
  | base => rw [matrixPad_self]
  | succ m h ih => rw [matrixPad_succ h, spatialFinite_successor, ih]
end CuntzComparison

end

end OAI
