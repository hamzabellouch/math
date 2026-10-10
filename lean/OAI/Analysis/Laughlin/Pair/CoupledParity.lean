import OAI.Analysis.Laughlin.Spin.GenericNormalizedLadder

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem sign_reverse (r p : ℕ) (hp : p ≤ r) :
    (-1 : ℝ)^(r-p) = (-1 : ℝ)^r * (-1 : ℝ)^p := by
  have h : (-1 : ℝ)^p * (-1 : ℝ)^p = 1 := by
    rw [← mul_pow]; norm_num
  calc
    _ = (-1 : ℝ)^(r-p) * ((-1 : ℝ)^p * (-1 : ℝ)^p) := by rw [h,mul_one]
    _ = _ := by rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hp]

theorem highestUnit_reverse (Q r p : ℕ) (hp : p ≤ r) :
    highestUnit Q Q r (r-p) = (-1 : ℝ)^r * highestUnit Q Q r p := by
  unfold highestUnit highestRaw
  rw [ite_eq_left (by omega : r-p ≤ r),ite_eq_left hp,Nat.sub_sub_self hp,
    Nat.choose_symm hp,sign_reverse r p hp]
  rw [mul_comm (Q.choose (r-p) : ℝ) (Q.choose p : ℝ)]
  ring

theorem genericHighest_swap (Q r : ℕ) (hr : r ≤ Q) (i : SpinIndex Q Q) :
    genericHighest Q Q r hr hr i.swap = (-1 : ℝ)^r * genericHighest Q Q r hr hr i := by
  by_cases hi : i.1.val+i.2.val=r
  · let p : Fin (r+1) := ⟨i.1.val,by omega⟩
    let q : Fin (r+1) := ⟨r-i.1.val,by omega⟩
    have h1 : i = weightSliceIndex Q Q r hr hr p := by
      apply Prod.ext
      · rfl
      · apply Fin.ext; dsimp [weightSliceIndex,p]; omega
    have h2 : i.swap = weightSliceIndex Q Q r hr hr q := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [weightSliceIndex,q] <;> omega
    change extendWeightSlice Q Q r hr hr _ i.swap = _ * extendWeightSlice Q Q r hr hr _ i
    rw [h2,h1,extendWeightSlice_at,extendWeightSlice_at]
    exact highestUnit_reverse Q r i.1.val (by omega)
  · change extendWeightSlice Q Q r hr hr _ i.swap = _ * extendWeightSlice Q Q r hr hr _ i
    rw [extendWeightSlice_off _ _ _ _ _ _ i hi,
      extendWeightSlice_off _ _ _ _ _ _ i.swap (by simpa [Nat.add_comm] using hi),mul_zero]

theorem totalLower_swap (Q : ℕ) (f : SpinIndex Q Q → ℝ) (i : SpinIndex Q Q) :
    ((totalRaise Q Q)ᵀ *ᵥ (fun j => f j.swap)) i =
      ((totalRaise Q Q)ᵀ *ᵥ f) i.swap := by
  change (∑ j, totalRaise Q Q j i * f j.swap) =
    ∑ j, totalRaise Q Q j i.swap * f j
  rw [totalRaise_transpose_apply,totalRaise_transpose_apply]
  exact add_comm _ _

theorem genericDescendant_swap (Q r n : ℕ) (hr : r ≤ Q) (i : SpinIndex Q Q) :
    genericDescendant Q Q r hr hr n i.swap =
      (-1 : ℝ)^r * genericDescendant Q Q r hr hr n i := by
  induction n generalizing i with
  | zero => simpa [genericDescendant] using genericHighest_swap Q r hr i
  | succ n ih =>
    rw [genericDescendant_succ]
    rw [← totalLower_swap]
    have he : (fun j => genericDescendant Q Q r hr hr n j.swap) =
      (-1 : ℝ)^r • genericDescendant Q Q r hr hr n := by funext j; exact ih j
    rw [he,Matrix.mulVec_smul]
    rfl

theorem genericUnitDescendant_swap (Q r n : ℕ) (hr : r ≤ Q) (i : SpinIndex Q Q) :
    genericUnitDescendant Q Q r hr hr n i.swap =
      (-1 : ℝ)^r * genericUnitDescendant Q Q r hr hr n i := by
  simp only [genericUnitDescendant,Pi.smul_apply,smul_eq_mul,genericDescendant_swap]
  ring

noncomputable def pairCoupledTensor (Q r : ℕ) (hr : r ≤ Q) (n : ℕ) : SpinIndex Q Q → ℝ :=
  (-1 : ℝ)^r • genericUnitDescendant Q Q r hr hr n

theorem pairCoupledTensor_norm (Q r n : ℕ) (hr : r ≤ Q)
    (hn : n ≤ genericCoupledWeight Q Q r) :
    vectorNormSq (pairCoupledTensor Q r hr n) = 1 := by
  unfold pairCoupledTensor vectorNormSq
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  have h : ((-1 : ℝ)^r)^2 = 1 := by rw [← pow_mul,mul_comm r 2,pow_mul]; norm_num
  rw [h,one_mul]
  exact genericUnitDescendant_norm Q Q r n hr hr hn

theorem pairCoupledTensor_antisymmetric (Q r n : ℕ) (hr : r ≤ Q) (ho : Odd r)
    (i j : Fin (Q+1)) :
    pairCoupledTensor Q r hr n (j,i) = -pairCoupledTensor Q r hr n (i,j) := by
  have h := genericUnitDescendant_swap Q r n hr (i,j)
  have hs : (-1 : ℝ)^r = -1 := ho.neg_one_pow
  simpa [pairCoupledTensor,hs] using congrArg (fun x : ℝ => -x) h

end Laughlin.Spin

end OAI
