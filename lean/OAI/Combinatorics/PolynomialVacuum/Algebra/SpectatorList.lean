import OAI.Combinatorics.PolynomialVacuum.Algebra.CupPrescriptions
import OAI.Combinatorics.PolynomialVacuum.Algebra.BraidTrain

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp

theorem rightSpectators_val {n : ℕ} (i : Fin (n+1)) :
    (rightSpectators i).map Fin.val=List.range' (i.val+1) (n-i.val) := by
  have hm : (rightSpectators i).map Fin.val=
      (List.range (n+1)).filter (fun k => decide (i.val < k)) := by
    rw [← finRange_map_val]
    rw [List.filter_map]
    rfl
  rw [hm]
  apply List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _) (List.pairwise_lt_range')
  intro k
  simp only [List.mem_filter,List.mem_range,decide_eq_true_eq,List.mem_range'_1]
  have hi := i.isLt
  omega

noncomputable def braidList (c : ℂ) (X : ℕ → ℂ) (ks : List ℕ) :
    Module.End ℂ (SpinTensor ℕ ℂ) :=
  ks.foldl (fun A k => siteR k c (X k)*A) 1

theorem braidList_fold (c : ℂ) (X : ℕ → ℂ) (ks : List ℕ)
    (A : Module.End ℂ (SpinTensor ℕ ℂ)) :
    ks.foldl (fun B k => siteR k c (X k)*B) A=braidList c X ks*A := by
  induction ks generalizing A with
  | nil => simp [braidList]
  | cons k ks ih =>
    simp only [List.foldl_cons,braidList]
    rw [ih,ih]
    simp only [mul_one,mul_assoc]

theorem braidList_range (c : ℂ) (X : ℕ → ℂ) (k m : ℕ) :
    braidList c X (List.range' k m)=braidTrain c X k m := by
  induction m generalizing k with
  | zero => simp [braidList,braidTrain]
  | succ m ih =>
    rw [List.range'_succ]
    unfold braidList
    rw [List.foldl_cons,braidList_fold,ih]
    simp [braidTrain]

end PolynomialVacuumAlgebra

end OAI
