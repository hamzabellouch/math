import OAI.Analysis.BoundedHochschild.MultimodularMerges

namespace OAI

/-! Module balance survives an adjacent-input multiplication, on either
side of the balanced pair. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

lemma merge_balance_before_left {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : k.val < j.val) (hp : p.val + 1 = j.val) (r : M) :
    mergeInputs (Function.update x j.castSucc (x j.castSucc * r)) k =
      Function.update (mergeInputs x k) p.castSucc (mergeInputs x k p.castSucc * r) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  all_goals try simp only [mul_assoc]
  all_goals congr 3 <;> (try apply Fin.ext) <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

lemma merge_balance_before_right {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : k.val < j.val) (hp : p.val + 1 = j.val) (r : M) :
    mergeInputs (Function.update x j.succ (r * x j.succ)) k =
      Function.update (mergeInputs x k) p.succ (r * mergeInputs x k p.succ) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  congr 3
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

lemma merge_balance_after_left {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : j.val < k.val) (hp : p.val = j.val) (r : M) :
    mergeInputs (Function.update x j.castSucc (x j.castSucc * r)) k =
      Function.update (mergeInputs x k) p.castSucc (mergeInputs x k p.castSucc * r) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  congr 3
  apply Fin.ext
  simp only [Fin.val_castSucc]
  omega

lemma merge_balance_after_right {n : ℕ} (x : Fin (n + 2) → M)
    (k j : Fin (n + 1)) (p : Fin n) (hk : j.val < k.val) (hp : p.val = j.val) (r : M) :
    mergeInputs (Function.update x j.succ (r * x j.succ)) k =
      Function.update (mergeInputs x k) p.succ (r * mergeInputs x k p.succ) := by
  ext i
  simp only [mergeInputs, Function.update_apply, Fin.ext_iff, Fin.lt_def,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> try omega
  all_goals try simp_all only
  all_goals try simp only [mul_assoc]
  all_goals congr 3 <;> (try apply Fin.ext) <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega

end BoundedHochschild.KadisonRingrose

end

end OAI
