import OAI.Analysis.BoundedHochschild.MultimodularCofaces

namespace OAI

/-! The left and right end faces of the Hochschild differential preserve
ordinary module identities. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

omit [CStarAlgebra M] in
private lemma tail_update_zero {n : ℕ} (x : Fin (n + 1) → M) (a : M) :
    (fun i : Fin n => Function.update x 0 a i.succ) = (fun i => x i.succ) := by
  ext i
  simp

omit [CStarAlgebra M] in
private lemma tail_update_succ {n : ℕ} (x : Fin (n + 1) → M) (k : Fin n) (a : M) :
    (fun i : Fin n => Function.update x k.succ a i.succ) =
      Function.update (fun i => x i.succ) k a := by
  ext i
  by_cases hi : i = k <;> simp [hi]

omit [CStarAlgebra M] in
private lemma init_update_last {n : ℕ} (x : Fin (n + 1) → M) (a : M) :
    (fun i : Fin n => Function.update x (Fin.last n) a i.castSucc) = (fun i => x i.castSucc) := by
  ext i
  exact Function.update_of_ne (ne_of_lt (Fin.castSucc_lt_last i)) a x

omit [CStarAlgebra M] in
private lemma init_update_castSucc {n : ℕ} (x : Fin (n + 1) → M) (k : Fin n) (a : M) :
    (fun i : Fin n => Function.update x k.castSucc a i.castSucc) =
      Function.update (fun i => x i.castSucc) k a := by
  ext i
  by_cases hi : i = k <;> simp [hi]

lemma multimodularAt_leftCoboundary {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (leftCoboundary f) r := by
  constructor
  · intro x
    simp only [leftCoboundary_apply, Function.update_self, tail_update_zero, mul_assoc]
  · intro x
    have hlast : Fin.last (n + 1) = (Fin.last n).succ := rfl
    simp only [leftCoboundary_apply, hlast, tail_update_succ,
      Function.update_of_ne (Ne.symm (Fin.succ_ne_zero (Fin.last n)))]
    rw [hf.right]
    exact (mul_assoc _ _ _).symm
  · intro x j
    by_cases hj : j = 0
    · subst j
      simp only [leftCoboundary_apply, Fin.castSucc_zero, Function.update_self,
        tail_update_zero, tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero (0 : Fin (n + 1))))]
      rw [hf.left]
      exact mul_assoc _ _ _
    · obtain ⟨p, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      simp only [leftCoboundary_apply, Fin.castSucc_succ, tail_update_succ,
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero p.castSucc)),
        Function.update_of_ne (Ne.symm (Fin.succ_ne_zero p.succ))]
      rw [hf.balance]

lemma multimodularAt_rightCoboundary {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (rightCoboundary f) r := by
  constructor
  · intro x
    have hzero : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
    simp only [rightCoboundary_apply, hzero, init_update_castSucc,
      Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last (0 : Fin (n + 1)))))]
    rw [hf.left]
    exact mul_assoc _ _ _
  · intro x
    simp only [rightCoboundary_apply, Function.update_self, init_update_last, mul_assoc]
  · intro x j
    by_cases hj : j = Fin.last n
    · subst j
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
      simp only [rightCoboundary_apply, hlast, init_update_castSucc,
        Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last (Fin.last n)))),
        init_update_last, Function.update_self]
      rw [hf.right]
      exact mul_assoc _ _ _
    · obtain ⟨p, rfl⟩ := Fin.eq_castSucc_of_ne_last hj
      simp only [rightCoboundary_apply, ← Fin.castSucc_succ, init_update_castSucc,
        Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last p.castSucc))),
        Function.update_of_ne (Ne.symm (ne_of_lt (Fin.castSucc_lt_last p.succ)))]
      rw [hf.balance]

lemma multimodularAt_differential {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (differential f) r := by
  change MultimodularAt
    (leftCoboundary f + ∑ j : Fin (n + 1), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j +
      ((-1 : ℂ) ^ (n + 2)) • rightCoboundary f) r
  exact ((multimodularAt_leftCoboundary f r hf).add
    (MultimodularAt.sum Finset.univ _ r (fun j _ =>
      (multimodularAt_middleCoboundary f r hf j).smul _))).add
    ((multimodularAt_rightCoboundary f r hf).smul _)

end BoundedHochschild.KadisonRingrose

end

end OAI
