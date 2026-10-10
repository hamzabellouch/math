import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Cyclic

variable {A : Type*} [Fintype A]

def chainWeight (n : ℕ) (p : Fin n → A → A → ℝ) (x : Fin (n+1) → A) : ℝ :=
  ∏ i, p i (x i.castSucc) (x i.succ)

omit [Fintype A] in
lemma chainWeight_cons (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (a : A) (x : Fin (n+1) → A) :
    chainWeight (n+1) p (Fin.cons a x) =
      p 0 a (x 0) * chainWeight n (fun i => p i.succ) x := by
  unfold chainWeight
  rw [Fin.prod_univ_succ]
  simp

lemma sum_chainWeight (n : ℕ) (p : Fin n → A → A → ℝ)
    (hp : ∀ i y, ∑ x, p i x y = 1) :
    ∑ x : Fin (n+1) → A, chainWeight n p x = (Fintype.card A : ℝ) := by
  induction n with
  | zero => simp [chainWeight]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+2) => A)).sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    change (∑ x : Fin (n+1) → A, ∑ a : A, chainWeight (n+1) p (Fin.cons a x)) = _
    simp_rw [chainWeight_cons]
    simp only [← Finset.sum_mul, hp, one_mul]
    exact ih (fun i => p i.succ) (fun i => hp i.succ)

def deletedWeight (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (r : Fin (n+1)) (x : Fin (n+1) → A) : ℝ :=
  ∏ i, if i = r then 1 else p i (x i) (x (finRotate (n+1) i))

omit [Fintype A] in
lemma deletedWeight_last (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (x : Fin (n+1) → A) :
    deletedWeight n p (Fin.last n) x = chainWeight n (fun i => p i.castSucc) x := by
  unfold deletedWeight chainWeight
  rw [Fin.prod_univ_castSucc]
  simp [finRotate_apply, Fin.coeSucc_eq_succ]

omit [Fintype A] in
lemma deletedWeight_reindex (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (r : Fin (n+1)) (x : Fin (n+1) → A) :
    let e := finCycle (r - Fin.last n)
    deletedWeight n p r x =
      deletedWeight n (fun i => p (e i)) (Fin.last n) (fun i => x (e i)) := by
  dsimp only
  let e := finCycle (r - Fin.last n)
  have helast : e (Fin.last n) = r := by simp [e, finCycle_apply]
  have heq (i : Fin (n+1)) : e i = r ↔ i = Fin.last n := by
    rw [← helast, e.injective.eq_iff]
  have hecomm (i : Fin (n+1)) : e (finRotate (n+1) i) = finRotate (n+1) (e i) := by
    simp only [e, finCycle_apply, finRotate_apply]
    abel
  unfold deletedWeight
  rw [← Equiv.prod_comp e (fun i => if i = r then (1 : ℝ) else p i (x i) (x (finRotate (n+1) i)))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [heq, ← hecomm]
  rfl

lemma sum_deletedWeight (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i y, ∑ x, p i x y = 1) (r : Fin (n+1)) :
    ∑ x : Fin (n+1) → A, deletedWeight n p r x = (Fintype.card A : ℝ) := by
  let e := finCycle (r - Fin.last n)
  have hdel (x : Fin (n+1) → A) : deletedWeight n p r x =
      chainWeight n (fun i => p (e i.castSucc)) (fun i => x (e i)) := by
    rw [deletedWeight_reindex n p r x, deletedWeight_last]
  simp_rw [hdel]
  have he : (∑ x : Fin (n+1) → A,
      chainWeight n (fun i => p (e i.castSucc)) (fun i => x (e i))) =
      ∑ x : Fin (n+1) → A, chainWeight n (fun i => p (e i.castSucc)) x := by
    exact (Equiv.arrowCongr e.symm (Equiv.refl A)).sum_comp _
  rw [he]
  exact sum_chainWeight n _ (fun i => hp (e i.castSucc))

omit [Fintype A] in
lemma deletedWeight_nonneg (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y) (r : Fin (n+1)) (x : Fin (n+1) → A) :
    0 ≤ deletedWeight n p r x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact zero_le_one
  · exact hp _ _ _

omit [Fintype A] in
lemma prod_deletedWeight (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (x : Fin (n+1) → A) :
    ∏ r, deletedWeight n p r x =
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ n := by
  unfold deletedWeight
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have hset : Finset.univ.filter (fun r : Fin (n+1) => ¬ i = r) =
      Finset.univ.erase i := by ext r; simp [ne_comm]
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

omit [Fintype A] in
lemma prod_deletedWeight_rpow (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y) (x : Fin (n+1) → A) :
    (∏ r, (deletedWeight n p r x) ^ (1 / (n+1 : ℝ))) =
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ)) := by
  rw [Real.finsetProd_rpow _ _ (fun r _ => deletedWeight_nonneg n p hp r x),
    prod_deletedWeight,
    ← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hp _ _ _) _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hp _ _ _)]
  congr 1
  ring

theorem sum_cycle_rpow_le_card (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y)
    (hsum : ∀ i y, ∑ x, p i x y = 1) :
    (∑ x : Fin (n+1) → A,
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ)))
        ≤ (Fintype.card A : ℝ) := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ x : Fin (n+1) → A,
          ∏ r, (deletedWeight n p r x) ^ (1 / (n+1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (prod_deletedWeight_rpow n p hp x).symm
    _ ≤ ∑ x : Fin (n+1) → A,
          ∑ r, (1 / (n+1 : ℝ)) * deletedWeight n p r x := by
      apply Finset.sum_le_sum
      intro x _
      apply Real.geom_mean_le_arith_mean_weighted
      · intro r _; positivity
      · simp [hn]
      · intro r _; exact deletedWeight_nonneg n p hp r x
    _ = (Fintype.card A : ℝ) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_deletedWeight n p hsum]
      simp [hn]

end BinaryCoordinateSweeps.Cyclic

end

end OAI
