import OAI.Analysis.OInfinity.FinitePermutation

namespace OAI

/-! # Joint word rows and their finite coordinate cycle

The row consists of `n` source letters followed by one target letter.
Its coordinate cycle is a finite matrix permutation, with a path bound
independent of `n`. Identifying a different cocycle with this permutation
requires an equality; no nonzero-gauge cocycle is silently substituted.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

def finiteJointWord (s t : I → E) : (n : ℕ) → (Fin (n + 1) → I) → E
  | 0, w => t (w 0)
  | n + 1, w => s (w 0) * finiteJointWord s t n (Fin.tail w)

omit [DecidableEq I] in
private lemma sum_finFunction_succ {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n + 1) → I) → M) :
    (∑ w, f w) = ∑ i, ∑ w : Fin n → I, f (Fin.cons i w) := by
  calc
    _ = ∑ p : I × (Fin n → I), f (Fin.cons p.1 p.2) := by
      exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => I))
        (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

lemma finiteJointWord_support (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (n : ℕ) (w : Fin (n + 1) → I) :
    q * finiteJointWord s t n w = finiteJointWord s t n w ∧
      finiteJointWord s t n w * q = finiteJointWord s t n w := by
  induction n with
  | zero =>
      exact ⟨finiteRow_left_support q t hqstar hqq ht htsum _,
        finiteRow_right_support q t hqstar hqq ht _⟩
  | succ n ih =>
      constructor
      · change q * (s (w 0) * finiteJointWord s t n (Fin.tail w)) = _
        rw [← mul_assoc, finiteRow_left_support q s hqstar hqq hs hsum]
        rfl
      · change (s (w 0) * finiteJointWord s t n (Fin.tail w)) * q = _
        rw [mul_assoc, (ih (Fin.tail w)).2]
        rfl

lemma finiteJointWord_gram (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (n : ℕ) (u v : Fin (n + 1) → I) :
    star (finiteJointWord s t n u) * finiteJointWord s t n v =
      if u = v then q else 0 := by
  induction n with
  | zero =>
      change star (t (u 0)) * t (v 0) = _
      rw [ht]
      congr 1
      exact propext ⟨fun h => funext (fun i => by fin_cases i; exact h),
        fun h => congrFun h 0⟩
  | succ n ih =>
      change star (s (u 0) * finiteJointWord s t n (Fin.tail u)) *
        (s (v 0) * finiteJointWord s t n (Fin.tail v)) = _
      rw [star_mul]
      calc
        _ = star (finiteJointWord s t n (Fin.tail u)) *
            (star (s (u 0)) * s (v 0)) * finiteJointWord s t n (Fin.tail v) := by
          noncomm_ring
        _ = _ := by
          rw [hs]
          by_cases hh : u 0 = v 0
          · rw [ite_eq_left hh, mul_assoc,
              (finiteJointWord_support q s t hqstar hqq hs ht hsum htsum n _).1,
              ih]
            congr 1
            exact propext ⟨fun h => funext (fun i => by
              cases i using Fin.cases
              · exact hh
              · exact congrFun h _), fun h => congrArg Fin.tail h⟩
          · have huv : u ≠ v := fun h => hh (congrFun h 0)
            simp only [hh, huv, ite_false, mul_zero, zero_mul]

lemma finiteJointWord_sum (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q) (n : ℕ) :
    (∑ w, finiteJointWord s t n w * star (finiteJointWord s t n w)) = q := by
  induction n with
  | zero =>
      rw [sum_finFunction_succ]
      simpa only [finiteJointWord, Fin.cons_zero, Finset.univ_unique,
        Finset.sum_singleton] using htsum
  | succ n ih =>
      rw [sum_finFunction_succ]
      simp only [finiteJointWord, Fin.cons_zero, Fin.tail_cons, star_mul]
      calc
        _ = ∑ i, s i * (∑ w, finiteJointWord s t n w *
              star (finiteJointWord s t n w)) * star (s i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w hw
          noncomm_ring
        _ = q := by
          simp only [ih, finiteRow_right_support q s hqstar hqq hs]
          exact hsum

/-- The actual coordinate permutation of the joint word row has a uniform
path, independently of the number of source letters. -/
lemma exists_controlled_jointWordCycle_path [Nontrivial E]
    (q : E) (s t : I → E) (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q) (n : ℕ) :
    ∃ p : Path (1 : unitary E)
        (finiteRowPermutationUnitary q (finiteJointWord s t n) hqstar hqq
          (finiteJointWord_gram q s t hqstar hqq hs ht hsum htsum n)
          (finiteJointWord_sum q s t hqstar hqq hs hsum htsum n)
          (finiteCoordinateCycle (n + 1))),
      ∀ a b, ‖(p a : E) - p b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
  exact exists_controlled_coordinateCycle_path (n + 1) q (finiteJointWord s t n)
    hqstar hqq (finiteJointWord_gram q s t hqstar hqq hs ht hsum htsum n)
    (finiteJointWord_sum q s t hqstar hqq hs hsum htsum n)

end WeakPureInfiniteness

end

end OAI
