import OAI.Analysis.OInfinity.JointWordCycle

namespace OAI

/-! # The joint-word cycle as a cocycle coboundary

The finite matrix cycle is `W * φ^[n](W*)`, where `W = ∑ tᵢ sᵢ*`.
This is a coboundary of `W`, not the product `W φ(W) ⋯ φ^[n-1](W)`.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

def finiteRowShiftIterate (s : I → E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => finiteRowShift s (finiteRowShiftIterate s n x)

lemma finiteRowShift_support (q : E) (s : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q) (x : E) :
    q * finiteRowShift s x = finiteRowShift s x ∧
      finiteRowShift s x * q = finiteRowShift s x := by
  have hstar (i : I) : star (s i) * q = star (s i) := by
    simpa only [star_mul, hqstar] using
      congrArg star (finiteRow_left_support q s hqstar hqq hs hsum i)
  constructor
  · simp only [finiteRowShift, Finset.mul_sum, ← mul_assoc,
      finiteRow_left_support q s hqstar hqq hs hsum]
  · simp only [finiteRowShift, Finset.sum_mul, mul_assoc, hstar]

lemma finiteRowShiftIterate_right_support (q : E) (s : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q) (x : E) (hx : x * q = x) (n : ℕ) :
    finiteRowShiftIterate s n x * q = finiteRowShiftIterate s n x := by
  cases n with
  | zero => exact hx
  | succ n => exact (finiteRowShift_support q s hqstar hqq hs hsum _).2

lemma finiteRowShift_mul_row (q : E) (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (x : E) (hx : x * q = x) (i : I) :
    finiteRowShift s x * s i = s i * x := by
  rw [finiteRowShift, Finset.sum_mul]
  have hterm (j : I) : (s j * x * star (s j)) * s i =
      if j = i then s i * x else 0 := by
    rw [mul_assoc, hs]
    split_ifs with h
    · subst j
      rw [mul_assoc, hx]
    · exact mul_zero _
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRowShiftIterate_mul_jointWord (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q) (x : E) (hx : x * q = x)
    (n : ℕ) (w : Fin (n + 1) → I) :
    finiteRowShiftIterate s n x * finiteJointWord s t n w =
      finiteJointWord s (fun i => x * t i) n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change finiteRowShift s (finiteRowShiftIterate s n x) *
        (s (w 0) * finiteJointWord s t n (Fin.tail w)) =
          s (w 0) * finiteJointWord s (fun i => x * t i) n (Fin.tail w)
      rw [← mul_assoc, finiteRowShift_mul_row q s hs _
        (finiteRowShiftIterate_right_support q s hqstar hqq hs hsum x hx n),
        mul_assoc, ih]

lemma finiteRowCocycle_support (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q) :
    q * finiteRowCocycle s t = finiteRowCocycle s t ∧
      finiteRowCocycle s t * q = finiteRowCocycle s t := by
  have hstar (i : I) : star (s i) * q = star (s i) := by
    simpa only [star_mul, hqstar] using
      congrArg star (finiteRow_left_support q s hqstar hqq hs hsum i)
  constructor
  · simp only [finiteRowCocycle, Finset.mul_sum, ← mul_assoc,
      finiteRow_left_support q t hqstar hqq ht htsum]
  · simp only [finiteRowCocycle, Finset.sum_mul, mul_assoc, hstar]

lemma finiteRowShiftIterate_cocycle_star_mul_jointWord (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (n : ℕ) (w : Fin (n + 1) → I) :
    finiteRowShiftIterate s n (star (finiteRowCocycle s t)) * finiteJointWord s t n w =
      finiteJointWord s s n w := by
  have hx : star (finiteRowCocycle s t) * q = star (finiteRowCocycle s t) := by
    rw [finiteRowCocycle_star]
    exact (finiteRowCocycle_support q t s hqstar hqq ht hs htsum hsum).2
  rw [finiteRowShiftIterate_mul_jointWord q s t hqstar hqq hs hsum _ hx]
  have he : (fun i => star (finiteRowCocycle s t) * t i) = s := by
    funext i
    rw [finiteRowCocycle_star, finiteRowCocycle_mul_row q t s hqstar hqq ht hs]
  rw [he]

omit [Fintype I] [DecidableEq I] in
lemma finiteJointWord_move_target (s t : I → E)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ)
    (w : Fin (n + 1) → I) (i : I) :
    t i * finiteJointWord s s n w =
      finiteJointWord s t (n + 1) (Fin.snoc w i) := by
  induction n with
  | zero =>
      have hw : w = Fin.cons (w 0) (fun i : Fin 0 => i.elim0) := by
        ext j
        fin_cases j
        rfl
      rw [hw, ← Fin.cons_snoc_eq_snoc_cons]
      change t i * s (w 0) = s (w 0) * t i
      exact (hc (w 0) i).eq.symm
  | succ n ih =>
      conv_rhs => rw [← Fin.cons_self_tail w, ← Fin.cons_snoc_eq_snoc_cons]
      simp only [finiteJointWord, Fin.cons_zero, Fin.tail_cons]
      rw [← mul_assoc, (hc (w 0) i).eq.symm, mul_assoc, ih]
      rfl

lemma finiteRowCocycle_mul_sourceWord (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ) (w : Fin (n + 1) → I) :
    finiteRowCocycle s t * finiteJointWord s s n w =
      finiteJointWord s t n (Fin.snoc (Fin.tail w) (w 0)) := by
  cases n with
  | zero =>
      simpa only [finiteJointWord, show (0 : Fin 1) = Fin.last 0 from rfl,
        Fin.snoc_last] using finiteRowCocycle_mul_row q s t hqstar hqq hs ht (w 0)
  | succ n =>
      change finiteRowCocycle s t *
        (s (w 0) * finiteJointWord s s n (Fin.tail w)) = _
      rw [← mul_assoc, finiteRowCocycle_mul_row q s t hqstar hqq hs ht]
      exact finiteJointWord_move_target s t hc n (Fin.tail w) (w 0)

omit [Fintype I] [DecidableEq I] in
lemma finiteCoordinateCycle_eq_snoc (n : ℕ) (w : Fin (n + 1) → I) :
    finiteCoordinateCycle (n + 1) w = Fin.snoc (Fin.tail w) (w 0) := by
  change (fun i : Fin (n + 1) => w (i + 1)) = Fin.snoc (Fin.tail w) (w 0)
  funext i
  change w (i + 1) = (Fin.snoc (Fin.tail w) (w 0) : Fin (n + 1) → I) i
  cases i using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      congr 1
      by_cases hn : n = 0
      · subst n
        rfl
      · apply Fin.ext
        change (n + 1 % (n + 1)) % (n + 1) = 0
        rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
        exact Nat.mod_self _
  | cast i =>
      rw [Fin.snoc_castSucc]
      change w (i.castSucc + 1) = w i.succ
      congr 1
      have hi : i.val < n := i.isLt
      apply Fin.ext
      change (i.val + 1 % (n + 1)) % (n + 1) = i.val + 1
      rw [Nat.mod_eq_of_lt (by omega : 1 < n + 1)]
      exact Nat.mod_eq_of_lt (by omega)

/-- This is the degree-zero cycle coboundary, with its shifted adjoint tail. -/
def finiteJointCycleCoboundary (s t : I → E) (n : ℕ) : E :=
  finiteRowCocycle s t * finiteRowShiftIterate s n (star (finiteRowCocycle s t))

lemma finiteJointCycleCoboundary_mul_row (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ) (w : Fin (n + 1) → I) :
    finiteJointCycleCoboundary s t n * finiteJointWord s t n w =
      finiteJointWord s t n (finiteCoordinateCycle (n + 1) w) := by
  rw [finiteJointCycleCoboundary, mul_assoc,
    finiteRowShiftIterate_cocycle_star_mul_jointWord q s t hqstar hqq hs ht hsum htsum,
    finiteRowCocycle_mul_sourceWord q s t hqstar hqq hs ht hc,
    finiteCoordinateCycle_eq_snoc]

omit [DecidableEq I] in
lemma finiteRow_eq_of_mul_row_eq (q : E) (r : I → E)
    (hsum : (∑ i, r i * star (r i)) = q) (x y : E)
    (hx : x * q = x) (hy : y * q = y) (h : ∀ i, x * r i = y * r i) : x = y := by
  calc
    x = x * q := hx.symm
    _ = ∑ i, (x * r i) * star (r i) := by rw [← hsum]; simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i, (y * r i) * star (r i) := by simp only [h]
    _ = y * q := by rw [← hsum]; simp only [Finset.mul_sum, mul_assoc]
    _ = y := hy

lemma finiteJointCycleCoboundary_eq_permutation (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ) :
    finiteJointCycleCoboundary s t n =
      finiteRowPermutation (finiteJointWord s t n) (finiteCoordinateCycle (n + 1)) := by
  have hx : star (finiteRowCocycle s t) * q = star (finiteRowCocycle s t) := by
    rw [finiteRowCocycle_star]
    exact (finiteRowCocycle_support q t s hqstar hqq ht hs htsum hsum).2
  apply finiteRow_eq_of_mul_row_eq q (finiteJointWord s t n)
    (finiteJointWord_sum q s t hqstar hqq hs hsum htsum n)
  · rw [finiteJointCycleCoboundary, mul_assoc,
      finiteRowShiftIterate_right_support q s hqstar hqq hs hsum _ hx]
  · exact (finiteRowPermutation_support q _ hqstar hqq
      (finiteJointWord_gram q s t hqstar hqq hs ht hsum htsum n)
      (finiteJointWord_sum q s t hqstar hqq hs hsum htsum n) _).2
  · intro w
    rw [finiteJointCycleCoboundary_mul_row q s t hqstar hqq hs ht hsum htsum hc]
    exact (finiteRowPermutation_mul_row q (finiteJointWord s t n) hqstar hqq
      (finiteJointWord_gram q s t hqstar hqq hs ht hsum htsum n)
      (show Equiv.Perm (Fin (n + 1) → I) from finiteCoordinateCycle (n + 1)) w).symm

/-- The concrete coboundary has a path of speed at most `4π`, uniformly in
the iterate. This does not assert such a bound for products of `W`. -/
lemma exists_controlled_jointCycleCoboundary_path [Nontrivial E]
    (q : E) (s t : I → E) (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (hc : ∀ i j, Commute (s i) (t j)) (n : ℕ) :
    ∃ u : unitary E, (u : E) = finiteJointCycleCoboundary s t n + (1 - q) ∧
      ∃ p : Path (1 : unitary E) u,
        ∀ a b, ‖(p a : E) - p b‖ ≤ (4 * Real.pi) * |(a : ℝ) - b| := by
  obtain ⟨p, hp⟩ := exists_controlled_jointWordCycle_path q s t hqstar hqq hs ht hsum htsum n
  refine ⟨_, ?_, p, hp⟩
  change finiteRowPermutation (finiteJointWord s t n) (finiteCoordinateCycle (n + 1)) +
    (1 - q) = finiteJointCycleCoboundary s t n + (1 - q)
  rw [finiteJointCycleCoboundary_eq_permutation q s t hqstar hqq hs ht hsum htsum hc]

end WeakPureInfiniteness

end

end OAI
