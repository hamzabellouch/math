import OAI.Analysis.OInfinity.CocycleGluing

namespace OAI

/-! # Actual cocycle commutators with periodic source towers

The same source shift occurs in the cocycle and in the tower estimate.
For elements fixed by the target row, the cocycle commutator equals the
source-periodicity defect. In particular an N-cycle with step error η
has cocycle commutator at most Nη. No centrality on source isometries is
assumed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

section Group
variable {G : Type*} [Group G]

lemma finiteGroupCocycle_inv (α β : G →* G) (w : G)
    (hβ : ∀ x, β x = w * α x * w⁻¹) (n : ℕ) :
    (finiteGroupCocycle α w n)⁻¹ = finiteGroupCocycle β w⁻¹ n := by
  induction n with
  | zero => simp [finiteGroupCocycle]
  | succ n ih =>
      change (w * α (finiteGroupCocycle α w n))⁻¹ =
        w⁻¹ * β (finiteGroupCocycle β w⁻¹ n)
      rw [mul_inv_rev, ← map_inv, ih, hβ]
      group

end Group

variable {E : Type*} [CStarAlgebra E]

lemma finiteRowShift_mul (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (x y : E) :
    finiteRowShift s (x * y) = finiteRowShift s x * finiteRowShift s y :=
  map_mul (finiteCuntzDiagonalHom s hs) x y

lemma finiteRowShift_fixed_of_commutes (t : Fin 2 → E)
    (htsum : (∑ i, t i * star (t i)) = 1) (x : E)
    (hc : ∀ i, Commute (t i) x) : finiteRowShift t x = x := by
  have he (i : Fin 2) : t i * x * star (t i) = x * (t i * star (t i)) := by
    rw [(hc i).eq, mul_assoc]
  simp only [finiteRowShift, he, ← Finset.mul_sum, htsum, mul_one]

lemma finiteRowShiftIterate_fixed_of_commutes (t : Fin 2 → E)
    (htsum : (∑ i, t i * star (t i)) = 1) (x : E)
    (hc : ∀ i, Commute (t i) x) (n : ℕ) : finiteRowShiftIterate t n x = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finiteRowShiftIterate, ih, finiteRowShift_fixed_of_commutes t htsum x hc]

lemma binaryRowCocycle_coe_succ (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) :
    (binaryRowCocycleUnitary s t hs ht hsum htsum (n + 1) : E) =
      finiteRowCocycle s t * finiteRowShift s
        (binaryRowCocycleUnitary s t hs ht hsum htsum n) := by
  change finiteRowCocycle s t *
    (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
      (by simpa using hs 1 1) (by simpa using hs 0 1)
      (binaryRowCocycleUnitary s t hs ht hsum htsum n) : E) = _
  rw [binarySplitHom_coe s hs hsum]

lemma finiteRowCocycle_shift_intertwining (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (x : E) :
    finiteRowCocycle s t * finiteRowShift s x =
      finiteRowShift t x * finiteRowCocycle s t := by
  have hw : star (finiteRowCocycle s t) * finiteRowCocycle s t = 1 :=
    (finiteRowCocycle_gram 1 s t (by simp) (by simp) hs ht hsum htsum).1
  calc
    _ = (finiteRowCocycle s t * finiteRowShift s x * star (finiteRowCocycle s t)) *
        finiteRowCocycle s t := by rw [mul_assoc, hw, mul_one]
    _ = _ := by rw [finiteRowCocycle_conjugate_shift s t hs ht]

/-- Intertwining holds on every element, not just on generators. -/
lemma binaryRowCocycle_iterate_intertwining (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) (x : E) :
    (binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * finiteRowShiftIterate s n x =
      finiteRowShiftIterate t n x * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E) := by
  induction n with
  | zero => change 1 * x = x * 1; rw [one_mul, mul_one]
  | succ n ih =>
      rw [binaryRowCocycle_coe_succ, finiteRowShiftIterate, finiteRowShiftIterate]
      calc
        _ = finiteRowCocycle s t * finiteRowShift s
            ((binaryRowCocycleUnitary s t hs ht hsum htsum n : E) *
              finiteRowShiftIterate s n x) := by rw [finiteRowShift_mul s hs, mul_assoc]
        _ = finiteRowCocycle s t * finiteRowShift s
            (finiteRowShiftIterate t n x *
              (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)) := by rw [ih]
        _ = (finiteRowCocycle s t * finiteRowShift s (finiteRowShiftIterate t n x)) *
            finiteRowShift s (binaryRowCocycleUnitary s t hs ht hsum htsum n) := by
          rw [finiteRowShift_mul s hs, mul_assoc]
        _ = _ := by
          rw [finiteRowCocycle_shift_intertwining s t hs ht hsum htsum]
          simp only [mul_assoc]

/-- Reversing the rows gives exactly the adjoint product cocycle. -/
lemma binaryRowCocycle_star (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) :
    star (binaryRowCocycleUnitary s t hs ht hsum htsum n) =
      binaryRowCocycleUnitary t s ht hs htsum hsum n := by
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let β := binarySplitHom (t 0) (t 1) (by simpa using ht 0 0)
    (by simpa using ht 1 1) (by simpa using ht 0 1)
  let w := binaryRowUnitary s t hs ht hsum htsum
  have hw : w⁻¹ = binaryRowUnitary t s ht hs htsum hsum := by
    apply Subtype.ext
    exact finiteRowCocycle_star s t
  have h := finiteGroupCocycle_inv α β w
    (binarySplitHom_conjugacy s t hs ht hsum htsum) n
  rw [hw] at h
  exact h

lemma binaryRowCocycle_commutator_norm (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1) (n : ℕ) (x : E)
    (hxt : ∀ i, Commute (t i) x) :
    ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) * x -
        x * (binaryRowCocycleUnitary s t hs ht hsum htsum n : E)‖ =
      ‖x - finiteRowShiftIterate s n x‖ := by
  have hi := binaryRowCocycle_iterate_intertwining s t hs ht hsum htsum n x
  rw [finiteRowShiftIterate_fixed_of_commutes t htsum x hxt n] at hi
  calc
    _ = ‖(binaryRowCocycleUnitary s t hs ht hsum htsum n : E) *
        (x - finiteRowShiftIterate s n x)‖ := by rw [mul_sub, hi]
    _ = _ := CStarRing.norm_coe_unitary_mul _ _

lemma finiteRowShiftIterate_cycle_error (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (x : ℕ → E) (N : ℕ) (η : ℝ)
    (hstep : ∀ k < N, ‖finiteRowShift s (x k) - x (k + 1)‖ ≤ η) :
    ∀ n ≤ N, ‖finiteRowShiftIterate s n (x 0) - x n‖ ≤ (n : ℝ) * η := by
  intro n
  induction n with
  | zero => intro _; simp [finiteRowShiftIterate]
  | succ n ih =>
      intro hn
      have hnN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hprev := ih (Nat.le_of_lt hnN)
      rw [finiteRowShiftIterate]
      calc
        _ ≤ ‖finiteRowShift s (finiteRowShiftIterate s n (x 0)) - finiteRowShift s (x n)‖ +
            ‖finiteRowShift s (x n) - x (n + 1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖finiteRowShiftIterate s n (x 0) - x n‖ + η :=
          add_le_add (finiteCuntzTransfer_sub_norm_le s s hs hs _ _) (hstep n hnN)
        _ ≤ (n : ℝ) * η + η := add_le_add hprev le_rfl
        _ = _ := by push_cast; ring

/-- A periodic source tower gives the actual cocycle commutator estimate. -/
lemma binaryRowCocycle_periodic_commutator_le (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (x : ℕ → E) (N : ℕ) (η : ℝ) (hperiod : x N = x 0)
    (hstep : ∀ k < N, ‖finiteRowShift s (x k) - x (k + 1)‖ ≤ η)
    (hxt : ∀ i, Commute (t i) (x 0)) :
    ‖(binaryRowCocycleUnitary s t hs ht hsum htsum N : E) * x 0 -
        x 0 * (binaryRowCocycleUnitary s t hs ht hsum htsum N : E)‖ ≤ (N : ℝ) * η := by
  rw [binaryRowCocycle_commutator_norm s t hs ht hsum htsum N (x 0) hxt, norm_sub_rev]
  simpa only [hperiod] using finiteRowShiftIterate_cycle_error s hs x N η hstep N le_rfl

/-- Actual finite coefficients with uniform mesh error for the binary row
cocycle. The endpoint equality is exact. -/
lemma exists_binaryCocycleGrid [Nontrivial E] (s t : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (htsum : (∑ i, t i * star (t i)) = 1)
    (hc : ∀ i j, Commute (s i) (t j)) (N : ℕ) (hN : 0 < N) :
    ∃ v : Fin (N + 1) → unitary E,
      v 0 = v (Fin.last N) ∧
      ∀ k : Fin N, ‖finiteRowCocycle s t * finiteRowShift s (v k.castSucc) -
        (v k.succ : E)‖ ≤ (192 * Real.pi) / N := by
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let w := binaryRowUnitary s t hs ht hsum htsum
  obtain ⟨p, hp⟩ := exists_uniform_binaryRowCocycle_path s t hs ht hsum htsum hc N
  let v : Fin (N + 1) → unitary E := fun k =>
    finiteCocycleCoefficient α w p k (cocycleGridTime N hN k)
  refine ⟨v, finiteCocycleCoefficient_grid_seam α w N hN p, ?_⟩
  intro k
  have h := finiteCocycleCoefficient_grid_step α w
    (binarySplitHom_sub_norm_le s hs hsum) N hN p (192 * Real.pi) hp k
  change ‖finiteRowCocycle s t * (α (v k.castSucc) : E) - (v k.succ : E)‖ ≤ _ at h
  rwa [binarySplitHom_coe s hs hsum] at h

end WeakPureInfiniteness

end

end OAI
