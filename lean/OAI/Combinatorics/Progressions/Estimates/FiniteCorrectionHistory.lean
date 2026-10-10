import Mathlib.Data.Finset.Sigma
import OAI.Combinatorics.Progressions.Linear.FiniteRankTriangularFinset

namespace OAI

section

universe u v

namespace Erdos3

open scoped BigOperators

def CorrectionHistory {State : Type v} (I : State → Type u)
    (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State) : ℕ → State → Type u
  | 0, _ => PUnit
  | n + 1, state =>
      Σ sr : (I state → ℝ) × (I state → ℚ), CorrectionHistory I next n (next state sr)

def CorrectionHistoryValid {State : Type v} (I : State → Type u)
    (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State)
    (valid : ∀ state, ((I state → ℝ) × (I state → ℚ)) → Prop) :
    ∀ n state, CorrectionHistory I next n state → Prop
  | 0, _, _ => True
  | n + 1, state, h =>
      valid state h.1 ∧ CorrectionHistoryValid I next valid n (next state h.1) h.2

private theorem exists_correction_history_finset
    {State : Type v} (I : State → Type u)
    (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State)
    (valid : ∀ state, ((I state → ℝ) × (I state → ℚ)) → Prop)
    {K : ℝ} (hK : 0 ≤ K)
    (hnode : ∀ state, ∃ S : Finset ((I state → ℝ) × (I state → ℚ)),
      (S.card : ℝ) ≤ K ∧ ∀ sr, sr ∈ S ↔ valid state sr) :
    ∀ n state, ∃ S : Finset (CorrectionHistory I next n state),
      (S.card : ℝ) ≤ K ^ n ∧ ∀ h, h ∈ S ↔ CorrectionHistoryValid I next valid n state h := by
  classical
  intro n
  induction n with
  | zero =>
    intro state
    dsimp only [CorrectionHistory, CorrectionHistoryValid]
    refine ⟨{PUnit.unit}, by simp, ?_⟩
    intro h
    cases h
    exact ⟨fun _ => trivial, fun _ => Finset.mem_singleton_self _⟩
  | succ n ih =>
    intro state
    obtain ⟨S, hS, hvalid⟩ := hnode state
    choose tails htailCard htailValid using fun sr => ih (next state sr)
    refine ⟨S.sigma tails, ?_, ?_⟩
    · change ((S.sigma tails).card : ℝ) ≤ K ^ (n + 1)
      rw [Finset.card_sigma, Nat.cast_sum]
      calc
        _ ≤ ∑ _sr ∈ S, K ^ n := Finset.sum_le_sum (fun sr _ => htailCard sr)
        _ = (S.card : ℝ) * K ^ n := by simp
        _ ≤ K * K ^ n := mul_le_mul_of_nonneg_right hS (pow_nonneg hK n)
        _ = K ^ (n + 1) := by rw [pow_succ]; ring
    · intro h
      rcases h with ⟨sr, tail⟩
      change (⟨sr, tail⟩ : Sigma _) ∈ S.sigma tails ↔
        valid state sr ∧ CorrectionHistoryValid I next valid n (next state sr) tail
      rw [Finset.mem_sigma, hvalid, htailValid]

def TriangularCorrectionHistoryValid {State : Type v} (I : State → Type u)
    [∀ state, Fintype (I state)]
    (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State)
    (q : State → ℕ) (B : State → ℝ)
    (A : ∀ state, Matrix (I state) (I state) ℝ) (c : ∀ state, I state → ℝ) :=
  CorrectionHistoryValid I next
    (fun state sr => sr ∈ finiteRankCorrectionSolutions (A state) (c state) (B state) (q state))

theorem exists_finite_triangular_correction_histories
    {State : Type v} (I : State → Type u) [∀ state, Fintype (I state)]
    (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State)
    (q : State → ℕ) (hq : ∀ state, 0 < q state)
    (B : State → ℝ) (hB : ∀ state, 0 ≤ B state)
    (rank : ∀ state, I state → ℕ)
    (A : ∀ state, Matrix (I state) (I state) ℝ) (c : ∀ state, I state → ℝ)
    (htri : ∀ state i j, rank state j ≤ rank state i → j ≠ i → A state i j = 0)
    (hdiag : ∀ state i, A state i i ≠ 0)
    (hdiagBound : ∀ state i, |A state i i| ≤ 1)
    (K : ℕ)
    (hcount : ∀ state,
      (2 * ⌈(q state : ℝ) * B state⌉₊ + 3) ^ Fintype.card (I state) ≤ K)
    (n : ℕ) (initial : State) :
    ∃ S : Finset (CorrectionHistory I next n initial), S.card ≤ K ^ n ∧
      ∀ h, h ∈ S ↔ TriangularCorrectionHistoryValid I next q B A c n initial h := by
  have hnode (state : State) : ∃ S : Finset ((I state → ℝ) × (I state → ℚ)),
      (S.card : ℝ) ≤ K ∧ ∀ sr,
        sr ∈ S ↔ sr ∈ finiteRankCorrectionSolutions (A state) (c state) (B state) (q state) := by
    obtain ⟨S, hS, hmem⟩ := exists_finite_rank_triangular_correction_finset
      (q state) (hq state) (B state) (hB state) (rank state) (A state) (c state)
      (htri state) (hdiag state) (hdiagBound state)
    exact ⟨S, Nat.cast_le.mpr (hS.trans (hcount state)), hmem⟩
  obtain ⟨S, hS, hmem⟩ := exists_correction_history_finset I next _
    (Nat.cast_nonneg K) hnode n initial
  refine ⟨S, ?_, hmem⟩
  exact_mod_cast hS

theorem exists_finite_triangular_correction_histories_exp
    {State : Type v} (I : State → Type u) [∀ state, Fintype (I state)]
    (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State)
    (q : State → ℕ) (hq : ∀ state, 0 < q state)
    (B : State → ℝ) (hB : ∀ state, 0 ≤ B state)
    {p : ℝ} (hp : 0 ≤ p) (hI : ∀ state, (Fintype.card (I state) : ℝ) ≤ p)
    (hqCap : ∀ state, (q state : ℝ) ≤ Real.exp p)
    (hBCap : ∀ state, B state ≤ Real.exp p)
    (rank : ∀ state, I state → ℕ)
    (A : ∀ state, Matrix (I state) (I state) ℝ) (c : ∀ state, I state → ℝ)
    (htri : ∀ state i j, rank state j ≤ rank state i → j ≠ i → A state i j = 0)
    (hdiag : ∀ state i, A state i i ≠ 0)
    (hdiagBound : ∀ state i, |A state i i| ≤ 1)
    (n : ℕ) (initial : State) :
    ∃ S : Finset (CorrectionHistory I next n initial),
      (S.card : ℝ) ≤ Real.exp ((n : ℝ) * (p + 3) ^ 3) ∧
      ∀ h, h ∈ S ↔ TriangularCorrectionHistoryValid I next q B A c n initial h := by
  have hnode (state : State) := exists_finite_rank_triangular_correction_finset_exp
    (q state) (hq state) hp (hB state) (hI state) (hqCap state) (hBCap state)
    (rank state) (A state) (c state) (htri state) (hdiag state) (hdiagBound state)
  obtain ⟨S, hS, hmem⟩ := exists_correction_history_finset I next _
    (Real.exp_nonneg ((p + 3) ^ 3)) hnode n initial
  exact ⟨S, by simpa only [← Real.exp_nat_mul] using hS, hmem⟩

theorem exists_uniform_finite_triangular_correction_histories (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {State : Type v} (I : State → Type u) [∀ state, Fintype (I state)]
      (next : ∀ state, ((I state → ℝ) × (I state → ℚ)) → State)
      (q : State → ℕ), (∀ state, 0 < q state) →
      ∀ (B : State → ℝ), (∀ state, 0 ≤ B state) →
      ∀ p : ℝ, 0 ≤ p → (∀ state, (Fintype.card (I state) : ℝ) ≤ p) →
      (∀ state, (q state : ℝ) ≤ Real.exp ((p + a) ^ a)) →
      (∀ state, B state ≤ Real.exp ((p + a) ^ a)) →
      ∀ (rank : ∀ state, I state → ℕ)
        (A : ∀ state, Matrix (I state) (I state) ℝ) (c : ∀ state, I state → ℝ),
      (∀ state i j, rank state j ≤ rank state i → j ≠ i → A state i j = 0) →
      (∀ state i, A state i i ≠ 0) → (∀ state i, |A state i i| ≤ 1) →
      ∀ n : ℕ, (n : ℝ) ≤ p → ∀ initial : State,
      ∃ S : Finset (CorrectionHistory I next n initial),
        (S.card : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ h, h ∈ S ↔ TriangularCorrectionHistoryValid I next q B A c n initial h := by
  let R : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (R * (R + (R + Polynomial.C a) ^ a + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro State I _ next q hq B hB p hp hI hqCap hBCap rank A c htri hdiag hdiagBound n hn initial
  let p' := p + (p + a) ^ a
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hpp : p ≤ p' := le_add_of_nonneg_right (by positivity)
  have hap : (p + a) ^ a ≤ p' := le_add_of_nonneg_left hp
  obtain ⟨S, hS, hmem⟩ := exists_finite_triangular_correction_histories_exp
    I next q hq B hB hp' (fun state => (hI state).trans hpp)
    (fun state => (hqCap state).trans (Real.exp_le_exp.mpr hap))
    (fun state => (hBCap state).trans (Real.exp_le_exp.mpr hap))
    rank A c htri hdiag hdiagBound n initial
  refine ⟨S, hS.trans (Real.exp_le_exp.mpr ?_), hmem⟩
  calc
    (n : ℝ) * (p' + 3) ^ 3 ≤ p * (p' + 3) ^ 3 :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ ≤ (p + C) ^ C := by
      simpa [R, p', Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
