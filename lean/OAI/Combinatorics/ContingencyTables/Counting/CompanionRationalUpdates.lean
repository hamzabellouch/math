import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseComposition
import OAI.Combinatorics.ContingencyTables.Counting.CompanionWeightOracle

namespace OAI

/-! # Exact rational multiplier updates of the outer annealing run -/

namespace ContingencyTables.CompanionRationalUpdates

open CompanionFactorialApplication CompanionPhaseComposition CompanionMultiplierUpdate
open CommonBasesFPRAS TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

abbrev Pair (A : Instance I J) := (Labels A×Bool)×(Labels A×Bool)

def initial (A : Instance I J) (p q : Pair A) : ℚ :=
  if (p.1.1).1=(q.1.1).1 then 6
  else 6*((A.b (p.1.1).1.val.1 (p.1.1).1.val.2:ℚ)+1)/
    ((A.b (q.1.1).1.val.1 (q.1.1).1.val.2:ℚ)+2)

lemma initial_positive (A : Instance I J) (p q : Pair A) : 0 < initial A p q := by
  unfold initial
  split_ifs <;> positivity

lemma initial_cast (A : Instance I J) (p q : Pair A) :
    (initial A p q:ℝ)=CompanionInitialMultipliers.multiplier A p q := by
  simp only [initial,CompanionInitialMultipliers.multiplier,InitialMultiplierValues.value]
  split_ifs <;> simp only [Rat.cast_ofNat,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]

/-- The initializer has a uniform binary bound using only the polynomial
small-cell scale, including values at pair arguments outside defect types. -/
lemma initial_binary_bound (A : Instance I J) (p q : Pair A) :
    RatBound (initial A p q) (2^(A.W+4)) := by
  have hp := A.hsmall (p.1.1).1.val.1 (p.1.1).1.val.2 (p.1.1).1.property
  have hq := A.hsmall (q.1.1).1.val.1 (q.1.1).1.val.2 (q.1.1).1.property
  have hW : A.W ≤ 2^A.W := A.W.lt_two_pow_self.le
  have hpow : 0 < 2^A.W := by positivity
  have hnum : 6*(A.b (p.1.1).1.val.1 (p.1.1).1.val.2+1) ≤ 2^(A.W+4) := by
    rw [pow_add]
    norm_num
    omega
  have hden : A.b (q.1.1).1.val.1 (q.1.1).1.val.2+2 ≤ 2^(A.W+4) := by
    rw [pow_add]
    norm_num
    omega
  unfold initial
  split_ifs
  · apply RatBound.nat 6 _ _ (by positivity)
    rw [pow_add]
    norm_num
    omega
  · have hh := RatBound.nat_div _ _ _ hnum hden (by positivity)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hh

def plainCount (A : Instance I J) (l : List (Set (Labels A×Bool))) : ℕ :=
  l.countP (fun S => decide (PlainState pairs S))

def defectCount (A : Instance I J) (l : List (Set (Labels A×Bool))) (p q : Pair A) : ℕ :=
  l.countP (fun S => decide (DefectState pairs p q S))

lemma plainCount_le (A : Instance I J) (l : List (Set (Labels A×Bool))) :
    plainCount A l ≤ l.length := List.countP_le_length

lemma defectCount_le (A : Instance I J) (l : List (Set (Labels A×Bool))) (p q : Pair A) :
    defectCount A l p q ≤ l.length := List.countP_le_length

lemma rationalLearn_counts (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (l : List (Set (Labels A×Bool))) (hl : 0 < l.length) (p q : Pair A) :
    rationalLearn pairs w l p q=
      if p∈pairs ∧ q∈pairs ∧ p≠q then w p q*(plainCount A l:ℚ)/(defectCount A l p q:ℚ)
      else w p q := by
  have hN : (l.length:ℚ)≠0 := by exact_mod_cast hl.ne'
  unfold rationalLearn rationalEmpirical rationalPlain rationalDefect plainCount defectCount
  simp only [indicator_list_sum]
  split_ifs <;> simp only [div_div_div_cancel_right₀ hN,mul_div_assoc]

/-- Every decision to divide is preceded by the literal positive-count
check used in the source algorithm. -/
def CountsPositive (A : Instance I J) (l : List (Set (Labels A×Bool))) : Prop :=
  0 < plainCount A l ∧ ∀ p∈pairs,∀ q∈pairs,p≠q → 0 < defectCount A l p q

def checkedUpdate (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (l : List (Set (Labels A×Bool))) : Option (Pair A → Pair A → ℚ) :=
  if CountsPositive A l then some (rationalLearn pairs w l) else none

lemma checkedUpdate_positive (A : Instance I J) (w : Pair A → Pair A → ℚ)
    (hw : ∀ p q,0 < w p q) (l : List (Set (Labels A×Bool)))
    (w' : Pair A → Pair A → ℚ) (hu : checkedUpdate A w l=some w') :
    ∀ p q,0 < w' p q := by
  unfold checkedUpdate at hu
  split_ifs at hu with hc
  · cases Option.some.inj hu
    have hl : 0 < l.length := lt_of_lt_of_le hc.1 (plainCount_le A l)
    intro p q
    rw [rationalLearn_counts A w l hl]
    split_ifs with hpq
    · exact div_pos (mul_pos (hw p q) (by exact_mod_cast hc.1))
        (by exact_mod_cast hc.2 p hpq.1 q hpq.2.1 hpq.2.2)
    · exact hw p q

/-- The literal rational history is exactly the real
history, including all unsuccessful histories. -/
def history (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool))) :
    ℕ → Pair A → Pair A → ℚ
  | 0 => initial A
  | j+1 => rationalLearn pairs (history A samples j) (samples j)

lemma history_cast (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (j : ℕ) (p q : Pair A) :
    (history A samples j p q:ℝ)=weights A samples j p q := by
  induction j generalizing p q with
  | zero => exact initial_cast A p q
  | succ j ih =>
    change (rationalLearn pairs (history A samples j) (samples j) p q:ℝ)=_
    rw [rationalLearn_cast]
    have he : (fun p q => (history A samples j p q:ℝ))=weights A samples j := by
      funext p q
      exact ih p q
    rw [he]
    rfl

theorem history_good (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1/4) (j : ℕ)
    (hall : ∀ a<j, Accurate A samples eta a) :
    GoodMultipliers pairs (CompanionAnnealing.weight A j)
      (fun p q => (history A samples j p q:ℝ)) := by
  have he : (fun p q => (history A samples j p q:ℝ))=weights A samples j := by
    funext p q
    exact history_cast A samples j p q
  rw [he]
  exact weights_good A samples eta he0 he1 j hall

lemma history_positive (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (eta : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1/4) (j : ℕ)
    (hall : ∀ a<j, Accurate A samples eta a) (p q : Pair A) :
    0 < history A samples j p q := by
  have hh := (history_good A samples eta he0 he1 j hall).positive p q
  exact_mod_cast hh

/-- Every bounded observation history has polynomial-length rational
multipliers, without a success or positivity assumption on that history. -/
theorem history_binary_bound (A : Instance I J) (samples : ℕ → List (Set (Labels A×Bool)))
    (N j : ℕ) (hlen : ∀ a<j,(samples a).length ≤ N) (p q : Pair A) :
    RatBound (history A samples j p q) (2^(A.W+4+j*N)) := by
  induction j generalizing p q with
  | zero => simpa only [history,Nat.zero_mul,Nat.add_zero] using initial_binary_bound A p q
  | succ j ih =>
    have hh := rationalLearn_bound pairs (history A samples j) (samples j)
      (2^(A.W+4+j*N)) (2^N) (by positivity)
      ((hlen j (by omega)).trans N.lt_two_pow_self.le)
      (fun p q => ih (by intro a ha; exact hlen a (by omega)) p q) p q
    simpa only [history,←pow_add,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hh

end

end ContingencyTables.CompanionRationalUpdates

end OAI
