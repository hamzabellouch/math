import OAI.Combinatorics.ContingencyTables.Counting.CompanionRationalUpdates

namespace OAI

/-! # Explicit fresh words and rational arithmetic for one outer phase -/

namespace ContingencyTables.CompanionPhaseWords

open CompanionFactorialApplication CompanionOracleDensity CompanionWeightOracle CompanionRationalUpdates
open CommonBasesFPRAS GridBoundary FirstSuccess FairBits TwoLiftStates
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Separate current-parameter and next-parameter oracle words are
reserved at every observed state, including states at which they are unused. -/
def observationBits (A : Instance I J) (C K j : ℕ) (xi : ℚ) : ℕ :=
  medianEstimatorBits A C K j xi xi+medianEstimatorBits A C K (j+1) xi xi

def phaseBits (A : Instance I J) (C K j N : ℕ) (xi : ℚ) : ℕ :=
  N*observationBits A C K j xi

def phaseWordEquiv (A : Instance I J) (C K j N : ℕ) (xi : ℚ) :
    (Fin (phaseBits A C K j N xi) → Bool) ≃
      (Fin N → WeightWord A C K j xi × WeightWord A C K (j+1) xi) :=
  (oracleWalkWordEquiv N (observationBits A C K j xi)).trans
    (Equiv.piCongrRight (fun _ => splitWordEquiv _ _))

def observedTerm (A : Instance I J) (C K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi) : ℚ :=
  if PlainState pairs S then
    evaluate A C K hK hW (j+1) xi v S bits.2/evaluate A C K hK hW j xi v S bits.1
  else 0

def observedRatio (A : Instance I J) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : ℚ :=
  (∑ i,observedTerm A C K j hK hW xi v (states i) (phaseWordEquiv A C K j N xi bits i))/
    plainCount A (List.ofFn states)

lemma observedTerm_nonneg (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (S : Set (Labels A×Bool))
    (bits : WeightWord A C K j xi × WeightWord A C K (j+1) xi) :
    0 ≤ observedTerm A C K j hK hW xi v S bits := by
  unfold observedTerm
  split_ifs
  · exact (div_pos (evaluate_positive A C hC K hK hW hB (j+1) hj xi hx0 hx1 v S bits.2)
      (evaluate_positive A C hC K hK hW hB j (by omega) xi hx0 hx1 v S bits.1)).le
  · rfl

lemma observedRatio_positive (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (states : Fin N → Set (Labels A×Bool))
    (hc : 0 < plainCount A (List.ofFn states))
    (bits : Fin (phaseBits A C K j N xi) → Bool) :
    0 < observedRatio A C K j N hK hW xi v states bits := by
  obtain ⟨S,hS,hplain⟩ := List.countP_pos_iff.mp hc
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hS
  have hpi : PlainState pairs (states i) := by
    rw [hi]
    exact of_decide_eq_true hplain
  have hterm : 0 < observedTerm A C K j hK hW xi v (states i)
      (phaseWordEquiv A C K j N xi bits i) := by
    rw [observedTerm,ite_eq_left hpi]
    exact div_pos (evaluate_positive A C hC K hK hW hB (j+1) hj xi hx0 hx1 v _ _)
      (evaluate_positive A C hC K hK hW hB j (by omega) xi hx0 hx1 v _ _)
  unfold observedRatio
  apply div_pos _ (by exact_mod_cast hc)
  exact hterm.trans_le (Finset.single_le_sum
    (fun k _ => observedTerm_nonneg A C hC K j hK hW hB hj xi hx0 hx1 v _ _)
    (Finset.mem_univ i))

structure Stored (A : Instance I J) where
  multiplier : Pair A → Pair A → ℚ
  estimate : ℚ

def update (A : Instance I J) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (old : Stored A)
    (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool) : Option (Stored A) :=
  if CountsPositive A (List.ofFn states) then
    some ⟨rationalLearn pairs old.multiplier (List.ofFn states),
      old.estimate*observedRatio A C K j N hK hW xi v states bits⟩
  else none

/-- A nonaborting update keeps every stored rational positive, even if
all its weight calls were statistically inaccurate. -/
theorem update_positive (A : Instance I J) (C : ℕ) (hC : 0 < C) (K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hj : j+1 ≤ rationalHeight A C) (xi : ℚ) (hx0 : 0 < xi) (hx1 : xi < 1)
    (v : Grid (I := Fin (dimension A)) K) (old next : Stored A)
    (hw : ∀ p q,0 < old.multiplier p q) (hE : 0 < old.estimate)
    (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hu : update A C K j N hK hW xi v old states bits=some next) :
    (∀ p q,0 < next.multiplier p q) ∧ 0 < next.estimate := by
  unfold update at hu
  split_ifs at hu with hc
  · cases Option.some.inj hu
    constructor
    · apply checkedUpdate_positive A old.multiplier hw (List.ofFn states)
      simp only [checkedUpdate,hc,ite_true]
    · exact mul_pos hE (observedRatio_positive A C hC K j N hK hW hB hj xi hx0 hx1 v states hc.1 bits)

lemma update_multiplier_cast (A : Instance I J) (C K j N : ℕ)
    (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (xi : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (old next : Stored A)
    (states : Fin N → Set (Labels A×Bool))
    (bits : Fin (phaseBits A C K j N xi) → Bool)
    (hu : update A C K j N hK hW xi v old states bits=some next) (p q : Pair A) :
    (next.multiplier p q:ℝ)=
      learnedMultipliers pairs (fun p q => (old.multiplier p q:ℝ)) (List.ofFn states) p q := by
  unfold update at hu
  split_ifs at hu
  · cases Option.some.inj hu
    exact rationalLearn_cast _ _ _ _ _

end

end ContingencyTables.CompanionPhaseWords

end OAI
