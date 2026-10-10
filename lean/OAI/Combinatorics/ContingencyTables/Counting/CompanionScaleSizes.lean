import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialDraw
import OAI.Combinatorics.ContingencyTables.Counting.CompanionMinMass

namespace OAI

/-! # Explicit sizes at the companion's bounded-capacity scale

The unary copy labels are used only below the chosen cutoff, not below
the original binary-encoded capacities. These estimates retain the
cutoff dependency and then substitute the paper's actual polynomial
scale. The initial precision is bounded without executing a real log.
-/

namespace ContingencyTables.CompanionScaleSizes

open CompanionFactorialApplication CompanionInitialDraw
open scoped BigOperators Classical

def strength (d K : ℕ) (epsilon : ℚ) : ℕ :=
  ⌈(2048:ℚ)*d*K^2/epsilon⌉₊

def bins (d C : ℕ) : ℕ := 16*C*d^2

def cutoff (d C : ℕ) : ℕ := 100*d*bins d C

def finalPhase (d C : ℕ) : ℕ := 10*C*d^2*(cutoff d C+1)

lemma strength_source (d K : ℕ) (hd : 0<d) (hK : 0<K)
    (epsilon : ℚ) (he : 0<epsilon) :
    strength d K epsilon=⌈(4:ℚ)*K/(epsilon/(512*d*K))⌉₊ := by
  have hdq : (d:ℚ)≠0 := by exact_mod_cast hd.ne'
  have hkq : (K:ℚ)≠0 := by exact_mod_cast hK.ne'
  unfold strength
  congr 1
  field_simp [hdq,hkq,he.ne']
  ring

lemma cutoff_eq (d C : ℕ) : cutoff d C=1600*C*d^3 := by
  unfold cutoff bins
  ring

lemma strength_le (d K E : ℕ) (epsilon : ℚ) (hE : 1/epsilon≤(E:ℚ)) :
    strength d K epsilon≤2048*d*K^2*E := by
  unfold strength
  apply Nat.ceil_le.mpr
  calc
    (2048:ℚ)*d*K^2/epsilon = ((2048:ℚ)*d*K^2)*(1/epsilon) := by ring
    _ ≤ ((2048:ℚ)*d*K^2)*E := mul_le_mul_of_nonneg_left hE (by positivity)
    _ = ((2048*d*K^2*E:ℕ):ℚ) := by push_cast; rfl

/-- Choosing an integer reciprocal-accuracy bound suffices for every
subsequent numeric loop bound. -/
lemma cutoff_strength_le (d K E : ℕ) (epsilon : ℚ) (hE : 1/epsilon≤(E:ℚ)) :
    cutoff d (strength d K epsilon)≤3276800*d^4*K^2*E := by
  rw [cutoff_eq]
  calc
    _ ≤ 1600*(2048*d*K^2*E)*d^3 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (strength_le d K E epsilon hE))
    _ = _ := by ring

variable {I J : Type*} [Fintype I] [Fintype J]

lemma label_count_le (A : Instance I J) : Fintype.card (Labels A)≤A.d*A.W := by
  rw [CompanionMinMass.label_card]
  calc
    _ ≤ ∑ _s : SmallCell A,A.W := Finset.sum_le_sum (fun s _ => (A.hsmall _ _ s.property).le)
    _ = Fintype.card (SmallCell A)*A.W := by simp
    _ ≤ A.d*A.W := Nat.mul_le_mul_right _ (cellCount_bound A)

lemma scheduled_label_count (A : Instance I J) (C : ℕ) (hW : A.W=cutoff A.d C) :
    Fintype.card (Labels A)≤1600*C*A.d^4 := by
  calc
    _ ≤ A.d*A.W := label_count_le A
    _ = _ := by rw [hW,cutoff_eq]; ring

lemma precision_le (A : Instance I J) (h : ℕ) :
    precision A h≤A.d*(3*A.W+1)+1+h := by
  unfold precision
  apply Nat.add_le_add_right
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)

theorem initialBits_polynomial_bound (A : Instance I J) (h : ℕ) :
    initialBits A (precision A h)≤
      A.d*(A.W+1)*(A.d*(3*A.W+1)+1+h) := by
  exact (initialBits_bound A (precision A h)).trans
    (Nat.mul_le_mul_left _ (precision_le A h))

/-- After substituting W=100dB, B=16Cd², the complete initializer word
length is an explicit polynomial in d, C, and its accuracy exponent. -/
theorem scheduled_initialBits (A : Instance I J) (C h : ℕ) (hW : A.W=cutoff A.d C) :
    initialBits A (precision A h)≤
      A.d*(1600*C*A.d^3+1)*(A.d*(4800*C*A.d^3+1)+1+h) := by
  have hh := initialBits_polynomial_bound A h
  rw [hW,cutoff_eq] at hh
  convert hh using 1
  ring

end ContingencyTables.CompanionScaleSizes

end OAI
