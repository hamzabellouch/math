import OAI.Combinatorics.GraphThreshold.Basic
import OAI.Combinatorics.GraphThreshold.LocalFailureNumerics
import OAI.Combinatorics.GraphThreshold.CopyOrbits
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace OAI

/-!
# Maximizing predecessors

The predecessor is chosen by maximization over the actual finite powerset,
including its empty member.  The graph application uses distinct group-orbit
copies and the actual containment probability, not labeled embeddings.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

/-- The standard real binomial upper bound, derived directly from the
exponential series and the factorial upper bound on `choose`. -/
theorem choose_le_exp_div_pow (h r : ℕ) (hr : 0 < r) :
    (h.choose r : ℝ) ≤ (Real.exp 1 * (h : ℝ) / (r : ℝ)) ^ r := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hexp : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp 1 ^ r := by
    simpa only [← Real.exp_nat_mul, mul_one] using
      Real.pow_div_factorial_le_exp (r : ℝ) (show 0 ≤ (r : ℝ) by positivity) r
  calc
    (h.choose r : ℝ) ≤ (h : ℝ) ^ r / (r.factorial : ℝ) := Nat.choose_le_pow_div r h
    _ = ((h : ℝ) / (r : ℝ)) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ ((h : ℝ) / (r : ℝ)) ^ r * Real.exp 1 ^ r :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (Real.exp 1 * (h : ℝ) / (r : ℝ)) ^ r := by
      rw [← mul_pow]
      congr 1
      ring

theorem two_choose_div_le_predecessor_power (h r : ℕ) (hr : 0 < r)
    (hhr : h ≤ 17 * r) :
    2 * (h.choose r : ℝ) / (128 : ℝ) ^ r ≤
      2 * (17 * Real.exp 1 / 128) ^ r := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast hr
  have hhr' : (h : ℝ) ≤ 17 * (r : ℝ) := by exact_mod_cast hhr
  have hbase : Real.exp 1 * (h : ℝ) / (r : ℝ) ≤ 17 * Real.exp 1 := by
    apply (div_le_iff₀ hr0).mpr
    calc
      Real.exp 1 * (h : ℝ) ≤ Real.exp 1 * (17 * (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hhr' (Real.exp_pos 1).le
      _ = _ := by ring
  have hchoose : (h.choose r : ℝ) ≤ (17 * Real.exp 1) ^ r :=
    (choose_le_exp_div_pow h r hr).trans (pow_le_pow_left₀ (by positivity) hbase r)
  calc
    2 * (h.choose r : ℝ) / (128 : ℝ) ^ r ≤
        2 * (17 * Real.exp 1) ^ r / (128 : ℝ) ^ r :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by rw [div_pow]; ring

theorem two_choose_div_lt_one (h r : ℕ) (hr : 0 < r) (hhr : h ≤ 17 * r) :
    2 * (h.choose r : ℝ) / (128 : ℝ) ^ r < 1 :=
  (two_choose_div_le_predecessor_power h r hr hhr).trans_lt
    (predecessor_power_lt_one hr)

/-- Arithmetic form of the expectation constraint and internal-copy count bound. -/
theorem normalized_count_score_bound {a m h r : ℕ} {q : ℝ}
    (hq : 0 < q) (hm : 0 < m) (ha : a ≤ h.choose r)
    (he : (1 / 2 : ℝ) ≤ (m : ℝ) * q ^ r) :
    ((a : ℝ) / (m : ℝ)) / (128 * q) ^ r ≤
      2 * (h.choose r : ℝ) / (128 : ℝ) ^ r := by
  apply (div_le_iff₀ (pow_pos (by positivity : 0 < 128 * q) r)).mpr
  have hscale : (2 * (h.choose r : ℝ) / (128 : ℝ) ^ r) * (128 * q) ^ r =
      2 * (h.choose r : ℝ) * q ^ r := by
    rw [mul_pow]
    field_simp
  rw [hscale]
  apply (div_le_iff₀ (show 0 < (m : ℝ) by exact_mod_cast hm)).mpr
  have ha' : (a : ℝ) ≤ (h.choose r : ℝ) := by exact_mod_cast ha
  have hprod := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 2 * (h.choose r : ℝ) by positivity)
  nlinarith

section FiniteMaximum

variable {X : Type*}

private theorem exists_powerset_max (I : Finset X) (score : Finset X → ℝ) :
    ∃ S ∈ I.powerset, ∀ U ∈ I.powerset, score U ≤ score S :=
  Finset.exists_max_image I.powerset score ⟨∅, by simp⟩

/-- A deterministic classical choice of a maximizer over all subsets of `I`.
The empty set is included, so this definition also applies to empty `I`. -/
def maximizingSubset (I : Finset X) (score : Finset X → ℝ) : Finset X :=
  (exists_powerset_max I score).choose

theorem maximizingSubset_subset (I : Finset X) (score : Finset X → ℝ) :
    maximizingSubset I score ⊆ I :=
  Finset.mem_powerset.mp (exists_powerset_max I score).choose_spec.1

theorem le_maximizingSubset (I : Finset X) (score : Finset X → ℝ)
    {U : Finset X} (hU : U ⊆ I) : score U ≤ score (maximizingSubset I score) :=
  (exists_powerset_max I score).choose_spec.2 U (Finset.mem_powerset.mpr hU)

end FiniteMaximum

section OrbitPredecessor

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

def predecessorScore (I : Finset X) (σ : ℝ) (S : Finset X) : ℝ :=
  containmentProb G I S / σ ^ S.card

/-- The actual maximizing predecessor; the finite choice includes the empty set. -/
def maximizingPredecessor (I : Finset X) (σ : ℝ) : Finset X :=
  maximizingSubset I (predecessorScore G I σ)

theorem maximizingPredecessor_subset (I : Finset X) (σ : ℝ) :
    maximizingPredecessor G I σ ⊆ I :=
  maximizingSubset_subset I _

theorem predecessorScore_le_max (I : Finset X) (σ : ℝ)
    {S : Finset X} (hS : S ⊆ I) :
    predecessorScore G I σ S ≤ predecessorScore G I σ (maximizingPredecessor G I σ) :=
  le_maximizingSubset I _ hS

@[simp]
theorem predecessorScore_empty (I : Finset X) (σ : ℝ) :
    predecessorScore G I σ ∅ = 1 := by
  simp [predecessorScore]

theorem one_le_predecessorScore_max (I : Finset X) (σ : ℝ) :
    1 ≤ predecessorScore G I σ (maximizingPredecessor G I σ) := by
  simpa using predecessorScore_le_max G I σ (Finset.empty_subset I)

theorem predecessorScore_eq_of_mem_copyOrbit (σ : ℝ) {I S S₀ : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G S) :
    predecessorScore G I σ S₀ = predecessorScore G I σ S := by
  rw [predecessorScore, predecessorScore,
    containmentProb_eq_of_mem_copyOrbit G hS₀, card_eq_of_mem_copyOrbit G hS₀]

/-- A positive observation pulls back to an actual subset of `I`; zero-probability
observations cannot exceed the empty set's score.  Thus the chosen finite
maximum controls every observed set, not only subsets of the original copy. -/
theorem predecessorScore_le_max_all (I U : Finset X) (σ : ℝ) :
    predecessorScore G I σ U ≤ predecessorScore G I σ (maximizingPredecessor G I σ) := by
  by_cases hzero : containmentProb G I U = 0
  · rw [predecessorScore, hzero, zero_div]
    exact zero_le_one.trans (one_le_predecessorScore_max G I σ)
  · have hpos : 0 < containmentProb G I U :=
      lt_of_le_of_ne (containmentProb_nonneg G I U) (Ne.symm hzero)
    obtain ⟨V, hVI, hcopy, _⟩ := exists_pullback_of_containmentProb_pos G hpos
    rw [predecessorScore_eq_of_mem_copyOrbit G σ hcopy]
    exact predecessorScore_le_max G I σ hVI

theorem predecessorScore_le_two_choose {I S : Finset X} {q : ℝ}
    (hq : 0 < q)
    (hE : (1 / 2 : ℝ) ≤ (orbitCount G S : ℝ) * q ^ S.card) :
    predecessorScore G I (128 * q) S ≤
      2 * (I.card.choose S.card : ℝ) / (128 : ℝ) ^ S.card := by
  rw [predecessorScore, containmentProb_eq_internalCopyCount]
  exact normalized_count_score_bound hq (orbitCount_pos G S)
    (internalCopyCount_le_choose G I S) hE

/-- The maximizing predecessor is less than one seventeenth of the current set.
The only probabilistic input is the actual expectation constraint for its
nonempty edge subsets. -/
theorem maximizingPredecessor_small (I : Finset X) (hI : I.Nonempty)
    {q : ℝ} (hq : 0 < q)
    (hE : ∀ S : Finset X, S ⊆ I → S.Nonempty →
      (1 / 2 : ℝ) ≤ (orbitCount G S : ℝ) * q ^ S.card) :
    17 * (maximizingPredecessor G I (128 * q)).card < I.card := by
  by_contra hsmall
  have hcardI : 0 < I.card := Finset.card_pos.mpr hI
  have hlarge : I.card ≤ 17 * (maximizingPredecessor G I (128 * q)).card := by omega
  have hcardS : 0 < (maximizingPredecessor G I (128 * q)).card := by omega
  have hbound := predecessorScore_le_two_choose G (I := I) hq
    (hE _ (maximizingPredecessor_subset G I _) (Finset.card_pos.mp hcardS))
  have hlt := hbound.trans_lt (two_choose_div_lt_one I.card _ hcardS hlarge)
  have hge := one_le_predecessorScore_max G I (128 * q)
  linarith

theorem predecessor_copy_prob_pos (I : Finset X) (σ : ℝ) {S₀ : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G (maximizingPredecessor G I σ)) :
    0 < containmentProb G I S₀ :=
  containmentProb_pos_of_copy_subset G (maximizingPredecessor_subset G I σ) hS₀

theorem predecessor_conditional_ratio_le (I : Finset X) {σ : ℝ} (hσ : 0 < σ)
    {S₀ J : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G (maximizingPredecessor G I σ))
    (hdisj : Disjoint S₀ J) :
    containmentProb G I (S₀ ∪ J) / containmentProb G I S₀ ≤ σ ^ J.card := by
  have hscore := predecessorScore_le_max_all G I (S₀ ∪ J) σ
  rw [← predecessorScore_eq_of_mem_copyOrbit G σ hS₀] at hscore
  simp only [predecessorScore, Finset.card_union_of_disjoint hdisj, pow_add] at hscore
  have hpowS : 0 < σ ^ S₀.card := pow_pos hσ _
  have hpowJ : 0 < σ ^ J.card := pow_pos hσ _
  have hclear := (div_le_div_iff₀ (mul_pos hpowS hpowJ) hpowS).mp hscore
  have hnum : containmentProb G I (S₀ ∪ J) ≤
      σ ^ J.card * containmentProb G I S₀ := by
    apply (mul_le_mul_iff_right₀ hpowS).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hclear
  exact (div_le_iff₀ (predecessor_copy_prob_pos G I σ hS₀)).mpr hnum

end OrbitPredecessor

end LeanBlast.SecondKahnKalai

end

end OAI
