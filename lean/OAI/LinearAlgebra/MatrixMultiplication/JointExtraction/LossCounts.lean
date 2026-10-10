import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexFiniteEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexSeparationCounting
import Mathlib.Tactic.Linarith

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointLossCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*}

theorem card_filter_exists_le (samples : Finset Ω) (indices : Finset I)
    (event : I → Ω → Prop) :
    (samples.filter (fun ω => ∃ i ∈ indices, event i ω)).card ≤
      ∑ i ∈ indices, (samples.filter (event i)).card := by
  classical
  have heq : samples.filter (fun ω => ∃ i ∈ indices, event i ω) =
      indices.biUnion (fun i => samples.filter (event i)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hω, i, hi, he⟩
      exact ⟨i, hi, hω, he⟩
    · rintro ⟨i, hi, hω, he⟩
      exact ⟨hω, i, hi, he⟩
  rw [heq]
  exact Finset.card_biUnion_le

theorem competitor_union_card_mul_le (ownSurvival : Finset Ω)
    (competitors : Finset I) (collision : I → Ω → Prop) (M : ℕ)
    (hcollision : ∀ i ∈ competitors,
      M * (ownSurvival.filter (collision i)).card ≤ ownSurvival.card) :
    M * (ownSurvival.filter (fun ω => ∃ i ∈ competitors, collision i ω)).card ≤
      competitors.card * ownSurvival.card := by
  classical
  calc
    _ ≤ M * ∑ i ∈ competitors, (ownSurvival.filter (collision i)).card :=
      Nat.mul_le_mul_left M (card_filter_exists_le ownSurvival competitors collision)
    _ = ∑ i ∈ competitors, M * (ownSurvival.filter (collision i)).card :=
      by rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ competitors, ownSurvival.card :=
      Finset.sum_le_sum hcollision
    _ = _ := by simp

def randomLossCount (passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : ℕ := by
  classical
  exact (passing.filter (fun v => bad v ω)).card

def randomLossFraction (full passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : ℝ :=
  (randomLossCount passing bad ω : ℝ) / (full.card : ℝ)

theorem randomLossFraction_nonneg (full passing : Finset V)
    (bad : V → Ω → Prop) (ω : Ω) : 0 ≤ randomLossFraction full passing bad ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sum_randomLossCount (ownSurvival : Finset Ω) (passing : Finset V)
    (bad : V → Ω → Prop) :
    (∑ ω ∈ ownSurvival, randomLossCount passing bad ω) =
      ∑ v ∈ passing, (ownSurvival.filter (bad v)).card := by
  classical
  simp only [randomLossCount, Finset.card_filter]
  exact Finset.sum_comm

theorem sum_randomLossCount_le (ownSurvival : Finset Ω) (full passing : Finset V)
    (bad : V → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε) (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    (∑ ω ∈ ownSurvival, (randomLossCount passing bad ω : ℝ)) ≤
      (full.card : ℝ) * (ε * (ownSurvival.card : ℝ)) := by
  classical
  have hdouble : (∑ ω ∈ ownSurvival, (randomLossCount passing bad ω : ℝ)) =
      ∑ v ∈ passing, ((ownSurvival.filter (bad v)).card : ℝ) := by
    exact_mod_cast sum_randomLossCount ownSurvival passing bad
  rw [hdouble]
  calc
    _ ≤ ∑ _v ∈ passing, ε * (ownSurvival.card : ℝ) := Finset.sum_le_sum hbad
    _ = (passing.card : ℝ) * (ε * (ownSurvival.card : ℝ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card hpassing)
      (mul_nonneg hε (Nat.cast_nonneg _))

theorem sum_randomLossFraction_le (ownSurvival : Finset Ω) (full passing : Finset V)
    (bad : V → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε) (hfull : 0 < full.card)
    (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    (∑ ω ∈ ownSurvival, randomLossFraction full passing bad ω) ≤
      ε * (ownSurvival.card : ℝ) := by
  have hcard : (0 : ℝ) < full.card := by exact_mod_cast hfull
  simp only [randomLossFraction, ← Finset.sum_div]
  apply (div_le_iff₀ hcard).2
  simpa only [mul_comm] using
    sum_randomLossCount_le ownSurvival full passing bad ε hε hpassing hbad

theorem conditional_mean_randomLossFraction_le
    (ownSurvival : Finset Ω) (full passing : Finset V) (bad : V → Ω → Prop)
    (ε : ℝ) (hε : 0 ≤ ε) (hs : 0 < ownSurvival.card) (hfull : 0 < full.card)
    (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    (∑ ω ∈ ownSurvival, randomLossFraction full passing bad ω) /
      (ownSurvival.card : ℝ) ≤ ε := by
  apply (div_le_iff₀ (by exact_mod_cast hs : (0 : ℝ) < ownSurvival.card)).2
  exact sum_randomLossFraction_le ownSurvival full passing bad ε hε hfull hpassing hbad

theorem card_filter_mul_le_sum (samples : Finset Ω) (f : Ω → ℝ) (t : ℝ)
    (hf : ∀ ω ∈ samples, 0 ≤ f ω) :
    ((samples.filter (fun ω => t < f ω)).card : ℝ) * t ≤
      ∑ ω ∈ samples, f ω := by
  classical
  calc
    _ = ∑ _ω ∈ samples.filter (fun ω => t < f ω), t := by simp
    _ ≤ ∑ ω ∈ samples.filter (fun ω => t < f ω), f ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact (Finset.mem_filter.mp hω).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω hω _ => hf ω hω)

theorem bad_orbit_card_le (ownSurvival : Finset Ω) (full passing : Finset V)
    (bad : V → Ω → Prop) (ε N : ℝ) (hε : 0 ≤ ε) (hN : 0 < N)
    (hfull : 0 < full.card) (hpassing : passing ⊆ full)
    (hbad : ∀ v ∈ passing,
      ((ownSurvival.filter (bad v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ)) :
    ((ownSurvival.filter (fun ω => 1 / N < randomLossFraction full passing bad ω)).card : ℝ)
      ≤ N * ε * (ownSurvival.card : ℝ) := by
  classical
  have hm := card_filter_mul_le_sum ownSurvival
    (randomLossFraction full passing bad) (1 / N)
    (fun ω _ => randomLossFraction_nonneg full passing bad ω)
  have he := sum_randomLossFraction_le ownSurvival full passing bad ε hε hfull hpassing hbad
  have hdiv :
      ((ownSurvival.filter (fun ω => 1 / N < randomLossFraction full passing bad ω)).card : ℝ) / N
        ≤ ε * (ownSurvival.card : ℝ) := by
    simpa only [one_div, ← div_eq_mul_inv] using hm.trans he
  have hmul := (div_le_iff₀ hN).1 hdiv
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul

def targetBad (orbits : Finset I) (full passing : I → Finset V)
    (bad : I → V → Ω → Prop) (eligible : Ω → Prop) (N : ℝ) (ω : Ω) : Prop :=
  ¬ eligible ω ∨ ∃ i ∈ orbits, 1 / N < randomLossFraction (full i) (passing i) (bad i) ω

theorem targetBad_card_le (ownSurvival : Finset Ω) (orbits : Finset I)
    (full passing : I → Finset V) (bad : I → V → Ω → Prop)
    (eligible : Ω → Prop) (ε eligibilityError N : ℝ)
    (hε : 0 ≤ ε) (hN : 0 < N)
    (hfull : ∀ i ∈ orbits, 0 < (full i).card)
    (hpassing : ∀ i ∈ orbits, passing i ⊆ full i)
    (hbad : ∀ i ∈ orbits, ∀ v ∈ passing i,
      ((ownSurvival.filter (bad i v)).card : ℝ) ≤ ε * (ownSurvival.card : ℝ))
    (heligible : ((ownSurvival.filter (fun ω => ¬ eligible ω)).card : ℝ) ≤
      eligibilityError * (ownSurvival.card : ℝ)) :
    ((ownSurvival.filter (targetBad orbits full passing bad eligible N)).card : ℝ) ≤
      (eligibilityError + (orbits.card : ℝ) * N * ε) * (ownSurvival.card : ℝ) := by
  classical
  let excess := fun i ω => 1 / N < randomLossFraction (full i) (passing i) (bad i) ω
  have hunion : ownSurvival.filter (targetBad orbits full passing bad eligible N) =
      (ownSurvival.filter (fun ω => ¬ eligible ω)) ∪
        (ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union, targetBad, excess]
    constructor
    · rintro ⟨hω, he | ho⟩
      · exact Or.inl ⟨hω, he⟩
      · exact Or.inr ⟨hω, ho⟩
    · rintro (⟨hω, he⟩ | ⟨hω, ho⟩)
      · exact ⟨hω, Or.inl he⟩
      · exact ⟨hω, Or.inr ho⟩
  have hu : ((ownSurvival.filter (targetBad orbits full passing bad eligible N)).card : ℝ) ≤
      ((ownSurvival.filter (fun ω => ¬ eligible ω)).card : ℝ) +
        ((ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω)).card : ℝ) := by
    rw [hunion]
    exact_mod_cast Finset.card_union_le
      (ownSurvival.filter (fun ω => ¬ eligible ω))
      (ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω))
  have horbits : ((ownSurvival.filter (fun ω => ∃ i ∈ orbits, excess i ω)).card : ℝ) ≤
      ∑ i ∈ orbits, ((ownSurvival.filter (excess i)).card : ℝ) := by
    exact_mod_cast card_filter_exists_le ownSurvival orbits excess
  have hsum : (∑ i ∈ orbits, ((ownSurvival.filter (excess i)).card : ℝ)) ≤
      (orbits.card : ℝ) * (N * ε * (ownSurvival.card : ℝ)) := by
    calc
      _ ≤ ∑ _i ∈ orbits, N * ε * (ownSurvival.card : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact bad_orbit_card_le ownSurvival (full i) (passing i) (bad i)
          ε N hε hN (hfull i hi) (hpassing i hi) (hbad i hi)
      _ = _ := by simp
  calc
    _ ≤ eligibilityError * (ownSurvival.card : ℝ) +
        (orbits.card : ℝ) * (N * ε * (ownSurvival.card : ℝ)) :=
      hu.trans (add_le_add heligible (horbits.trans hsum))
    _ = _ := by ring

theorem good_card_lower (ownSurvival : Finset Ω) (failure : Ω → Prop) (error : ℝ)
    (hbad : ((ownSurvival.filter failure).card : ℝ) ≤ error * (ownSurvival.card : ℝ)) :
    (1 - error) * (ownSurvival.card : ℝ) ≤
      ((ownSurvival.filter (fun ω => ¬ failure ω)).card : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := ownSurvival) failure
  have hsplitR : ((ownSurvival.filter failure).card : ℝ) +
      ((ownSurvival.filter (fun ω => ¬ failure ω)).card : ℝ) =
      (ownSurvival.card : ℝ) := by exact_mod_cast hsplit
  nlinarith

section MissingVariables

variable [DecidableEq V]

def retained (passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : Finset V :=
  passing.filter (fun v => ¬ bad v ω)

def deterministicLossFraction (full passing : Finset V) : ℝ :=
  ((full \ passing).card : ℝ) / (full.card : ℝ)

def missingFraction (full passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : ℝ :=
  ((full \ retained passing bad ω).card : ℝ) / (full.card : ℝ)

theorem missing_card_eq (full passing : Finset V) (bad : V → Ω → Prop) (ω : Ω)
    (hpassing : passing ⊆ full) :
    (full \ retained passing bad ω).card =
      (full \ passing).card + randomLossCount passing bad ω := by
  classical
  have hkeep : retained passing bad ω ⊆ full :=
    (Finset.filter_subset _ _).trans hpassing
  have h₁ := Finset.card_sdiff_add_card_eq_card hpassing
  have h₂ := Finset.card_sdiff_add_card_eq_card hkeep
  have h₃ := Finset.card_filter_add_card_filter_not
    (s := passing) (fun v => bad v ω)
  simp only [retained, randomLossCount] at *
  omega

theorem missingFraction_eq (full passing : Finset V) (bad : V → Ω → Prop) (ω : Ω)
    (hpassing : passing ⊆ full) :
    missingFraction full passing bad ω = deterministicLossFraction full passing +
      randomLossFraction full passing bad ω := by
  unfold missingFraction deterministicLossFraction randomLossFraction
  rw [missing_card_eq full passing bad ω hpassing, Nat.cast_add, add_div]

theorem good_missingFraction_le (orbits : Finset I) (full passing : I → Finset V)
    (bad : I → V → Ω → Prop) (eligible : Ω → Prop) (C₀ N : ℝ) (ω : Ω)
    (hgood : ¬ targetBad orbits full passing bad eligible N ω)
    (hpassing : ∀ i ∈ orbits, passing i ⊆ full i)
    (hdet : ∀ i ∈ orbits, deterministicLossFraction (full i) (passing i) ≤ C₀ / N)
    (i : I) (hi : i ∈ orbits) :
    missingFraction (full i) (passing i) (bad i) ω ≤ (C₀ + 1) / N := by
  have hr : randomLossFraction (full i) (passing i) (bad i) ω ≤ 1 / N := by
    apply le_of_not_gt
    intro h
    exact hgood (Or.inr ⟨i, hi, h⟩)
  rw [missingFraction_eq (full i) (passing i) (bad i) ω (hpassing i hi)]
  calc
    _ ≤ C₀ / N + 1 / N := add_le_add (hdet i hi) hr
    _ = _ := (add_div C₀ 1 N).symm

end MissingVariables

end MatrixMultiplication.JointLossCounts

end

end OAI
