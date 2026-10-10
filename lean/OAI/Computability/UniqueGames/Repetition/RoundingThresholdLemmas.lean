import OAI.Computability.UniqueGames.Foundations.Rectangle
import OAI.Computability.UniqueGames.Repetition.RoundingPaddingLemmas
import OAI.Computability.UniqueGames.Repetition.RoundingSampling

namespace OAI

section

/-!
Exact finite threshold expansion for unit vectors.  A shared seed chooses one
coordinate and one atom of the common threshold partition.  Squared amplitudes
are acceptance probabilities, and joint acceptance has the coordinatewise
minimum law.  The construction permits arbitrary vertex-dependent labels and
arbitrary relations between their labels.
-/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open Foundations Games CorrelatedSampling

noncomputable section

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

/-- All squared amplitudes, including repetitions, determine a single shared
finite threshold partition. -/
def thresholdLevels (f : V → Ω → ℝ) : List ℝ := by
  classical
  exact (Finset.univ : Finset (V × Ω)).toList.map (fun p => f p.1 p.2 ^ 2)

theorem square_mem_thresholdLevels (f : V → Ω → ℝ) (x : V) (ω : Ω) :
    f x ω ^ 2 ∈ thresholdLevels f := by
  classical
  apply List.mem_map.mpr
  exact ⟨(x, ω), by simp, rfl⟩

/-- The seed is a coordinate and a finite threshold interval. -/
abbrev ThresholdSeed (f : V → Ω → ℝ) := RectangleSeed (thresholdLevels f) Ω

def thresholdDistribution [Nonempty Ω] (f : V → Ω → ℝ) :
    FiniteDistribution (ThresholdSeed f) := rectangleDistribution (thresholdLevels f)

theorem thresholdSeed_nonempty [Nonempty Ω] (f : V → Ω → ℝ) :
    Nonempty (ThresholdSeed f) := by
  have hsum : (∑ seed, (thresholdDistribution f).weight seed) ≠ 0 := by
    rw [(thresholdDistribution f).normalized]
    norm_num
  obtain ⟨seed, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨seed⟩

def thresholdAccept (f : V → Ω → ℝ) (x : V) : ThresholdSeed f → Bool :=
  rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)

/-- Labels use only the local vertex and the shared coordinate. -/
def thresholdLabel (f : V → Ω → ℝ) (a : V → Ω → A) (x : V)
    (seed : ThresholdSeed f) : A := a x seed.1

def thresholdRate (Ω : Type*) [Fintype Ω] : ℝ := 1 / Fintype.card Ω

theorem thresholdRate_positive [Nonempty Ω] : 0 < thresholdRate Ω := by
  unfold thresholdRate
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := Ω))

omit [Fintype V] in
theorem square_le_one_of_row_norm (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) (ω : Ω) : f x ω ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ t, f x t ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg (f x t)) (Finset.mem_univ ω)
    _ = 1 := hnorm x

/-- Every vertex accepts with the same positive mass, independently of its
unit vector.  Nonnegativity of the amplitudes is unnecessary for this lemma. -/
theorem threshold_acceptance_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) :
    (thresholdDistribution f).probability (thresholdAccept f x) = thresholdRate Ω := by
  change eventMass (rectangleWeight (thresholdLevels f))
    (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)) = _
  rw [rectangle_acceptance_mass (thresholdLevels f) _
    (square_mem_thresholdLevels f x) (fun ω => sq_nonneg (f x ω))
    (square_le_one_of_row_norm f hnorm x), hnorm x]
  rfl

/-- Joint acceptance with any relation on the two local labels has exactly the
minimum-overlap mass.  Both vertices use the same coordinate and threshold. -/
theorem threshold_good_pair_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Prop) [DecidableRel R] :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        decide (R (thresholdLabel f a x seed) (thresholdLabel f a y seed))) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  classical
  change (∑ seed : RectangleSeed (thresholdLevels f) Ω,
    if (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2) seed &&
        rectangleAccept (thresholdLevels f) (fun ω => f y ω ^ 2) seed) &&
        decide (R (a x seed.1) (a y seed.1)) then
      rectangleWeight (thresholdLevels f) seed else 0) = _
  have hand := congrFun (rectangle_and (thresholdLevels f)
    (fun ω => f x ω ^ 2) (fun ω => f y ω ^ 2))
  simp_rw [hand]
  rw [Fintype.sum_prod_type]
  have hrow (ω : Ω) :
      (∑ i : Fin (thresholdPartition (thresholdLevels f)).length,
        if rectangleAccept (thresholdLevels f)
            (fun t => min (f x t ^ 2) (f y t ^ 2)) (ω, i) &&
            decide (R (a x ω) (a y ω)) then
          rectangleWeight (thresholdLevels f) (ω, i) else 0) =
        (if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0) /
          (Fintype.card Ω : ℝ) := by
    by_cases hR : R (a x ω) (a y ω)
    · simpa only [hR, decide_true, Bool.and_true, ite_true] using
        rectangle_row_mass (thresholdLevels f)
          (fun t => min (f x t ^ 2) (f y t ^ 2)) ω
          (min_mem_thresholds _ (square_mem_thresholdLevels f x ω)
            (square_mem_thresholdLevels f y ω))
          (le_min (sq_nonneg _) (sq_nonneg _))
          ((min_le_left _ _).trans (square_le_one_of_row_norm f hnorm x ω))
    · simp [hR]
  simp_rw [hrow]
  simp only [thresholdRate, div_eq_mul_inv, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- Boolean-predicate form used by finite games and the shared sampler. -/
theorem threshold_good_pair_mass_bool [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Bool) :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        R (thresholdLabel f a x seed) (thresholdLabel f a y seed)) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  simpa only [Bool.decide_eq_true] using
    threshold_good_pair_mass f hnorm a x y (fun b c => R b c = true)

end

end UniqueGamesTheorem.Repetition

end

section

/-! High-value rounding of finite nonnegative vectors. The finite threshold
partition and bounded shared rejection sampler produce an ordinary deterministic
labeling. The auxiliary edge sample may retain hidden constraint information;
the labeling receives only its local vertex. -/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V E A Ω : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype Ω]
  [Nonempty V] [Nonempty A] [Nonempty Ω]

omit [Fintype A] [Nonempty V] [Nonempty A] in
theorem threshold_average_good_mass (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) :
    ν.expectation (partialEdgeMass (thresholdDistribution f)
      (thresholdAccept f) (thresholdLabel f a) left right R) =
      thresholdRate Ω * pairOverlap ν left right R a f := by
  unfold partialEdgeMass pairOverlap FiniteDistribution.expectation
  simp_rw [threshold_good_pair_mass_bool f hrow a]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Unit squared row mass converts a large collision energy into a genuinely
local deterministic labeling. All randomness used by the proof is independent
of the sampled constraint, and the final answer has no random seed. -/
theorem exists_labeling_high_value (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_ge_partial
    (thresholdDistribution f) ν (thresholdAccept f) (thresholdLabel f a)
    left right R (thresholdRate Ω) thresholdRate_positive
    (threshold_acceptance_mass f hrow)
  rw [threshold_average_good_mass ν left right R a f hrow,
    mul_div_cancel_left₀ _ (ne_of_gt (thresholdRate_positive (Ω := Ω)))] at hlabels
  have hoverlap := pairOverlap_ge_energy ν left right R a f hf hrow
  refine ⟨labels, ?_⟩
  linarith

omit [Nonempty Ω] in
/-- Rows of mass at most one are completed by private vertex coordinates.
Their nonnegative contribution only improves the collision energy. -/
theorem exists_labeling_high_value_of_rows_le_one (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1) :
    ∃ labels : V → A,
      1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
        partialLabelScore ν left right R labels := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value ν left right R
    (paddedLabel a fallback) (paddedAmplitude f)
    (paddedAmplitude_nonnegative f hf) (paddedAmplitude_row f hrow)
  have henergy := pairEnergy_le_padded ν left right R a f hf fallback
  have hsqrt := Real.sqrt_le_sqrt (show
      2 * (1 - pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f)) ≤
        2 * (1 - pairEnergy ν left right R a f) by linarith)
  exact ⟨labels, (by linarith :
    1 - 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      1 - 2 * Real.sqrt
        (2 * (1 - pairEnergy ν left right R (paddedLabel a fallback)
          (paddedAmplitude f)))).trans hlabels⟩

omit [Nonempty Ω] in
/-- A genuine gap for every deterministic labeling bounds the vector energy
by an alphabet-independent quadratic gap. -/
theorem pairEnergy_le_of_labeling_gap (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v ≤ 1)
    {g : ℝ} (hg : 0 < g)
    (hgap : ∀ labels : V → A, partialLabelScore ν left right R labels ≤ 1 - g) :
    pairEnergy ν left right R a f ≤ 1 - g ^ 2 / 8 := by
  obtain ⟨labels, hlabels⟩ := exists_labeling_high_value_of_rows_le_one
    ν left right R a f hf hrow
  have hbound := hlabels.trans (hgap labels)
  have he : pairEnergy ν left right R a f ≤ 1 := by
    by_contra h
    have hneg : 2 * (1 - pairEnergy ν left right R a f) ≤ 0 := by linarith
    rw [Real.sqrt_eq_zero_of_nonpos hneg] at hbound
    linarith
  have hs := Real.sq_sqrt (show 0 ≤ 2 * (1 - pairEnergy ν left right R a f) by linarith)
  have hgs : g ≤ 2 * Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) := by
    linarith
  have hsq := mul_self_le_mul_self hg.le hgs
  nlinarith

end
end UniqueGamesTheorem.Repetition

end

end OAI
