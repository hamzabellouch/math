import Mathlib.Analysis.SpecificLimits.Basic
import OAI.Computability.UniqueGames.Games.SelectedCommonMarginalLemmas

namespace OAI

section

/-!
Correlated rounding of finite partial assignments of equal density. A common
finite list of seeds is scanned locally at every vertex. An edge succeeds when
the first seed accepted by either endpoint is a jointly accepted good seed.
The finite truncation error is at most `(1 - density)^n`. Maximizing over the finite
set of deterministic labelings removes that error. No infinite random seed or
assumed rounding principle is used.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Foundations.CorrelatedSampling
open UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators

noncomputable section

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

def partialPairMass (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool) (x y : V) : ℝ :=
  μ.probability (fun s => accept x s && accept y s && R x y (label x s) (label y s))

def partialEdgeMass {E : Type*} (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (left right : E → V) (R : E → A → A → Bool) (e : E) : ℝ :=
  μ.probability (fun s => accept (left e) s && accept (right e) s &&
    R e (label (left e) s) (label (right e) s))

def partialLabelScore {E : Type*} [Fintype E] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool) (f : V → A) : ℝ :=
  ν.probability (fun e => R e (f (left e)) (f (right e)))

def partialSample (accept : V → S → Bool) (label : V → S → A)
    (fallback : A) (proposals : List S) (v : V) : A :=
  localSample (accept v) (label v) fallback proposals

private theorem expectation_mono' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  simp [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized]

omit [Fintype V] [Fintype S] [Fintype A] in
private theorem first_good_relation_le (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool)
    (fallback : A) (x y : V) (proposals : List S) :
    goodFirstIndicator (fun s => accept x s || accept y s)
      (fun s => accept x s && accept y s && R x y (label x s) (label y s)) proposals ≤
    (if R x y (partialSample accept label fallback proposals x)
      (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  cases hfirst : firstAccepted (fun s => accept x s || accept y s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      split <;> norm_num
  | some s =>
      by_cases hg : (accept x s && accept y s && R x y (label x s) (label y s)) = true
      · have hp : (accept x s = true ∧ accept y s = true) ∧
            R x y (label x s) (label y s) = true := by simpa using hg
        have hs := first_union_common (accept x) (accept y) proposals s hfirst hp.1.1 hp.1.2
        simp [goodFirstIndicator, hfirst, partialSample, localSample,
          hs.1, hs.2, hp.1.1, hp.1.2, hp.2]
      · simp only [goodFirstIndicator, hfirst, hg, Bool.false_eq_true, ite_false]
        split <;> norm_num

omit [Fintype V] [Fintype A] in
private theorem partial_mass_bounds (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (density : ℝ)
    (hdensity : ∀ v, μ.probability (accept v) = density) (x y : V) :
    0 ≤ partialPairMass μ accept label R x y ∧
    partialPairMass μ accept label R x y ≤ density ∧
    density ≤ μ.probability (fun s => accept x s || accept y s) ∧
    μ.probability (fun s => accept x s || accept y s) +
      partialPairMass μ accept label R x y ≤ 2 * density := by
  refine ⟨μ.probability_nonnegative _, ?_, ?_, ?_⟩
  · rw [← hdensity x]
    apply μ.probability_mono
    intro s hs
    have hp : (accept x s = true ∧ accept y s = true) ∧
        R x y (label x s) (label y s) = true := by simpa using hs
    exact hp.1.1
  · rw [← hdensity x]
    exact μ.probability_mono (fun s hs => by simp [hs])
  · calc
      _ ≤ μ.probability (accept x) + μ.probability (accept y) := by
        unfold partialPairMass FiniteDistribution.probability
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro s _
        cases hx : accept x s <;> cases hy : accept y s <;>
          cases hr : R x y (label x s) (label y s) <;>
          simp [hx, hy, hr]
        linarith [μ.nonnegative s]
      _ = 2 * density := by rw [hdensity x, hdensity y]; ring

private theorem partial_ratio_bound {g u density : ℝ} (hdensity : 0 < density)
    (hg : 0 ≤ g) (hlu : density ≤ u) (hug : u + g ≤ 2 * density) :
    2 * (g / density) - 1 ≤ g / u := by
  have hu : 0 < u := lt_of_lt_of_le hdensity hlu
  apply (le_div_iff₀ hu).2
  by_cases hsgn : 2 * (g / density) - 1 ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hsgn hu.le).trans hg
  · have hcoeff : 0 ≤ 2 * g - density := by
      have hd : 1 < 2 * g / density := by
        rw [mul_div_assoc]
        linarith
      have := (lt_div_iff₀ hdensity).mp hd
      linarith
    have hm := mul_le_mul_of_nonneg_left hug hcoeff
    have heq : (2 * (g / density) - 1) * u = ((2 * g - density) * u) / density := by
      field_simp [ne_of_gt hdensity]
    rw [heq]
    apply (div_le_iff₀ hdensity).2
    nlinarith [sq_nonneg (density - g)]

omit [Fintype V] [Fintype A] in
/-- Pointwise success bound for the actual shared finite first-accept sampler.
The relation may depend on the ordered pair and need not be symmetric. -/
theorem partialSample_pair_lower (μ : FiniteDistribution S)
    (accept : V → S → Bool) (label : V → S → A)
    (R : V → V → A → A → Bool) (fallback : A) (density : ℝ)
    (hdensity₀ : 0 < density) (hdensity : ∀ v, μ.probability (accept v) = density)
    (x y : V) (n : Nat) :
    2 * (partialPairMass μ accept label R x y / density) - 1 - (1 - density) ^ n ≤
      traceAverage μ.weight n (fun proposals =>
        if R x y (partialSample accept label fallback proposals x)
          (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  let union : S → Bool := fun s => accept x s || accept y s
  let good : S → Bool := fun s =>
    accept x s && accept y s && R x y (label x s) (label y s)
  obtain ⟨hg, _, hlu, hug⟩ := partial_mass_bounds μ accept label R density hdensity x y
  have hu : 0 < eventMass μ.weight union := lt_of_lt_of_le hdensity₀ hlu
  have hm : eventMass μ.weight (fun s => union s && good s) =
      partialPairMass μ accept label R x y := by
    unfold eventMass partialPairMass FiniteDistribution.probability
    apply Finset.sum_congr rfl
    intro s _
    cases hx : accept x s <;> cases hy : accept y s <;> simp [union, good, hx, hy]
  have hfirst := goodFirstMass_lower_bound μ.weight union good
    μ.nonnegative μ.normalized hu n
  rw [hm] at hfirst
  have hactual := traceAverage_mono μ.weight μ.nonnegative n _ _
    (first_good_relation_le accept label R fallback x y)
  rw [goodFirstIndicator_law μ.weight _ _ μ.normalized n] at hactual
  have hcompl := eventMass_complement μ.weight union μ.normalized
  have hre : eventMass μ.weight (fun s => !(union s)) ≤ 1 - density := by
    change density ≤ eventMass μ.weight union at hlu
    linarith
  have hp := pow_le_pow_left₀
    (eventMass_nonneg μ.weight (fun s => !(union s)) μ.nonnegative) hre n
  have hr := partial_ratio_bound hdensity₀ hg hlu hug
  change 2 * (partialPairMass μ accept label R x y / density) - 1 ≤
    partialPairMass μ accept label R x y / eventMass μ.weight union at hr
  change goodFirstMass μ.weight union good n ≤ _ at hactual
  linarith

private theorem expectation_partial_lower {E : Type*} [Fintype E]
    (ν : FiniteDistribution E) (g : E → ℝ) (density tail : ℝ) :
    ν.expectation (fun xy => 2 * (g xy / density) - 1 - tail) =
      2 * (ν.expectation g / density) - 1 - tail := by
  unfold FiniteDistribution.expectation
  calc
    _ = ∑ xy, (2 / density * (ν.weight xy * g xy) - (1 + tail) * ν.weight xy) := by
      apply Finset.sum_congr rfl
      intro xy _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ν.normalized]
      ring

/-- Finite partial-assignment correlated rounding. Every vertex has acceptance
probability `density`. The normalized accepted good-pair mass `T` gives an actual
deterministic labeling with success at least `2*T - 1`. -/
theorem exists_labeling_ge_partial {E : Type*} [Fintype E] [Nonempty V] [Nonempty A]
    (μ : FiniteDistribution S) (ν : FiniteDistribution E)
    (accept : V → S → Bool) (label : V → S → A)
    (left right : E → V) (R : E → A → A → Bool) (density : ℝ) (hdensity₀ : 0 < density)
    (hdensity : ∀ v, μ.probability (accept v) = density) :
    ∃ f : V → A,
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 ≤
        partialLabelScore ν left right R f := by
  classical
  let fallback : A := Classical.choice inferInstance
  obtain ⟨best, _, hbest⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (V → A))) Finset.univ_nonempty (partialLabelScore ν left right R)
  have hmax (f : V → A) :
      partialLabelScore ν left right R f ≤ partialLabelScore ν left right R best := by
    rw [← hbest]
    exact Finset.le_sup' (partialLabelScore ν left right R) (Finset.mem_univ f)
  have hbounded (n : Nat) :
      2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1 -
        (1 - density) ^ n ≤ partialLabelScore ν left right R best := by
    let seeds := traceSeedLaw μ n
    let sample := fun seed => partialSample accept label fallback (traceList n seed)
    have hpoint (e : E) := partialSample_pair_lower μ accept label (fun _ _ => R e)
      fallback density hdensity₀ hdensity (left e) (right e) n
    change ∀ e : E, 2 * (partialEdgeMass μ accept label left right R e / density) - 1 -
      (1 - density) ^ n ≤ traceAverage μ.weight n (fun proposals =>
        if R e (partialSample accept label fallback proposals (left e))
          (partialSample accept label fallback proposals (right e)) then 1 else 0) at hpoint
    have hlower := expectation_mono' ν hpoint
    rw [expectation_partial_lower] at hlower
    have hswitch :
        ν.expectation (fun e => traceAverage μ.weight n (fun proposals =>
          if R e (partialSample accept label fallback proposals (left e))
            (partialSample accept label fallback proposals (right e)) then 1 else 0)) =
        seeds.expectation (fun seed => partialLabelScore ν left right R (sample seed)) := by
      simp_rw [← traceSeedLaw_expectation μ n]
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro seed
      simp [partialLabelScore, FiniteDistribution.probability,
        FiniteDistribution.expectation, sample, mul_ite]
    rw [hswitch] at hlower
    have hupper := expectation_mono' seeds (fun seed => hmax (sample seed))
    rw [expectation_const'] at hupper
    exact hlower.trans hupper
  refine ⟨best, ?_⟩
  have hdensity₁ : density ≤ 1 := by
    rw [← hdensity (Classical.choice (inferInstance : Nonempty V))]
    exact μ.probability_le_one _
  by_contra hn
  have hgap : 0 <
      (2 * (ν.expectation (partialEdgeMass μ accept label left right R) / density) - 1) -
        partialLabelScore ν left right R best := sub_pos.mpr (lt_of_not_ge hn)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - density)
    (by linarith : 1 - density < 1)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hgap)).exists
  linarith [hbounded n]

end
end UniqueGamesTheorem.Repetition

end

end OAI
