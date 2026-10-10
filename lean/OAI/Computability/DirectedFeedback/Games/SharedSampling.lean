import Mathlib
import OAI.Computability.DirectedFeedback.Games.ChainRule

namespace OAI


namespace DFVSGames.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

def sharedOutputLaw {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) :
    FiniteDistribution ((X × Y) × S × S) :=
  (μ.product seedLaw).pushforward
    (fun z => (z.1, left z.2 z.1.1, right z.2 z.1.2))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]


open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

def samplerLocal (thresholds : List ℝ) (profile : X → FiniteDistribution S)
    (fallback : S) (n : Nat) (seed : TraceSeed (RectangleSeed thresholds S) n)
    (x : X) : S :=
  localSample (rectangleAccept thresholds (profile x).weight) Prod.fst fallback
    (traceList n seed)

def samplerOutputLaw (thresholds : List ℝ) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) : FiniteDistribution ((X × Y) × S × S) :=
  sharedOutputLaw μ (traceSeedLaw (rectangleDistribution thresholds) n)
    (samplerLocal thresholds L fallback n) (samplerLocal thresholds R fallback n)

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩


end
end DFVSGames.Foundations.Repetition


namespace DFVSGames.Repetition

open DFVSGames.Foundations.Games
open DFVSGames.Foundations.CorrelatedSampling
open DFVSGames.Foundations.Repetition
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

private theorem expectation_mono_inline_RoundingSampling' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const_inline_RoundingSampling' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  simp [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized]

omit [Fintype V] [Fintype S] [Fintype A] in
private theorem first_good_relation_le_inline_RoundingSampling (accept : V → S → Bool)
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
private theorem partial_mass_bounds_inline_RoundingSampling (μ : FiniteDistribution S)
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
          simp [hx, hy, hr] ; linarith [μ.nonnegative s]
      _ = 2 * density := by rw [hdensity x, hdensity y]; ring

private theorem partial_ratio_bound_inline_RoundingSampling {g u density : ℝ} (hdensity : 0 < density)
    (hg : 0 ≤ g) (_hgl : g ≤ density) (hlu : density ≤ u) (hug : u + g ≤ 2 * density) :
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
  obtain ⟨hg, hgl, hlu, hug⟩ := partial_mass_bounds_inline_RoundingSampling μ accept label R density hdensity x y
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
    (first_good_relation_le_inline_RoundingSampling accept label R fallback x y)
  rw [goodFirstIndicator_law μ.weight _ _ μ.normalized n] at hactual
  have hcompl := eventMass_complement μ.weight union μ.normalized
  have hre : eventMass μ.weight (fun s => !(union s)) ≤ 1 - density := by
    change density ≤ eventMass μ.weight union at hlu
    linarith
  have hp := pow_le_pow_left₀
    (eventMass_nonneg μ.weight (fun s => !(union s)) μ.nonnegative) hre n
  have hr := partial_ratio_bound_inline_RoundingSampling hdensity₀ hg hgl hlu hug
  change 2 * (partialPairMass μ accept label R x y / density) - 1 ≤
    partialPairMass μ accept label R x y / eventMass μ.weight union at hr
  change goodFirstMass μ.weight union good n ≤ _ at hactual
  linarith

private theorem expectation_partial_lower_inline_RoundingSampling {E : Type*} [Fintype E]
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
    have hlower := expectation_mono_inline_RoundingSampling' ν hpoint
    rw [expectation_partial_lower_inline_RoundingSampling] at hlower
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
    have hupper := expectation_mono_inline_RoundingSampling' seeds (fun seed => hmax (sample seed))
    rw [expectation_const_inline_RoundingSampling'] at hupper
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
end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open Foundations Games CorrelatedSampling

noncomputable section

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

def thresholdLevels (f : V → Ω → ℝ) : List ℝ := by
  classical
  exact (Finset.univ : Finset (V × Ω)).toList.map (fun p => f p.1 p.2 ^ 2)

theorem square_mem_thresholdLevels (f : V → Ω → ℝ) (x : V) (ω : Ω) :
    f x ω ^ 2 ∈ thresholdLevels f := by
  classical
  apply List.mem_map.mpr
  exact ⟨(x, ω), by simp, rfl⟩

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

theorem threshold_acceptance_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) :
    (thresholdDistribution f).probability (thresholdAccept f x) = thresholdRate Ω := by
  change eventMass (rectangleWeight (thresholdLevels f))
    (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)) = _
  rw [rectangle_acceptance_mass (thresholdLevels f) _
    (square_mem_thresholdLevels f x) (fun ω => sq_nonneg (f x ω))
    (square_le_one_of_row_norm f hnorm x), hnorm x]
  rfl

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

end DFVSGames.Repetition


namespace DFVSGames.Repetition

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
end DFVSGames.Repetition


namespace DFVSGames.Repetition

open scoped BigOperators
open DFVSGames.Foundations.Games

noncomputable section

variable {V A T : Type*} [Fintype V] [Fintype A] [Fintype T]

def rowMass (h : V → A → ℝ) (v : V) : ℝ := ∑ a, h v a

def deterministicVector [DecidableEq A] (h : V → A → ℝ) (labels : V → A)
    (v : V) (a : A) : ℝ :=
  if a = labels v then rowMass h v else 0

omit [Fintype V] in
@[simp] theorem deterministicVector_rowMass [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (v : V) :
    rowMass (deterministicVector h labels) v = rowMass h v := by
  simp [rowMass, deterministicVector]

omit [Fintype V] in
theorem rowMass_nonnegative (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a) (v : V) :
    0 ≤ rowMass h v :=
  Finset.sum_nonneg (fun a _ => hh v a)

omit [Fintype V] in
theorem deterministicVector_nonnegative [DecidableEq A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (labels : V → A) (v : V) (a : A) :
    0 ≤ deterministicVector h labels v a := by
  unfold deterministicVector
  split
  · exact rowMass_nonnegative h hh v
  · exact le_rfl

@[simp] theorem deterministicVector_linear_image [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (c : V → A → ℝ) :
    (∑ v, ∑ a, c v a * deterministicVector h labels v a) =
      ∑ v, c v (labels v) * rowMass h v := by
  simp [deterministicVector, mul_ite]

omit [Fintype V] in
theorem entry_eq_zero_of_rowMass_eq_zero (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (hz : rowMass h v = 0) (a : A) :
    h v a = 0 := by
  have hle : h v a ≤ rowMass h v :=
    Finset.single_le_sum (fun b _ => hh v b) (Finset.mem_univ a)
  exact le_antisymm (hz ▸ hle) (hh v a)

def rowLaw [Nonempty A] (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (v : V) : FiniteDistribution A := by
  classical
  exact if hz : rowMass h v = 0 then
    { weight := fun a => if a = Classical.choice (inferInstance : Nonempty A) then 1 else 0
      nonnegative := fun a => by split <;> norm_num
      normalized := by simp }
  else
    { weight := fun a => h v a / rowMass h v
      nonnegative := fun a => div_nonneg (hh v a) (rowMass_nonnegative h hh v)
      normalized := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        exact mul_inv_cancel₀ hz }

omit [Fintype V] in
theorem rowLaw_expectation_mul_mass [Nonempty A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (f : A → ℝ) :
    (rowLaw h hh v).expectation (fun a => f a * rowMass h v) =
      ∑ a, f a * h v a := by
  classical
  by_cases hz : rowMass h v = 0
  · have he : ∀ a, h v a = 0 := entry_eq_zero_of_rowMass_eq_zero h hh v hz
    simp [FiniteDistribution.expectation, hz, he]
  · simp only [rowLaw, hz, ↓reduceDIte, FiniteDistribution.expectation]
    apply Finset.sum_congr rfl
    intro a _
    field_simp [hz]

theorem square_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (f : Ω → ℝ) :
    law.expectation f ^ 2 ≤ law.expectation (fun x => f x ^ 2) := by
  let m := law.expectation f
  have h : 0 ≤ law.expectation (fun x => (f x - m) ^ 2) := by
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (law.nonnegative x) (sq_nonneg _)
  have he : law.expectation (fun x => (f x - m) ^ 2) =
      law.expectation (fun x => f x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * f x ^ 2 - 2 * m * (law.weight x * f x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => f x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

theorem exists_expectation_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (law : FiniteDistribution Ω) (f : Ω → ℝ) :
    ∃ x, law.expectation f ≤ f x := by
  classical
  let M := Finset.univ.sup' Finset.univ_nonempty f
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset Ω)) Finset.univ_nonempty f
  refine ⟨x, ?_⟩
  calc
    law.expectation f ≤ ∑ y, law.weight y * M := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' f (Finset.mem_univ y)) (law.nonnegative y)
    _ = M := by rw [← Finset.sum_mul, law.normalized, one_mul]
    _ = f x := hx

theorem exists_deterministic_preserving_mass [Nonempty A]
    (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (c : T → V → A → ℝ) :
    ∃ labels : V → A,
      (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
        ∑ t, w t * (∑ v, c t v (labels v) * rowMass h v) ^ 2 := by
  classical
  let law := FiniteDistribution.table (rowLaw h hh)
  let X (t : T) (labels : V → A) : ℝ :=
    ∑ v, c t v (labels v) * rowMass h v
  have hmean (t : T) : law.expectation (X t) = ∑ v, ∑ a, c t v a * h v a := by
    change (∑ labels : V → A, law.weight labels *
      ∑ v, c t v (labels v) * rowMass h v) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    change (FiniteDistribution.table (rowLaw h hh)).expectation
      (fun labels => c t v (labels v) * rowMass h v) = _
    exact (FiniteDistribution.expectation_table_eval (rowLaw h hh) v
      (fun a => c t v a * rowMass h v)).trans
        (rowLaw_expectation_mul_mass h hh v (c t v))
  have hjensen (t : T) : (∑ v, ∑ a, c t v a * h v a) ^ 2 ≤
      law.expectation (fun labels => X t labels ^ 2) := by
    rw [← hmean]
    exact square_expectation_le law (X t)
  have hsum : (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
      ∑ t, w t * law.expectation (fun labels => X t labels ^ 2) := by
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul_of_nonneg_left (hjensen t) (hw t)
  have heq : (∑ t, w t * law.expectation (fun labels => X t labels ^ 2)) =
      law.expectation (fun labels => ∑ t, w t * X t labels ^ 2) := by
    unfold FiniteDistribution.expectation
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro labels _
    apply Finset.sum_congr rfl
    intro t _
    ring
  obtain ⟨labels, hlabels⟩ := exists_expectation_le law
    (fun labels => ∑ t, w t * X t labels ^ 2)
  rw [heq] at hsum
  exact ⟨labels, hsum.trans hlabels⟩

theorem exists_deterministic_vector [Nonempty A] [DecidableEq A]
    (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (c : T → V → A → ℝ) :
    ∃ labels : V → A,
      (∀ v a, 0 ≤ deterministicVector h labels v a) ∧
      (∀ v, rowMass (deterministicVector h labels) v = rowMass h v) ∧
      (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
        ∑ t, w t * (∑ v, ∑ a, c t v a * deterministicVector h labels v a) ^ 2 := by
  obtain ⟨labels, hlabels⟩ := exists_deterministic_preserving_mass h hh w hw c
  refine ⟨labels, deterministicVector_nonnegative h hh labels,
    deterministicVector_rowMass h labels, ?_⟩
  simpa only [deterministicVector_linear_image] using hlabels

end

end DFVSGames.Repetition

end OAI
