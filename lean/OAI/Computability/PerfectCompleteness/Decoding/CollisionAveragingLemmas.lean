import Mathlib.Tactic.Linarith
import OAI.Computability.PerfectCompleteness.Construction.HiddenChildMixture
import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanConditioning
import OAI.Computability.PerfectCompleteness.Sampling.DensityVariation

namespace OAI


namespace PerfectCompleteness.CollisionAveraging

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B : Type*} [Fintype B]

theorem mean_square_le (μ : FiniteDistribution B) (p : B → ℝ) :
    μ.expectation p ^ 2 ≤ μ.expectation (fun b => p b ^ 2) :=
  UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le μ.weight p
    ⟨μ.nonnegative, μ.normalized⟩

theorem average_square_bound (μ : FiniteDistribution B) (p collision : B → ℝ)
    (hlocal : ∀ b, p b ^ 2 / 2 ≤ collision b) :
    μ.expectation p ^ 2 / 2 ≤ μ.expectation collision := by
  calc
    _ ≤ μ.expectation (fun b => p b ^ 2) / 2 :=
      div_le_div_of_nonneg_right (mean_square_le μ p) (by norm_num)
    _ = μ.expectation (fun b => p b ^ 2 / 2) :=
      (DensityVariation.expectation_div μ (fun b => p b ^ 2) 2).symm
    _ ≤ μ.expectation collision := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hlocal b) (μ.nonnegative b)

theorem eighth_square_bound (μ : FiniteDistribution B) (p collision : B → ℝ)
    (hlocal : ∀ b, p b ^ 2 / 2 ≤ collision b)
    (c : ℝ) (hc : 0 ≤ c) (hmass : c / 2 ≤ μ.expectation p) :
    c ^ 2 / 8 ≤ μ.expectation collision := by
  have h := average_square_bound μ p collision hlocal
  have hprod : 0 ≤ (μ.expectation p - c / 2) * (μ.expectation p + c / 2) :=
    mul_nonneg (sub_nonneg.mpr hmass) (by linarith)
  nlinarith


variable {Ω Y : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, Fintype (Y b)]

theorem average_collision (μ : FiniteDistribution B)
    (ν : (b : B) → FiniteDistribution (Ω b))
    (f : (b : B) → Ω b → Option (Y b)) (good : (b : B) → Ω b → Bool)
    (hcard : ∀ b, Nat.card {y : Y b // TwoResponseCollision.GoodResponse (f b) (good b) y} ≤ 2) :
    μ.expectation (fun b => (ν b).probability (TwoResponseCollision.goodDefined (f b) (good b))) ^ 2 / 2 ≤
      μ.expectation (fun b => ((ν b).product (ν b)).probability (TwoResponseCollision.collision (f b))) :=
  average_square_bound μ _ _ (fun b =>
    TwoResponseCollision.collision_probability_ge (ν b) (f b) (good b) (hcard b))

theorem actual_eighth_square_bound (μ : FiniteDistribution B)
    (ν : (b : B) → FiniteDistribution (Ω b))
    (f : (b : B) → Ω b → Option (Y b)) (good : (b : B) → Ω b → Bool)
    (hcard : ∀ b, Nat.card {y : Y b // TwoResponseCollision.GoodResponse (f b) (good b) y} ≤ 2)
    (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ μ.expectation
      (fun b => (ν b).probability (TwoResponseCollision.goodDefined (f b) (good b)))) :
    c ^ 2 / 8 ≤ μ.expectation
      (fun b => ((ν b).product (ν b)).probability (TwoResponseCollision.collision (f b))) :=
  eighth_square_bound μ _ _ (fun b =>
    TwoResponseCollision.collision_probability_ge (ν b) (f b) (good b) (hcard b)) c hc hmass

end
end PerfectCompleteness.CollisionAveraging


namespace PerfectCompleteness.SparseProjection

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def localDensity (β : ℝ) (q : (i : I) → Ω i → ℝ) (i : I) (x : Ω i) : ℝ :=
  1 - β + β * q i x

omit [Fintype I] [DecidableEq I] in
theorem local_mean (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (i : I) : (P i).expectation (localDensity β q i) = 1 := by
  calc
    _ = (1 - β) * (P i).expectation (fun _ => 1) + β * (P i).expectation (q i) := by
      simp only [FiniteDistribution.expectation, localDensity, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 1 := by rw [expectation_const, mean]; ring

omit [Fintype I] [DecidableEq I] in
theorem local_second_moment (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (i : I) :
    (P i).expectation (fun x => localDensity β q i x ^ 2) =
      1 + β ^ 2 * (P i).expectation (fun x => (q i x - 1) ^ 2) := by
  calc
    _ = (P i).expectation (fun _ => 1) +
        (2 * β) * ((P i).expectation (q i) - (P i).expectation (fun _ => 1)) +
        β ^ 2 * (P i).expectation (fun x => (q i x - 1) ^ 2) := by
      simp only [FiniteDistribution.expectation, localDensity, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [expectation_const, mean]; ring

def density (β : ℝ) (q : (i : I) → Ω i → ℝ) (x : (i : I) → Ω i) : ℝ :=
  ∏ i, localDensity β q i (x i)

theorem density_mean (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) : (FiniteProduct.law P).expectation (density β q) = 1 := by
  change (FiniteProduct.law P).expectation (fun x => ∏ i, localDensity β q i (x i)) = 1
  rw [FiniteProduct.expectation_product]
  simp only [local_mean P q mean, Finset.prod_const_one]

theorem density_second_moment (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) :
    (FiniteProduct.law P).expectation (fun x => (density β q x - 1) ^ 2) =
      (∏ i, (1 + β ^ 2 * (P i).expectation (fun x => (q i x - 1) ^ 2))) - 1 := by
  have identity : (FiniteProduct.law P).expectation (fun x => (density β q x - 1) ^ 2) =
      (FiniteProduct.law P).expectation (fun x => density β q x ^ 2) -
        2 * (FiniteProduct.law P).expectation (density β q) + 1 := by
    calc
      _ = (FiniteProduct.law P).expectation (fun x => density β q x ^ 2) -
          2 * (FiniteProduct.law P).expectation (density β q) +
          (FiniteProduct.law P).expectation (fun _ => 1) := by
        simp only [FiniteDistribution.expectation, Finset.mul_sum,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [expectation_const]
  rw [identity, density_mean P q mean]
  have square : (FiniteProduct.law P).expectation (fun x => density β q x ^ 2) =
      ∏ i, (P i).expectation (fun x => localDensity β q i x ^ 2) := by
    simp only [density, ← Finset.prod_pow]
    exact FiniteProduct.expectation_product P (fun i x => localDensity β q i x ^ 2)
  rw [square]
  simp only [local_second_moment P q mean]
  ring

theorem density_second_moment_le (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β v : ℝ) (bound : ∀ i, (P i).expectation (fun x => (q i x - 1) ^ 2) ≤ v) :
    (FiniteProduct.law P).expectation (fun x => (density β q x - 1) ^ 2) ≤
      (1 + β ^ 2 * v) ^ Fintype.card I - 1 := by
  rw [density_second_moment P q mean]
  apply sub_le_sub_right
  calc
    _ ≤ ∏ _i : I, (1 + β ^ 2 * v) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have h : 0 ≤ (P i).expectation (fun x => (q i x - 1) ^ 2) :=
          Finset.sum_nonneg fun x _ => mul_nonneg ((P i).nonnegative x) (sq_nonneg _)
        positivity
      · intro i _
        exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left (bound i) (sq_nonneg β))
    _ = _ := by simp

def projectedLaw (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution ((i : I) → Ω i) :=
  FiniteProduct.law (fun i => reweight (P i) (localDensity β q i)
    (fun x => add_nonneg (sub_nonneg.mpr hβ') (mul_nonneg hβ (nonnegative i x)))
    (local_mean P q mean β i))

theorem projected_weight (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (x : (i : I) → Ω i) :
    (projectedLaw P q nonnegative mean β hβ hβ').weight x =
      (FiniteProduct.law P).weight x * density β q x := by
  simp only [projectedLaw, FiniteProduct.law, reweight, Finset.prod_mul_distrib, density]

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (v : ℝ) (bound : ∀ i, (P i).expectation (fun x => (q i x - 1) ^ 2) ≤ v)
    (observe : ((i : I) → Ω i) → Γ) :
    ((projectedLaw P q nonnegative mean β hβ hβ').pushforward observe).totalVariation
        ((FiniteProduct.law P).pushforward observe) ≤
      Real.sqrt ((1 + β ^ 2 * v) ^ Fintype.card I - 1) / 2 :=
  observed_variation_le_sqrt (FiniteProduct.law P) _ (density β q)
    (projected_weight P q nonnegative mean β hβ hβ') _
    (density_second_moment_le P q mean β v bound) observe

end
end PerfectCompleteness.SparseProjection


namespace PerfectCompleteness.ProjectionPosterior

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation SparseProjection CleanConditioning

noncomputable section

def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp, sub_nonneg.mpr hp']
  normalized := by simp

theorem bernoulli_true (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (bernoulli p hp hp').probability id = p := by
  simp [FiniteDistribution.probability, bernoulli]

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

def posterior (β : ℝ) (q : (i : I) → Ω i → ℝ) (i : I) (x : Ω i) : ℝ :=
  β * q i x / localDensity β q i x

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem localDensity_positive (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x) (i : I) (x : Ω i) :
    0 < localDensity β q i x :=
  add_pos_of_pos_of_nonneg (sub_pos.mpr hβ') (mul_nonneg hβ (nonnegative i x))

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem posterior_nonnegative (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x) (i : I) (x : Ω i) :
    0 ≤ posterior β q i x :=
  div_nonneg (mul_nonneg hβ (nonnegative i x))
    (le_of_lt (localDensity_positive β hβ hβ' q nonnegative i x))

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem posterior_le_one (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x) (i : I) (x : Ω i) :
    posterior β q i x ≤ 1 := by
  apply (div_le_iff₀ (localDensity_positive β hβ hβ' q nonnegative i x)).mpr
  unfold localDensity
  linarith

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem posterior_le (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L) (i : I) (x : Ω i) :
    posterior β q i x ≤ β * L / (1 - β) := by
  have hd := localDensity_positive β hβ hβ' q nonnegative i x
  calc
    _ ≤ β * L / localDensity β q i x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (bound i x) hβ) hd.le
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hβ hL) (sub_pos.mpr hβ')
      (by unfold localDensity; linarith [mul_nonneg hβ (nonnegative i x)])

def posteriorMask (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (x : (i : I) → Ω i) : FiniteDistribution (I → Bool) :=
  FiniteProduct.law fun i => bernoulli (posterior β q i (x i))
    (posterior_nonnegative β hβ hβ' q nonnegative i (x i))
    (posterior_le_one β hβ hβ' q nonnegative i (x i))

def forward (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    FiniteDistribution ((I → Bool) × ((i : I) → Ω i)) :=
  kernelJoint (FiniteProduct.law fun _ : I => bernoulli β hβ hβ'.le)
    (fun mask => FiniteProduct.law fun i =>
      if mask i then reweight (P i) (q i) (nonnegative i) (mean i) else P i)

def reverse (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    FiniteDistribution (((i : I) → Ω i) × (I → Bool)) :=
  kernelJoint (projectedLaw P q nonnegative mean β hβ hβ'.le)
    (posteriorMask β hβ hβ' q nonnegative)

theorem forward_reverse_weight (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (mask : I → Bool) (x : (i : I) → Ω i) :
    (forward P q nonnegative mean β hβ hβ').weight (mask, x) =
      (reverse P q nonnegative mean β hβ hβ').weight (x, mask) := by
  change (∏ i, (bernoulli β hβ hβ'.le).weight (mask i)) *
      (∏ i, (if mask i then reweight (P i) (q i) (nonnegative i) (mean i) else P i).weight (x i)) =
    (∏ i, (P i).weight (x i) * localDensity β q i (x i)) *
      (∏ i, (bernoulli (posterior β q i (x i)) _ _).weight (mask i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hd := ne_of_gt (localDensity_positive β hβ hβ' q nonnegative i (x i))
  cases hi : mask i <;> simp only [bernoulli, Bool.false_eq_true, ite_false,
    ite_true, reweight, posterior]
  · field_simp
    unfold localDensity
    ring
  · field_simp

theorem probability_reverse (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (event : ((i : I) → Ω i) → (I → Bool) → Bool) :
    (forward P q nonnegative mean β hβ hβ').probability (fun z => event z.2 z.1) =
      (reverse P q nonnegative mean β hβ hβ').probability (fun z => event z.1 z.2) := by
  simp only [FiniteDistribution.probability, Fintype.sum_prod_type,
    forward_reverse_weight P q nonnegative mean β hβ hβ']
  exact Finset.sum_comm

end
end PerfectCompleteness.ProjectionPosterior


namespace PerfectCompleteness.AdaptiveProjection

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias ProjectionPosterior CleanConditioning

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem probability_selected_le (μ : FiniteDistribution (I → Bool)) (S : Finset I)
    (t : ℝ) (bound : ∀ i, μ.probability (fun mask => mask i) ≤ t) :
    μ.probability (fun mask => decide (∃ i ∈ S, mask i = true)) ≤ S.card * t := by
  classical
  have indicator (mask : I → Bool) :
      (if ∃ i ∈ S, mask i = true then (1 : ℝ) else 0) ≤
        ∑ i ∈ S, if mask i then (1 : ℝ) else 0 := by
    by_cases h : ∃ i ∈ S, mask i = true
    · obtain ⟨i, hi, hm⟩ := h
      rw [ite_eq_left ⟨i, hi, hm⟩]
      calc
        _ = (if mask i then (1 : ℝ) else 0) := by rw [hm]; rfl
        _ ≤ _ := Finset.single_le_sum (s := S) (a := i)
          (f := fun j : I => if mask j then (1 : ℝ) else 0)
          (fun j _ => by split <;> norm_num) hi
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun i _ => by split <;> norm_num
  calc
    _ = μ.expectation (fun mask => if ∃ i ∈ S, mask i = true then 1 else 0) := by
      simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
    _ ≤ μ.expectation (fun mask => ∑ i ∈ S, if mask i then (1 : ℝ) else 0) :=
      expectation_mono μ indicator
    _ = ∑ i ∈ S, μ.probability (fun mask => mask i) := by
      simp only [FiniteDistribution.expectation, FiniteDistribution.probability,
        Finset.mul_sum, mul_ite, mul_one, mul_zero]
      exact Finset.sum_comm
    _ ≤ ∑ _i ∈ S, t := Finset.sum_le_sum fun i _ => bound i
    _ = _ := by simp

variable {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [∀ i, Fintype (Ω i)] in
theorem posteriorMask_marginal (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (x : (i : I) → Ω i) (i : I) :
    (posteriorMask β hβ hβ' q nonnegative x).probability (fun mask => mask i) =
      posterior β q i (x i) := by
  calc
    _ = (posteriorMask β hβ hβ' q nonnegative x).expectation
        (fun mask => if mask i then 1 else 0) := by
      simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
    _ = (bernoulli (posterior β q i (x i)) _ _).expectation
        (fun b => if b then 1 else 0) :=
      FiniteProduct.expectation_eval
        (fun j : I => bernoulli (posterior β q j (x j))
          (posterior_nonnegative β hβ hβ' q nonnegative j (x j))
          (posterior_le_one β hβ hβ' q nonnegative j (x j)))
        i (fun b : Bool => if b then 1 else 0)
    _ = _ := by simp [FiniteDistribution.expectation, ProjectionPosterior.bernoulli]

theorem adaptive_selection (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L)
    (select : ((i : I) → Ω i) → Finset I) (m : ℕ)
    (size : ∀ x, (select x).card ≤ m) :
    (forward P q nonnegative mean β hβ hβ').probability
      (fun z => decide (∃ i ∈ select z.2, z.1 i = true)) ≤
        m * (β * L / (1 - β)) := by
  classical
  rw [probability_reverse P q nonnegative mean β hβ hβ'
    (fun x mask => decide (∃ i ∈ select x, mask i = true))]
  unfold reverse
  rw [probability_kernelJoint]
  have hnonneg : 0 ≤ β * L / (1 - β) :=
    div_nonneg (mul_nonneg hβ hL) (le_of_lt (sub_pos.mpr hβ'))
  calc
    _ ≤ ∑ x, (SparseProjection.projectedLaw P q nonnegative mean β hβ hβ'.le).weight x *
        (m * (β * L / (1 - β))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.nonnegative _ x)
      calc
        _ ≤ (select x).card * (β * L / (1 - β)) :=
          probability_selected_le _ (select x) _ (fun i => by
            rw [posteriorMask_marginal]
            exact posterior_le β hβ hβ' q nonnegative L hL bound i (x i))
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast size x) hnonneg
    _ = _ := by rw [← Finset.sum_mul, FiniteDistribution.normalized, one_mul]

end
end PerfectCompleteness.AdaptiveProjection

end OAI
