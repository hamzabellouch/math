import Mathlib
import OAI.Computability.MinUncut.Games.OuterQuestions

namespace OAI

namespace MinUncutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem iid_pushforward {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f : Ω → Γ) (n : Nat) :
    (μ.pushforward f).iid n =
      (μ.iid n).pushforward (fun answers i => f (answers i)) := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [iid, pushforward]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : (fun i => f (x i)) = y
  · have hp : ∀ i, f (x i) = y i := congrFun h
    simp [hp]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ i, f (x i) = y i := fun hp => h (funext hp)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteDistribution Ω where
  weight _ := 1 / (Fintype.card Ω : ℝ)
  nonnegative _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  normalized := by
    have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hn

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end
end MinUncutGames.Foundations.Games.FiniteDistribution

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncutGames.Foundations.Games
attribute [local instance] Classical.propDecidable
variable {Name S : Type*}

instance equationFintype [Fintype Name] : Fintype (Equation Name) :=
  Fintype.ofEquiv ((Fin 3 → Name) × F₂)
    { toFun := fun x => ⟨x.1,x.2⟩
      invFun := fun E => (E.names,E.rhs)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def ordinaryAccepts (E : Equation Name) (x : Name) (a : Triple) (b : F₂) : Bool :=
  decide (Valid E a ∧ ∀ p, E.names p=x → a p=b)

lemma ordinary_all_implies_satisfied (E : Equation Name) (a : Triple) (s : Name → F₂)
    (h : ∀ p, ordinaryAccepts E (E.names p) a (s (E.names p))=true) :
    Satisfied s E := by
  have hvalid : Valid E a := (of_decide_eq_true (h 0)).1
  have he : a=evaluatedTriple s E := by
    funext p
    exact (of_decide_eq_true (h p)).2 p rfl
  simpa only [Satisfied,← he] using hvalid.1

lemma ordinary_coordinate_bound (E : Equation Name) (a : Triple) (s : Name → F₂) :
    (∑ p : Fin 3, if ordinaryAccepts E (E.names p) a (s (E.names p)) then (1 : ℝ) else 0)
      ≤ 2+(if Satisfied s E then (1 : ℝ) else 0) := by
  have hall := ordinary_all_implies_satisfied E a s
  simp only [Fin.sum_univ_three]
  by_cases h0 : ordinaryAccepts E (E.names 0) a (s (E.names 0))=true
  <;> by_cases h1 : ordinaryAccepts E (E.names 1) a (s (E.names 1))=true
  <;> by_cases h2 : ordinaryAccepts E (E.names 2) a (s (E.names 2))=true
  · have hs : Satisfied s E := hall (by intro p; fin_cases p <;> assumption)
    norm_num [h0,h1,h2,hs]
  all_goals simp only [h0,h1,h2,Bool.false_eq_true,↓reduceIte]; split <;> norm_num

variable [Fintype S] [Nonempty S]

def equationFraction (equations : S → Equation Name) (s : Name → F₂) : ℝ :=
  (∑ i, if Satisfied s (equations i) then (1 : ℝ) else 0)/(Fintype.card S : ℝ)

variable [Fintype Name]

def ordinaryGame (equations : S → Equation Name) :
    Game (Equation Name) Name Triple F₂ where
  questions := (FiniteDistribution.uniform (S × Fin 3)).pushforward
    (fun ip => (equations ip.1,(equations ip.1).names ip.2))
  accepts := ordinaryAccepts

lemma ordinary_success_formula (equations : S → Equation Name)
    (strategy : Strategy (Equation Name) Name Triple F₂) :
    (ordinaryGame equations).success strategy =
      (∑ i, ∑ p : Fin 3,
        if ordinaryAccepts (equations i) ((equations i).names p)
          (strategy.1 (equations i)) (strategy.2 ((equations i).names p)) then
          (1 : ℝ) else 0) / ((Fintype.card S : ℝ)*3) := by
  unfold Game.success
  dsimp only [ordinaryGame]
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability,FiniteDistribution.uniform,Game.wins,
    Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_div,ite_div,zero_div]

lemma ordinary_success_le (equations : S → Equation Name)
    (strategy : Strategy (Equation Name) Name Triple F₂) :
    (ordinaryGame equations).success strategy ≤
      (2+equationFraction equations strategy.2)/3 := by
  have hc : (0 : ℝ)<Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  rw [ordinary_success_formula]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun i _ => ordinary_coordinate_bound (equations i) (strategy.1 (equations i)) strategy.2)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  unfold equationFraction
  apply (div_le_iff₀ (mul_pos hc (by norm_num : (0 : ℝ)<3))).2
  calc
    _ ≤ (Fintype.card S : ℝ)*2 +
        ∑ i, if Satisfied strategy.2 (equations i) then (1 : ℝ) else 0 := hsum
    _ = _ := by field_simp

theorem ordinary_value_le (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4) :
    (ordinaryGame equations).value ≤ 11/12 := by
  apply (Game.value_le_iff _ _).2
  intro strategy
  have h := ordinary_success_le equations strategy
  have hs := hsound strategy.2
  linarith

end MinUncut.Outer

end
namespace MinUncutGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def relativeEntropy (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

theorem posterior_isProbability (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) : IsProbability (posterior p w z) := by
  constructor
  · intro a
    exact div_nonneg (mul_nonneg (hp.1 a) (hw a)) hz.le
  · simp only [posterior, div_eq_mul_inv, ← Finset.sum_mul, hmass,
      mul_inv_cancel₀ hz.ne']

omit [Fintype α] in
theorem posterior_supportedBy (p w : α → ℝ) (z : ℝ) :
    SupportedBy (posterior p w z) p := by
  intro a ha hp
  exact ha (by simp [posterior, hp])

theorem mul_log_div_ge_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * Real.log (x / y) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  have hm := mul_le_mul_of_nonneg_left h hx.le
  have he : x * (1 - (x / y)⁻¹) = x - y := by
    field_simp [hx.ne', hy.ne']
  rwa [he] at hm

theorem relativeEntropy_nonneg (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) : 0 ≤ relativeEntropy p q := by
  have hpoint : ∀ a, p a - q a ≤ p a * Real.log (p a / q a) := by
    intro a
    by_cases hpa : p a = 0
    · simp only [hpa, zero_sub, zero_div, zero_mul]
      exact neg_nonpos.mpr (hq.1 a)
    · exact mul_log_div_ge_sub (lt_of_le_of_ne (hp.1 a) (Ne.symm hpa))
        (lt_of_le_of_ne (hq.1 a) (Ne.symm (hs a hpa)))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, hp.2, hq.2] using hsum

theorem posterior_relativeEntropy_le (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    relativeEntropy (posterior p w z) p ≤ Real.log (1 / z) := by
  have hpost := posterior_isProbability p w hp hw hz hmass
  have hpoint : ∀ a, posterior p w z a * Real.log (posterior p w z a / p a) ≤
      posterior p w z a * Real.log (1 / z) := by
    intro a
    by_cases hpa : posterior p w z a = 0
    · simp [hpa]
    have hpne := posterior_supportedBy p w z a hpa
    have hppos : 0 < p a := lt_of_le_of_ne (hp.1 a) (Ne.symm hpne)
    have hpostpos : 0 < posterior p w z a :=
      lt_of_le_of_ne (hpost.1 a) (Ne.symm hpa)
    have hr : posterior p w z a / p a = w a / z := by
      dsimp [posterior]
      field_simp [hpne, hz.ne']
    apply mul_le_mul_of_nonneg_left _ (hpost.1 a)
    apply Real.log_le_log (div_pos hpostpos hppos)
    rw [hr]
    exact div_le_div_of_nonneg_right (hw_one a) hz.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simpa only [relativeEntropy, ← Finset.sum_mul, hpost.2, one_mul] using hsum

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

theorem totalVariation_le_one (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ≤ 1 := by
  have hpoint : ∀ a, |p a - q a| ≤ p a + q a := by
    intro a
    rw [abs_le]
    constructor <;> linarith [hp.1 a, hq.1 a]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib, hp.2, hq.2] at hsum
  dsimp [totalVariation]
  linarith

theorem le_binaryLog_of_le_log {r x : ℝ} (hr : 0 ≤ r) (h : r ≤ Real.log x) :
    r ≤ Real.log x / Real.log 2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_one : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at ht ⊢
    exact ht
  apply (le_div_iff₀ htwo).2
  exact (mul_le_mul_of_nonneg_left htwo_one hr).trans (by simpa using h)

theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

def product (p : α → ℝ) (q : β → ℝ) : α × β → ℝ := fun ab => p ab.1 * q ab.2

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem secondMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (secondMarginal p) := by
  constructor
  · intro b
    exact Finset.sum_nonneg (fun a _ => hp.1 (a, b))
  · change (∑ b, ∑ a, p (a, b)) = 1
    rw [Finset.sum_comm]
    exact (firstMarginal_isProbability p hp).2

theorem product_isProbability (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) : IsProbability (product p q) := by
  constructor
  · intro ab
    exact mul_nonneg (hp.1 ab.1) (hq.1 ab.2)
  · simp only [product, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one, hp.2]

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

theorem point_le_secondMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ secondMarginal p b := by
  classical
  exact Finset.single_le_sum (fun a _ => hp.1 (a, b)) (Finset.mem_univ a)

theorem joint_supportedBy_product_marginals (p : α × β → ℝ) (hp : IsProbability p) :
    SupportedBy p (product (firstMarginal p) (secondMarginal p)) := by
  intro ab hpne
  have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hpne)
  exact mul_ne_zero
    (ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2)))
    (ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2)))

theorem relativeEntropy_product_reference (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy p (product u v) =
      relativeEntropy p (product (firstMarginal p) (secondMarginal p)) +
        relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v := by
  have hpoint : ∀ ab : α × β, p ab * Real.log (p ab / product u v ab) =
      p ab * Real.log (p ab / product (firstMarginal p) (secondMarginal p) ab) +
      p ab * Real.log (firstMarginal p ab.1 / u ab.1) +
      p ab * Real.log (secondMarginal p ab.2 / v ab.2) := by
    intro ab
    by_cases hzero : p ab = 0
    · simp [hzero]
    have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hzero)
    have hleft := ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2))
    have hright := ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2))
    have hune := (lt_of_le_of_ne (hu.1 ab.1) (Ne.symm (hsu ab.1 hleft))).ne'
    have hvne := (lt_of_le_of_ne (hv.1 ab.2) (Ne.symm (hsv ab.2 hright))).ne'
    simp only [product, Real.log_div hzero (mul_ne_zero hune hvne),
      Real.log_div hzero (mul_ne_zero hleft hright), Real.log_mul hune hvne,
      Real.log_mul hleft hright, Real.log_div hleft hune, Real.log_div hright hvne]
    ring
  have hleftSum : (∑ ab : α × β, p ab * Real.log (firstMarginal p ab.1 / u ab.1)) =
      relativeEntropy (firstMarginal p) u := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, relativeEntropy, firstMarginal]
  have hrightSum : (∑ ab : α × β, p ab * Real.log (secondMarginal p ab.2 / v ab.2)) =
      relativeEntropy (secondMarginal p) v := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, relativeEntropy, secondMarginal]
  unfold relativeEntropy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleftSum, hrightSum]
  rfl

theorem marginal_relativeEntropy_sum_le (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v ≤
      relativeEntropy p (product u v) := by
  rw [relativeEntropy_product_reference p u v hp hu hv hsu hsv]
  have hn := relativeEntropy_nonneg p (product (firstMarginal p) (secondMarginal p)) hp
    (product_isProbability _ _ (firstMarginal_isProbability p hp)
      (secondMarginal_isProbability p hp)) (joint_supportedBy_product_marginals p hp)
  linarith

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

theorem conditionalKernel_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback) (a : α) :
    IsProbability (conditionalKernel p fallback a) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · simpa only [IsProbability, conditionalKernel, ite_eq_left hm] using hf
  · constructor
    · intro b
      simp only [conditionalKernel, ite_eq_right hm]
      exact div_nonneg (hp.1 (a, b))
        ((firstMarginal_isProbability p hp).1 a)
    · simp only [conditionalKernel, ite_eq_right hm, div_eq_mul_inv, ← Finset.sum_mul]
      change firstMarginal p a * (firstMarginal p a)⁻¹ = 1
      exact mul_inv_cancel₀ hm

theorem marginal_mul_conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (a : α) (b : β) :
    firstMarginal p a * conditionalKernel p fallback a b = p (a, b) := by
  classical
  by_cases hm : firstMarginal p a = 0
  · have hpoint := point_le_firstMarginal p hp a b
    rw [hm] at hpoint
    have hz : p (a, b) = 0 := le_antisymm hpoint (hp.1 (a, b))
    simp [conditionalKernel, hm, hz]
  · simp only [conditionalKernel, ite_eq_right hm]
    calc
      firstMarginal p a * (p (a, b) / firstMarginal p a)
          = p (a, b) *
              (firstMarginal p a / firstMarginal p a) := by ring
      _ = p (a, b) := by rw [div_self hm, mul_one]

theorem law_of_total_probability
    (p : α × β → ℝ) (fallback : β → ℝ)
    (hp : IsProbability p) (b : β) :
    (∑ a, firstMarginal p a * conditionalKernel p fallback a b) =
      secondMarginal p b := by
  simp only [marginal_mul_conditionalKernel p fallback hp, secondMarginal]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

theorem alternativeInput_conditionalProduct_isProbability
    (p : α × β → ℝ) (fallback : β → ℝ) (r : α → ℝ)
    (hp : IsProbability p) (hf : IsProbability fallback)
    (hr : IsProbability r) :
    IsProbability
      (fun ab : α × β => r ab.1 * conditionalKernel p fallback ab.1 ab.2) :=
  kernelProduct_isProbability r (conditionalKernel p fallback) hr
    (conditionalKernel_isProbability p fallback hp hf)

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

theorem totalVariation_condition_le (p q : α → ℝ) (event : α → Prop)
    [DecidablePred event] {c : ℝ} (hc : 0 < c) :
    totalVariation (fun a => if event a then p a / c else 0)
      (fun a => if event a then q a / c else 0) ≤ totalVariation p q / c := by
  have hpoint : ∀ a, |(if event a then p a / c else 0) -
      (if event a then q a / c else 0)| ≤ |p a - q a| / c := by
    intro a
    by_cases he : event a
    · simp only [ite_eq_left he, ← sub_div, abs_div, abs_of_pos hc, le_refl]
    · simp only [ite_eq_right he, sub_self, abs_zero]
      exact div_nonneg (abs_nonneg _) hc.le
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [div_eq_mul_inv, ← Finset.sum_mul] at hsum
  have hd := div_le_div_of_nonneg_right hsum (show (0 : ℝ) ≤ 2 by norm_num)
  have hreorder : ((∑ a, |p a - q a|) * c⁻¹) / 2 =
      ((∑ a, |p a - q a|) / 2) / c := by ring
  rw [hreorder] at hd
  simpa only [totalVariation, div_eq_mul_inv] using hd

theorem weighted_coordinate_sum_sq_le
    (w : α → ℝ) (d : α → β → ℝ) (C : α → ℝ)
    (hw : IsProbability w)
    (hbudget : ∀ a, w a * (∑ b, d a b ^ 2) ≤ w a * C a) :
    (∑ b, ∑ a, w a * d a b)^2 ≤
      (Fintype.card β : ℝ) * (∑ a, w a * C a) := by
  have hv := Finset.sum_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset β)) =>
      weighted_sum_sq_le w (fun a => d a b) hw)
  have he :
      (∑ b, ∑ a, w a * d a b ^ 2) =
        ∑ a, w a * (∑ b, d a b ^ 2) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he] at hv
  have hb := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbudget a)
  have hs := hv.trans hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset β)
    (fun b => ∑ a, w a * d a b) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ b, ∑ a, w a * d a b)^2
        ≤ (∑ b, (∑ a, w a * d a b)^2) *
            (Fintype.card β : ℝ) := hcs
    _ = (Fintype.card β : ℝ) *
          (∑ b, (∑ a, w a * d a b)^2) := mul_comm _ _
    _ ≤ (Fintype.card β : ℝ) * (∑ a, w a * C a) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

end MinUncutGames.Foundations.Information

end OAI
