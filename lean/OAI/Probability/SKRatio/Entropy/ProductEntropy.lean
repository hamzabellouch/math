import Mathlib
import OAI.Probability.SKRatio.Entropy.FiniteEntropy

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def productPrior (q : Fin n → Prior Bool) : Prior (Spin n) where
  mass x := ∏ i, q i (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (q i).nonneg (x i))
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [Prior.sum_one,Finset.prod_const_one]

lemma productPrior_pos (q : Fin n → Prior Bool) (hq : ∀ i b,0<q i b) (x : Spin n) :
    0<productPrior q x := by
  change 0 < ∏ i, q i (x i)
  exact Finset.prod_pos (fun i _ => hq i (x i))

lemma sum_cons (F : Spin (n+1) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Spin n, F (Fin.cons b y) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)),Fintype.sum_prod_type]
  rfl

lemma avg_product_succ (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) :
    avg (productPrior q) f = avg (q 0) (fun b =>
      avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))) := by
  unfold avg FiniteLaw.mean
  rw [sum_cons]
  simp only [productPrior,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Finset.mul_sum,mul_assoc]

lemma avg_swap {α β : Type*} [Fintype α] [Fintype β] (p : Prior α) (q : Prior β)
    (F : α → β → ℝ) :
    avg p (fun a => avg q (F a)) = avg q (fun b => avg p (fun a => F a b)) := by
  simp only [avg,FiniteLaw.mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma entropy_product_chain (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) :
    ent (productPrior q) f =
      avg (q 0) (fun b => ent (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))) +
      ent (q 0) (fun b => avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))) := by
  change avg (productPrior q) (fun x => f x*log (f x))-
    avg (productPrior q) f*log (avg (productPrior q) f) = _
  rw [avg_product_succ,avg_product_succ]
  change _ = avg (q 0) (fun b =>
    avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y)*log (f (Fin.cons b y)))-
    avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))*
      log (avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y)))) + _
  rw [avg_sub]
  unfold ent FiniteLaw.entropy
  change _ = _ + (avg (q 0) (fun b =>
    avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y))*
      log (avg (productPrior (fun i => q i.succ)) (fun y => f (Fin.cons b y)))) - _)
  unfold avg
  ring

lemma update_cons_succ (b : Bool) (y : Spin n) (i : Fin n) (z : Bool) :
    Function.update (Fin.cons b y : Spin (n+1)) i.succ z =
      (Fin.cons b (Function.update y i z) : Spin (n+1)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
  · by_cases hk : k=i
    · subst k;simp
    · simp [hk]

def productSiteEntropy (q : Fin n → Prior Bool) (f : Spin n → ℝ) (i : Fin n) : ℝ :=
  avg (productPrior q) (fun x => ent (q i) (fun b => f (Function.update x i b)))

lemma productSiteEntropy_zero (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) :
    productSiteEntropy q f 0 =
      avg (productPrior (fun i => q i.succ)) (fun y => ent (q 0) (fun b => f (Fin.cons b y))) := by
  unfold productSiteEntropy
  rw [avg_product_succ]
  simp only [Fin.update_cons_zero]
  exact avg_const _ _

lemma productSiteEntropy_succ (q : Fin (n+1) → Prior Bool) (f : Spin (n+1) → ℝ) (i : Fin n) :
    productSiteEntropy q f i.succ = avg (q 0) (fun b =>
      productSiteEntropy (fun j => q j.succ) (fun y => f (Fin.cons b y)) i) := by
  unfold productSiteEntropy
  rw [avg_product_succ]
  simp only [update_cons_succ]

theorem product_entropy_tensorization : ∀ (n : ℕ) (q : Fin n → Prior Bool)
    (f : Spin n → ℝ), (∀ x,0<f x) →
    ent (productPrior q) f ≤ ∑ i,productSiteEntropy q f i := by
  intro n
  induction n with
  | zero =>
    intro q f hf
    let x₀ : Spin 0 := fun i => Fin.elim0 i
    have he : f = fun _ => f x₀ := funext (fun x => congrArg f (Subsingleton.elim x x₀))
    rw [he]
    change avg (productPrior q) (fun _ => f x₀*log (f x₀))-
      avg (productPrior q) (fun _ => f x₀)*log (avg (productPrior q) (fun _ => f x₀)) ≤ _
    simp only [avg_const,sub_self,Fin.sum_univ_zero,le_refl]
  | succ n ih =>
    intro q f hf
    rw [entropy_product_chain,Fin.sum_univ_succ,productSiteEntropy_zero]
    simp_rw [productSiteEntropy_succ]
    have h₁ := avg_mono (q 0) (fun b => ih (fun i => q i.succ) (fun y => f (Fin.cons b y))
      (fun y => hf _))
    rw [avg_sum] at h₁
    have h₂ := entropy_average_le (q 0) (productPrior (fun i => q i.succ))
      (fun y b => f (Fin.cons b y)) (fun y b => hf _)
    linarith only [h₁,h₂]

end SKRatio.Observation

namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma invariant_update (i : Fin n) (c : Spin n → ℝ)
    (hc : ∀ x,c (flip i x)=c x) (x : Spin n) (b : Bool) :
    c (Function.update x i b) = c x := by
  by_cases hb : b=x i
  · rw [hb,Function.update_eq_self]
  · have hb' : b= !(x i) := by cases b <;> cases hx : x i <;> simp_all
    rw [hb']
    exact hc x

lemma avg_product_resample : ∀ (n : ℕ) (q : Fin n → Prior Bool)
    (F : Spin n → ℝ) (i : Fin n),
    avg (productPrior q) (fun x => avg (q i) (fun b => F (Function.update x i b))) =
      avg (productPrior q) F := by
  intro n
  induction n with
  | zero => intro q F i;exact Fin.elim0 i
  | succ n ih =>
    intro q F i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [avg_product_succ,avg_product_succ]
      simp only [Fin.update_cons_zero]
      rw [avg_const,avg_swap]
    · rw [avg_product_succ,avg_product_succ]
      simp only [update_cons_succ]
      congr 1
      funext b
      exact ih (fun i => q i.succ) (fun y => F (Fin.cons b y)) j

theorem product_entropy_le_remainders (q : Fin n → Prior Bool)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) (c : Fin n → Spin n → ℝ)
    (hc : ∀ i x,0<c i x) (hinv : ∀ i x,c i (flip i x)=c i x) :
    ent (productPrior q) f ≤ avg (productPrior q) (fun x => ∑ i,logRemainder (f x) (c i x)) := by
  rw [avg_sum]
  apply (product_entropy_tensorization n q f hf).trans
  apply Finset.sum_le_sum
  intro i _
  have hh : productSiteEntropy q f i ≤ avg (productPrior q) (fun x =>
      avg (q i) (fun b => logRemainder (f (Function.update x i b)) (c i x))) :=
    avg_mono _ (fun x => ent_minimizes (q i) _ (fun b => hf _) (hc i x))
  have he : (fun x => avg (q i) (fun b => logRemainder (f (Function.update x i b)) (c i x))) =
      fun x => avg (q i) (fun b => logRemainder (f (Function.update x i b)) (c i (Function.update x i b))) := by
    funext x
    congr 1
    funext b
    rw [invariant_update i (c i) (hinv i)]
  rw [he,avg_product_resample n q (fun x => logRemainder (f x) (c i x)) i] at hh
  exact hh

end SKRatio.Observation

namespace SKRatio.Fields
open Observation
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def sitePrior (g : Disorder n) (h : Fin n → ℝ) (i : Fin n) (x : Spin n) : Prior Bool where
  mass b := (if b then weight g h x else weight g h (flip i x)) /
    (weight g h x+weight g h (flip i x))
  nonneg b := div_nonneg (by split <;> exact (weight_pos _ _ _).le)
    (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).le
  sum_one := by simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,←add_div];
                 rw [add_comm,div_self (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne']

lemma sitePrior_avg (g : Disorder n) (h : Fin n → ℝ) (i : Fin n) (x : Spin n)
    (f : Spin n → ℝ) :
    avg (sitePrior g h i x) (fun b => f (if b then x else flip i x)) =
      conditionalExpectation g h i f x := by
  simp only [avg,FiniteLaw.mean,sitePrior,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,
    conditionalExpectation]
  ring

lemma conditionalExpectation_pos (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) (x : Spin n) :
    0<conditionalExpectation g h i f x := by
  rw [←sitePrior_avg]
  exact avg_pos _ (fun b => hf _)

lemma conditionalExpectation_log_le (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) (x : Spin n) :
    conditionalExpectation g h i (fun y => log (f y)) x ≤ log (conditionalExpectation g h i f x) := by
  rw [←sitePrior_avg g h i x (fun y => log (f y)),←sitePrior_avg g h i x f]
  exact avg_log_le_log_avg (sitePrior g h i x)
    (fun b => f (if b then x else flip i x)) (fun b => hf _)

lemma single_remainder_le_energy (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) :
    expectation g h (fun x => logRemainder (f x) (conditionalExpectation g h i f x)) ≤
      expectation g h (fun x => f x*(log (f x)-conditionalExpectation g h i (fun y => log (f y)) x)) := by
  have he (x : Spin n) := logRemainder_eq (hf x).ne' (conditionalExpectation_pos g h i f hf x).ne'
  simp_rw [he]
  rw [expectation_add,expectation_sub,expectation_conditionalExpectation]
  have hc : expectation g h (fun x => f x*log (f x)-f x*log (conditionalExpectation g h i f x)) ≤
      expectation g h (fun x => f x*(log (f x)-conditionalExpectation g h i (fun y => log (f y)) x)) := by
    apply SKRatio.Fields.expectation_mono
    intro x
    have hj := mul_le_mul_of_nonneg_left (conditionalExpectation_log_le g h i f hf x) (hf x).le
    linarith only [hj]
  linarith only [hc]

theorem remainders_le_energy (g : Disorder n) (h : Fin n → ℝ)
    (f : Spin n → ℝ) (hf : ∀ x,0<f x) :
    expectation g h (fun x => ∑ i,logRemainder (f x) (conditionalExpectation g h i f x)) ≤
      expectation g h (fun x => f x*heatBathGenerator g h (fun y => log (f y)) x) := by
  unfold heatBathGenerator
  simp only [Finset.mul_sum]
  rw [expectation_sum,expectation_sum]
  exact Finset.sum_le_sum (fun i _ => single_remainder_le_energy g h i f hf)

end SKRatio.Fields

end
end

end OAI
