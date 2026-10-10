import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Truncation

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical

namespace OrdinaryCorrelations.SourceBonferroni
open Classical
variable {ι Ω Ω' : Type*}

lemma truncation_comparison (s : Finset Ω) (w : Ω → ℝ) (E : ι → Ω → Prop)
    (s' : Finset Ω') (w' : Ω' → ℝ) (E' : ι → Ω' → Prop)
    (P : Finset ι) (r : ℕ) :
    |eventTruncation s w P E r - eventTruncation s' w' P E' r| ≤
      ∑ k ∈ Finset.range (r+1), ∑ t ∈ P.powersetCard k,
        |intersectionMass s w E t - intersectionMass s' w' E' t| := by
  unfold eventTruncation
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range (r+1),
        |(-1:ℝ)^k * (∑ t ∈ P.powersetCard k, intersectionMass s w E t) -
          (-1:ℝ)^k * (∑ t ∈ P.powersetCard k, intersectionMass s' w' E' t)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_sub,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _

theorem sieve_transfer (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (E : ι → Ω → Prop) (s' : Finset Ω') (w' : Ω' → ℝ)
    (hw' : ∀ x ∈ s', 0 ≤ w' x) (E' : ι → Ω' → Prop)
    (P : Finset ι) (r : ℕ) :
    survivalMass s w P E ≤ survivalMass s' w' P E' +
      (∑ t ∈ P.powersetCard (2*r+1), intersectionMass s' w' E' t) +
      (∑ k ∈ Finset.range (2*r+1), ∑ t ∈ P.powersetCard k,
        |intersectionMass s w E t - intersectionMass s' w' E' t|) := by
  have ha := (finite_bonferroni s w hw P E r).1
  have hb := (finite_bonferroni s' w' hw' P E' r).2
  have hc := (le_abs_self _).trans (truncation_comparison s w E s' w' E' P (2*r))
  linarith

variable [Fintype ι]

def bernoulliWeight (v : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i = true then v i else 1-v i

def bernoulliEvent (i : ι) (ω : ι → Bool) : Prop := ω i = true

lemma bernoulli_nonneg (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (ω : ι → Bool) :
    0 ≤ bernoulliWeight v ω := by
  unfold bernoulliWeight
  exact Finset.prod_nonneg (fun i _ => by split_ifs <;> linarith [(hv i).1,(hv i).2])

lemma bernoulli_product (v : ι → ℝ) (F : ι → Bool → ℝ) :
    (∑ ω : ι → Bool, bernoulliWeight v ω * ∏ i, F i (ω i)) =
      ∏ i, (v i * F i true + (1-v i)*F i false) := by
  unfold bernoulliWeight
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if b = true then v i else 1-v i) * F i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool, Bool.false_eq_true,ite_false,ite_true]

lemma joint_prod (t : Finset ι) (ω : ι → Bool) :
    joint bernoulliEvent t ω =
      ∏ i, if i ∈ t then (if ω i = true then (1:ℝ) else 0) else 1 := by
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.prod_const_one,mul_one]
  rw [Finset.prod_boole]
  simp only [joint,bernoulliEvent]
  congr 1

lemma bernoulli_intersection (v : ι → ℝ) (t : Finset ι) :
    intersectionMass Finset.univ (bernoulliWeight v) bernoulliEvent t = ∏ i ∈ t, v i := by
  unfold intersectionMass
  simp_rw [joint_prod]
  rw [bernoulli_product v (fun i b => if i ∈ t then (if b = true then (1:ℝ) else 0) else 1)]
  calc
    _ = ∏ i, if i ∈ t then v i else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ t <;> simp [hi]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.prod_const_one,mul_one]

lemma bernoulli_survival (v : ι → ℝ) :
    survivalMass Finset.univ (bernoulliWeight v) Finset.univ bernoulliEvent =
      ∏ i, (1-v i) := by
  have he (ω : ι → Bool) : survives Finset.univ bernoulliEvent ω =
      ∏ i, if ω i = true then (0:ℝ) else 1 := by
    have hj : (∏ i, if ω i ≠ true then (1:ℝ) else 0) =
        if ∀ i, ω i ≠ true then (1:ℝ) else 0 := Fintype.prod_boole
    simpa only [survives,bernoulliEvent,Finset.mem_univ,forall_true_left,ite_not] using hj.symm
  unfold survivalMass
  simp_rw [he]
  rw [bernoulli_product v (fun _ b => if b = true then (0:ℝ) else 1)]
  simp

theorem finite_upper_sieve (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x)
    (E : ι → Ω → Prop) (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (r : ℕ) :
    survivalMass s w Finset.univ E ≤ (∏ i, (1-v i)) + elementary Finset.univ v (2*r+1) +
      (∑ k ∈ Finset.range (2*r+1), ∑ t ∈ Finset.univ.powersetCard k,
        |intersectionMass s w E t - ∏ i ∈ t, v i|) := by
  have h := sieve_transfer s w hw E Finset.univ (bernoulliWeight v)
      (fun ω _ => bernoulli_nonneg v hv ω) bernoulliEvent Finset.univ r
  simpa only [bernoulli_survival,bernoulli_intersection,elementary] using h

end OrdinaryCorrelations.SourceBonferroni

end

end OAI
