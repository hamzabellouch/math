import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Count

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

namespace OrdinaryCofactorWeight
variable {ι : Type*} [Fintype ι]

def bernoulliWeight (v : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, if ω i = true then v i else 1-v i

lemma bernoulli_nonneg [DecidableEq ι] (v : ι → ℝ)
    (hv : ∀i, 0≤v i ∧ v i≤1) (ω : ι → Bool) :
    0≤bernoulliWeight v ω := by
  unfold bernoulliWeight
  exact Finset.prod_nonneg (fun i _ => by split_ifs <;> linarith [(hv i).1,(hv i).2])

variable [DecidableEq ι]

lemma bernoulli_product (v : ι → ℝ) (F : ι → Bool → ℝ) :
    (∑ω : ι → Bool, bernoulliWeight v ω * ∏i,F i (ω i)) =
      ∏i,(v i*F i true+(1-v i)*F i false) := by
  unfold bernoulliWeight
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i b => (if b=true then v i else 1-v i)*F i b)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]

lemma generating_polynomial (v : ι → ℝ) (z : ℝ) :
    (∑ω : ι → Bool,bernoulliWeight v ω*z^count ω)=∏i,(1-(1-z)*v i) := by
  simp_rw [pow_count]
  rw [bernoulli_product v (fun _ b => if b=true then z else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [ite_true,Bool.false_eq_true,ite_false]
  ring

lemma generating_le_exp (v : ι → ℝ) (hv : ∀i,0≤v i ∧ v i≤1)
    {z : ℝ} (hz : z∈Icc (0:ℝ) 1) :
    (∑ω : ι → Bool,bernoulliWeight v ω*z^count ω)≤
      Real.exp (-(1-z)*(∑i,v i)) := by
  rw [generating_polynomial]
  calc
    _ ≤ ∏i,Real.exp (-(1-z)*v i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        nlinarith [(hv i).1,(hv i).2,hz.1,hz.2]
      · intro i _
        have hh := Real.add_one_le_exp (-(1-z)*v i)
        linarith
    _ = _ := by rw [←Real.exp_sum,←Finset.mul_sum]

lemma beta_integral (k : ℕ) :
    (∫z in (0:ℝ)..1,2*(1-z)*z^k)=2/((k+1:ℝ)*(k+2:ℝ)) := by
  have hfun : (fun z : ℝ => 2*(1-z)*z^k)=(fun z => 2*(z^k-z^(k+1))) := by
    funext z
    rw [pow_succ]
    ring
  rw [hfun,intervalIntegral.integral_const_mul,intervalIntegral.integral_sub,
    integral_pow,integral_pow]
  · simp only [one_pow,zero_pow (by omega : k+1≠0),zero_pow (by omega : k+1+1≠0),
      sub_zero,Nat.cast_add,Nat.cast_one]
    have h1 : (k+1:ℝ)≠0 := by positivity
    have h2 : (k+2:ℝ)≠0 := by positivity
    field_simp
    ring
  · exact (continuous_id.pow _).intervalIntegrable _ _
  · exact (continuous_id.pow _).intervalIntegrable _ _

lemma reciprocal_count_sq_le_beta (k : ℕ) :
    1/(k+1:ℝ)^2 ≤ ∫z in (0:ℝ)..1,2*(1-z)*z^k := by
  rw [beta_integral]
  have h1 : (0:ℝ)<k+1 := by positivity
  have h2 : (0:ℝ)<k+2 := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  nlinarith

lemma exponential_beta_bound {L : ℝ} (hL : 0<L) :
    (∫z in (0:ℝ)..1,2*(1-z)*Real.exp (-(1-z)*L))≤2/L^2 := by
  let F : ℝ → ℝ := fun z => 2*((1-z)/L+1/L^2)*Real.exp (-(1-z)*L)
  have hd (z : ℝ) : HasDerivAt F (2*(1-z)*Real.exp (-(1-z)*L)) z := by
    have h₁ := ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).div_const L
    have h₂ := ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).neg.mul_const L
    have hh := (((hasDerivAt_const z (2:ℝ)).mul
      (h₁.add_const (1/L^2))).mul h₂.exp)
    convert hh using 1 <;> first | rfl | (dsimp; field_simp [ne_of_gt hL]; ring)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => hd z)
    ((by fun_prop : Continuous (fun z : ℝ =>
      2*(1-z)*Real.exp (-(1-z)*L))).intervalIntegrable 0 1)
  rw [hi]
  have h0 : 0≤F 0 := by dsimp [F]; positivity
  have h1 : F 1=2/L^2 := by simp [F,div_eq_mul_inv]
  linarith

theorem reciprocal_count_second_moment (v : ι → ℝ)
    (hv : ∀i,0≤v i ∧ v i≤1) (hL : 0<∑i,v i) :
    (∑ω : ι → Bool,bernoulliWeight v ω/(count ω+1:ℝ)^2)≤2/(∑i,v i)^2 := by
  calc
    _ ≤ ∑ω : ι → Bool,bernoulliWeight v ω*
        (∫z in (0:ℝ)..1,2*(1-z)*z^count ω) := by
      apply Finset.sum_le_sum
      intro ω _
      simpa only [div_eq_mul_inv,one_div,one_mul] using
        mul_le_mul_of_nonneg_left (reciprocal_count_sq_le_beta (count ω))
          (bernoulli_nonneg v hv ω)
    _ = ∫z in (0:ℝ)..1,2*(1-z)*
        (∑ω : ι → Bool,bernoulliWeight v ω*z^count ω) := by
      simp_rw [←intervalIntegral.integral_const_mul]
      rw [←intervalIntegral.integral_finsetSum]
      · apply intervalIntegral.integral_congr
        intro z hz
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      · intro ω hω
        exact (by fun_prop : Continuous (fun z : ℝ =>
          bernoulliWeight v ω*(2*(1-z)*z^count ω))).intervalIntegrable _ _
    _ ≤ ∫z in (0:ℝ)..1,2*(1-z)*Real.exp (-(1-z)*(∑i,v i)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact (by fun_prop : Continuous (fun z : ℝ =>
          2*(1-z)*(∑ω : ι → Bool,bernoulliWeight v ω*z^count ω))).intervalIntegrable _ _
      · exact (by fun_prop : Continuous (fun z : ℝ =>
          2*(1-z)*Real.exp (-(1-z)*(∑i,v i)))).intervalIntegrable _ _
      · intro z hz
        exact mul_le_mul_of_nonneg_left (generating_le_exp v hv hz) (by nlinarith [hz.2])
    _ ≤ _ := exponential_beta_bound hL

end OrdinaryCofactorWeight

end

end OAI
