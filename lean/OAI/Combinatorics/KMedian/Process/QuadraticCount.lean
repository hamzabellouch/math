import Mathlib
import OAI.Combinatorics.KMedian.Probability.BernoulliBatches

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def bit (ω : I → Bool) (i : I) : ℝ := if ω i then 1 else 0
noncomputable def statistic (b : I → ℝ) (c : I → I → ℝ) (ω : I → Bool) : ℝ :=
  (∑ i, b i*bit ω i)+(1/2)*∑ i, ∑ j, c i j*bit ω i*bit ω j

omit [Fintype I] [DecidableEq I] in
theorem bit_nonneg (ω : I → Bool) (i : I) : 0 ≤ bit ω i := by unfold bit; split_ifs <;> norm_num
omit [Fintype I] [DecidableEq I] in
theorem bit_le_one (ω : I → Bool) (i : I) : bit ω i ≤ 1 := by unfold bit; split_ifs <;> norm_num

omit [Fintype I] in
theorem bit_update (ω : I → Bool) (i j : I) (v : Bool) :
    bit (Function.update ω i v) j=if j=i then (if v then (1:ℝ) else 0) else bit ω j := by
  by_cases h : j=i
  · subst j; simp only [bit, Function.update_self, ite_true]
  · simp only [bit, Function.update_of_ne h, ite_eq_right h]

theorem difference (b : I → ℝ) (c : I → I → ℝ)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (ω : I → Bool) (e : I) :
    statistic b c (Function.update ω e true)-statistic b c (Function.update ω e false)=
      b e+∑ j, c e j*bit ω j := by
  let xt := bit (Function.update ω e true)
  let xf := bit (Function.update ω e false)
  have hlin : (∑ i, b i*xt i)-(∑ i, b i*xf i)=b e := by
    rw [← Finset.sum_sub_distrib]
    have hp : ∀ i, b i*xt i-b i*xf i=if i=e then b e else 0 := by
      intro i
      dsimp only [xt, xf]
      simp only [bit_update, Bool.false_eq_true, ite_true, ite_false]
      by_cases hi : i=e
      · subst i; simp only [ite_true, mul_one, mul_zero, sub_zero]
      · simp only [ite_eq_right hi, sub_self]
    simp_rw [hp]
    simp
  have hprod : ∀ i j, c i j*xt i*xt j-c i j*xf i*xf j =
      (if i=e then c e j*bit ω j else 0)+(if j=e then c i e*bit ω i else 0) := by
    intro i j
    dsimp only [xt, xf]
    simp only [bit_update, Bool.false_eq_true, ite_true, ite_false]
    by_cases hi : i=e <;> by_cases hj : j=e
    · subst i; subst j; simp only [hdiag, zero_mul, sub_self, ite_true, add_zero]
    · subst i; simp only [ite_true, ite_eq_right hj, mul_one, mul_zero, zero_mul, sub_zero, add_zero]
    · subst j; simp only [ite_true, ite_eq_right hi, mul_one, mul_zero, sub_zero, zero_add]
    · simp only [ite_eq_right hi, ite_eq_right hj, sub_self, zero_add]
  have hquad : (∑ i, ∑ j, c i j*xt i*xt j)-(∑ i, ∑ j, c i j*xf i*xf j) =
      2*∑ j, c e j*bit ω j := by
    simp only [← Finset.sum_sub_distrib]
    simp_rw [hprod]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hswap : (∑ i, c i e*bit ω i)=(∑ i, c e i*bit ω i) :=
      Finset.sum_congr rfl (fun i _ => by rw [hc i e])
    rw [hswap]
    ring
  unfold statistic
  change (∑ i, b i*xt i)+(1/2)*(∑ i, ∑ j, c i j*xt i*xt j)-
    ((∑ i, b i*xf i)+(1/2)*(∑ i, ∑ j, c i j*xf i*xf j))=_
  linarith only [hlin, hquad]

theorem difference_bound (b : I → ℝ) (c : I → I → ℝ)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (ω : I → Bool) (e : I) :
    |statistic b c (Function.update ω e true)-statistic b c (Function.update ω e false)| ≤
      |b e|+∑ j, c e j := by
  rw [difference b c hc hdiag]
  have hs0 : 0 ≤ ∑ j, c e j*bit ω j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hc0 e j) (bit_nonneg ω j))
  calc
    _ ≤ |b e|+|∑ j, c e j*bit ω j| := abs_add_le _ _
    _ = |b e|+∑ j, c e j*bit ω j := by rw [abs_of_nonneg hs0]
    _ ≤ _ := add_le_add_right (Finset.sum_le_sum (fun j _ =>
      mul_le_of_le_one_right (hc0 e j) (bit_le_one ω j))) _

theorem expectation (p : I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : I → ℝ) (c : I → I → ℝ) (hdiag : ∀ i, c i i=0) :
    (FiniteLaw.bernoulli p hp0 hp1).expect (statistic b c)=
      (∑ i, b i*p i)+(1/2)*∑ i, ∑ j, c i j*p i*p j := by
  let μ := FiniteLaw.bernoulli p hp0 hp1
  have hm : ∀ i, μ.expect (fun ω => bit ω i)=p i := by
    intro i
    exact FiniteLaw.bernoulli_marginal p hp0 hp1 i
  have hpair : ∀ i j, μ.expect (fun ω => c i j*bit ω i*bit ω j)=c i j*p i*p j := by
    intro i j
    by_cases hij : i=j
    · subst j
      simp only [hdiag, zero_mul, FiniteLaw.expect_const]
    · have hp := FiniteLaw.bernoulli_pair p hp0 hp1 hij
      have hpoint : ∀ ω, bit ω i*bit ω j=if ω i=true ∧ ω j=true then (1:ℝ) else 0 := by
        intro ω
        unfold bit
        cases ω i <;> cases ω j <;> norm_num
      simp only [mul_assoc, FiniteLaw.expect_mul]
      simp_rw [hpoint]
      change c i j*μ.prob (fun ω => ω i=true ∧ ω j=true)=_
      rw [hp]
  change μ.expect (statistic b c)=_
  unfold statistic
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_sum, FiniteLaw.expect_mul, hm, hpair]

end MetricKMedian.CountStatistic
end
end

end OAI
