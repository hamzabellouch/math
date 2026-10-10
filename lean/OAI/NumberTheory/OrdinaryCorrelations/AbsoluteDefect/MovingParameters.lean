import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingSquareCompletePartialSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DivisorsEqFilterIoc
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ArithmeticTwist
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelConstant

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

namespace OrdinaryCorrelations.PretentiousEuler
open Completion Filter Finset OrdinaryArchimedeanTwist

def MovingParameters := {p : ℕ × ℝ // |p.2|≤(p.1:ℝ)/2}
def movingFilter : Filter MovingParameters := comap (fun p => p.1.1) atTop

lemma moving_length_tendsto : Tendsto (fun p : MovingParameters => p.1.1) movingFilter atTop :=
  tendsto_comap

lemma quotient_square_dominates (d N : ℕ) (hd : 0<d) (hN : 4*d*d≤N) :
    N≤(N/d)^2 := by
  have hq : 2*d≤N/d := (Nat.le_div_iff_mul_le hd).2 (by nlinarith)
  have hr := Nat.mod_lt N hd
  have he := Nat.mod_add_div N d
  nlinarith

lemma normalized_sum_small (M : ℕ) (hM : 0<M) (S : ℂ) (ε : ℝ)
    (hS : ‖S‖≤ε*(M:ℝ)) : ‖(M:ℂ)⁻¹*S‖≤ε := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (M:ℝ)⁻¹*(ε*(M:ℝ)) := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hMr.le)
    _ = ε := by rw [mul_left_comm,inv_mul_cancel₀ hMr.ne',mul_one]

lemma moving_quotient_mean_tendsto {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (d : ℕ) (hd : d≠0) :
    Tendsto (fun p : MovingParameters => (((p.1.1/d:ℕ):ℂ))⁻¹*
      ∑m∈Finset.Ioc 0 (p.1.1/d),twist (complete f) p.1.2 m) movingFilter (nhds 0) := by
  have hq : Tendsto (fun p : MovingParameters => p.1.1/d) movingFilter atTop :=
    (Nat.tendsto_div_const_atTop hd).comp moving_length_tendsto
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs := hq.eventually (moving_square_complete_partial_small hf hNP (ε/2) (by positivity))
  filter_upwards [hs,moving_length_tendsto.eventually (eventually_ge_atTop (4*d*d)),
    hq.eventually (eventually_ge_atTop (1:ℕ))] with p hp hN hq1
  have hdom : (p.1.1:ℝ)≤((p.1.1/d:ℕ):ℝ)^2 := by
    exact_mod_cast quotient_square_dominates d p.1.1 (Nat.pos_of_ne_zero hd) hN
  have hτ : |p.1.2|≤((p.1.1/d:ℕ):ℝ)^2/2 := by linarith [p.2]
  have heq : Finset.Icc 1 (p.1.1/d)=Finset.Ioc 0 (p.1.1/d) := by
    ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
  have hbound := hp p.1.2 hτ
  rw [heq] at hbound
  rw [_root_.dist_zero_right]
  exact (normalized_sum_small _ (by omega) _ (ε/2) hbound).trans_lt (by linarith)

lemma moving_normalized_div_tendsto {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (d : ℕ) :
    Tendsto (fun p : MovingParameters => (p.1.1:ℂ)⁻¹*
      ∑m∈Finset.Ioc 0 (p.1.1/d),twist (complete f) p.1.2 m) movingFilter (nhds 0) := by
  by_cases hd : d=0
  · subst d
    simpa only [Nat.div_zero,Finset.Ioc_self,Finset.sum_empty,mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : MovingParameters => (0:ℂ)) movingFilter (nhds 0))
  have ht := moving_quotient_mean_tendsto hf hNP d hd
  have hdr : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := (Metric.tendsto_nhds.mp ht) (ε*(d:ℝ)) (mul_pos hε hdr)
  filter_upwards [hh] with p hp
  rw [_root_.dist_zero_right] at hp ⊢
  calc
    _ ≤ ‖(((p.1.1/d:ℕ):ℂ))⁻¹*∑m∈Finset.Ioc 0 (p.1.1/d),
        twist (complete f) p.1.2 m‖/(d:ℝ) :=
      OrdinaryConvolution.normalized_div_norm (twist (complete f) p.1.2) p.1.1 d
    _ < ε := (div_lt_iff₀ hdr).2 hp

theorem moving_multiplicative_mean_tendsto_zero {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f) :
    Tendsto (fun p : MovingParameters => (p.1.1:ℂ)⁻¹*
      ∑n∈Finset.Icc 1 p.1.1,twist f p.1.2 n) movingFilter (nhds 0) := by
  rcases one_or_zero hm with h1 | hz
  · have hs : Summable (fun d : ℕ => ‖kernel f d‖/(d:ℝ)) := by
      have he (d : ℕ) : kernelWeight f 1 d=‖kernel f d‖/(d:ℝ) := by
        simp [kernelWeight,Real.rpow_neg_one,div_eq_mul_inv]
      have hfun : kernelWeight f 1=(fun d : ℕ => ‖kernel f d‖/(d:ℝ)) := funext he
      simpa only [hfun] using (kernelWeight_summable hf hm h1 (by norm_num : (1:ℝ)/2<1)).1
    let A := fun (p : MovingParameters) (d : ℕ) => twist (kernel f) p.1.2 d*
        ((p.1.1:ℂ)⁻¹*∑m∈Finset.Ioc 0 (p.1.1/d),twist (complete f) p.1.2 m)
    have hterm (d : ℕ) : Tendsto (fun p => A p d) movingFilter (nhds 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have he (p : MovingParameters) : ‖A p d‖=‖kernel f d‖*
          ‖(p.1.1:ℂ)⁻¹*∑m∈Finset.Ioc 0 (p.1.1/d),twist (complete f) p.1.2 m‖ := by
        simp only [A,norm_mul,norm_twist]
      simp_rw [he]
      simpa only [norm_zero,mul_zero] using (moving_normalized_div_tendsto hf hNP d).norm.const_mul ‖kernel f d‖
    have hbound (p : MovingParameters) (d : ℕ) : ‖A p d‖≤‖kernel f d‖/(d:ℝ) := by
      simp only [A,norm_mul,norm_twist]
      have hh := OrdinaryConvolution.normalized_div_bound (twist (complete f) p.1.2)
        (fun n => by simpa only [norm_twist] using complete_oneBounded hf n) p.1.1 d
      have hh' := mul_le_mul_of_nonneg_left hh (norm_nonneg (kernel f d))
      simpa only [one_div,div_eq_mul_inv,one_mul,norm_mul] using hh'
    have hlim := tendsto_tsum_of_dominated_convergence hs (g:=fun _ : ℕ => (0:ℂ)) hterm
      (Filter.Eventually.of_forall hbound)
    have he (p : MovingParameters) : (p.1.1:ℂ)⁻¹*∑n∈Finset.Icc 1 p.1.1,twist f p.1.2 n=∑'d,A p d := by
      have heq : Finset.Icc 1 p.1.1=Finset.Ioc 0 p.1.1 := by
        ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
      rw [heq]
      have hec : (∑n∈Finset.Ioc 0 p.1.1,twist f p.1.2 n)=
          ∑n∈Finset.Ioc 0 p.1.1,
            (arithmeticTwist (kernel f) p.1.2*arithmeticTwist (complete f) p.1.2) n := by
        rw [←arithmeticTwist_mul,kernel_reconstruct]
        apply sum_congr rfl
        intro n hn
        simp only [arithmeticTwist_apply,twist,arithmetic_apply_pos f (Finset.mem_Ioc.mp hn).1.ne']
      rw [hec,OrdinaryConvolution.sum_convolution,mul_sum]
      rw [tsum_eq_sum (s:=Finset.Ioc 0 p.1.1)]
      · apply sum_congr rfl
        intro d hd
        simp only [A,arithmeticTwist_apply]
        ring
      · intro d hd
        have hh : d=0 ∨ p.1.1<d := by
          simpa only [Finset.mem_Ioc,not_and_or,not_lt,not_le,Nat.le_zero] using hd
        rcases hh with rfl | hd
        · simp [A]
        · simp [A,Nat.div_eq_of_lt hd]
    simp_rw [he]
    simpa using hlim
  · have he (p : MovingParameters) : (∑n∈Finset.Icc 1 p.1.1,twist f p.1.2 n)=0 := by
      apply sum_eq_zero
      intro n hn
      simp only [twist,hz n (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1),zero_mul]
    simp_rw [he,mul_zero]
    exact tendsto_const_nhds

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
