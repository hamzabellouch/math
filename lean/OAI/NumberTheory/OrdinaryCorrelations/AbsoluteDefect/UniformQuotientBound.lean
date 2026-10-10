import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DivisorsEqFilterIoc
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ArithmeticTwist
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrincipalDivergence
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingParameters
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelWeightFactor

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

namespace OrdinaryCorrelations.UniformFamilyHalasz
open Completion PretentiousEuler OrdinaryArchimedeanTwist Finset Filter

lemma uniform_quotient_bound {ι : Type*} {F : ι → ℕ → ℂ}
    (hf : ∀i, OneBounded (F i)) (hD : PrincipalDivergence F)
    {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀i τ, |τ|≤(N:ℝ)/2 →
      ‖(N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),twist (complete (F i)) τ m‖≤ε/(d:ℝ) := by
  have hq : Tendsto (fun N : ℕ => N/d) atTop atTop := Nat.tendsto_div_const_atTop hd.ne'
  filter_upwards [hq.eventually (moving_square_complete_partial_small hf hD ε hε),
    eventually_ge_atTop (4*d*d),hq.eventually (eventually_ge_atTop (1:ℕ))] with N hs hN hM
  intro i τ hτ
  have hdom : (N:ℝ)≤((N/d:ℕ):ℝ)^2 := by exact_mod_cast quotient_square_dominates d N hd hN
  have heq : Finset.Icc 1 (N/d)=Finset.Ioc 0 (N/d) := by
    ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
  have hh := hs i τ (show |τ|≤((N/d:ℕ):ℝ)^2/2 by linarith)
  rw [heq] at hh
  exact (OrdinaryConvolution.normalized_div_norm _ N d).trans
    (div_le_div_of_nonneg_right (normalized_sum_small _ (by omega) _ ε hh) (Nat.cast_nonneg d))

lemma uniform_multiplicative_bound {ι : Type*} {F : ι → ℕ → ℂ}
    (hf : ∀i, OneBounded (F i)) (hm : ∀i, Multiplicative (F i)) (h1 : ∀i,F i 1=1)
    (hD : PrincipalDivergence F) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀i τ, |τ|≤(N:ℝ)/2 →
      ‖(N:ℂ)⁻¹*∑n∈Finset.Icc 1 N,twist (F i) τ n‖≤ε := by
  classical
  let K := kernelConstant 1+1
  have hK0 : 0<kernelConstant 1 := Real.exp_pos _
  have hK : 0<K := by dsimp [K]; linarith
  let η := ε/(2*K)
  have hη : 0<η := div_pos hε (mul_pos (by norm_num) hK)
  have hlim : Tendsto (fun D : ℕ => (D:ℝ)^(-(1/4:ℝ))*kernelConstant (3/4)) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp
      tendsto_natCast_atTop_atTop).mul_const (kernelConstant (3/4))
  obtain ⟨D,hDt,hD1⟩ := ((hlim.eventually (eventually_lt_nhds (show 0<ε/2 by positivity))).and
    (eventually_ge_atTop (1:ℕ))).exists
  have hsmall : ∀ᶠ N : ℕ in atTop, ∀d∈Finset.Icc 1 D, ∀i τ, |τ|≤(N:ℝ)/2 →
      ‖(N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),twist (complete (F i)) τ m‖≤η/(d:ℝ) := by
    rw [eventually_all_finset]
    intro d hd
    exact uniform_quotient_bound hf hD (by have hh := (Finset.mem_Icc.mp hd).1; omega) hη
  filter_upwards [hsmall] with N hsmall
  intro i τ hτ
  let A := fun d : ℕ => twist (kernel (F i)) τ d*
      ((N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),twist (complete (F i)) τ m)
  have he : (N:ℂ)⁻¹*∑n∈Finset.Icc 1 N,twist (F i) τ n=∑d∈Finset.Ioc 0 N,A d := by
    have heq : Finset.Icc 1 N=Finset.Ioc 0 N := by
      ext n; simp only [Finset.mem_Icc,Finset.mem_Ioc]; omega
    rw [heq]
    have hec : (∑n∈Finset.Ioc 0 N,twist (F i) τ n)=
        ∑n∈Finset.Ioc 0 N,(arithmeticTwist (kernel (F i)) τ*arithmeticTwist (complete (F i)) τ) n := by
      rw [←arithmeticTwist_mul,kernel_reconstruct]
      apply sum_congr rfl
      intro n hn
      simp only [arithmeticTwist_apply,twist,arithmetic_apply_pos (F i) (Finset.mem_Ioc.mp hn).1.ne']
    rw [hec,OrdinaryConvolution.sum_convolution,mul_sum]
    apply sum_congr rfl
    intro d hd
    simp only [A,arithmeticTwist_apply]
    ring
  have hlow : (∑d∈(Finset.Ioc 0 N).filter (fun d => d≤D),‖A d‖)≤η*kernelConstant 1 := by
    calc
      _ ≤ ∑d∈(Finset.Ioc 0 N).filter (fun d => d≤D),η*(‖kernel (F i) d‖/(d:ℝ)) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hdN,hdD⟩ := mem_filter.mp hd
        have hd0 := (Finset.mem_Ioc.mp hdN).1
        have hh := mul_le_mul_of_nonneg_left (hsmall d (Finset.mem_Icc.mpr ⟨by omega,hdD⟩) i τ hτ)
          (norm_nonneg (kernel (F i) d))
        simpa only [A,norm_mul,norm_twist,div_eq_mul_inv,mul_left_comm,mul_assoc] using hh
      _ = η*∑d∈(Finset.Ioc 0 N).filter (fun d => d≤D),kernelWeight (F i) 1 d := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d hd
        simp [kernelWeight,Real.rpow_neg_one,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (kernelWeight_sum_le (hf i) (hm i) (h1 i) (by norm_num : (1:ℝ)/2<1) _) hη.le
  have htail : (∑d∈(Finset.Ioc 0 N).filter (fun d => ¬d≤D),‖A d‖)≤
      (D:ℝ)^(-(1/4:ℝ))*kernelConstant (3/4) := by
    have hp : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
    have hfe : (Finset.Ioc 0 N).filter (fun d => ¬d≤D)=
        (Finset.Ioc 0 N).filter (fun (d:ℕ) => (D:ℝ)<(d:ℝ)) := by
      ext d
      simp only [Finset.mem_filter,not_le,Nat.cast_lt]
    rw [hfe]
    refine le_trans (sum_le_sum ?_) (kernelTail_quarter (hf i) (hm i) (h1 i) hp _)
    intro d hd
    have hh := mul_le_mul_of_nonneg_left (OrdinaryConvolution.normalized_div_bound
      (twist (complete (F i)) τ) (fun n => by simpa only [norm_twist] using complete_oneBounded (hf i) n) N d)
      (norm_nonneg (kernel (F i) d))
    simpa only [A,norm_mul,norm_twist,one_div,div_eq_mul_inv,one_mul] using hh
  have hηK : η*kernelConstant 1≤ε/2 := by
    have hid : η*(2*K)=ε := div_mul_cancel₀ ε (by positivity)
    have hh : kernelConstant 1≤K := by dsimp [K]; linarith
    nlinarith
  rw [he]
  refine (norm_sum_le _ _).trans ?_
  rw [←sum_filter_add_sum_filter_not (Finset.Ioc 0 N) (fun d => d≤D) (fun d => ‖A d‖)]
  linarith

end OrdinaryCorrelations.UniformFamilyHalasz

end

end OAI
