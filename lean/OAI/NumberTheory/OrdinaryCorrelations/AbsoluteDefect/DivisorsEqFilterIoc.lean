import Mathlib

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

namespace OrdinaryConvolution

lemma divisors_eq_filter_Ioc {n N : ℕ} (hn : 0<n) (hnN : n≤N) :
    n.divisors=(Finset.Ioc 0 N).filter (fun d => d∣n) := by
  ext d
  simp only [Nat.mem_divisors,mem_filter,Finset.mem_Ioc]
  constructor
  · rintro ⟨hd,hn0⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnN⟩,hd⟩
  · rintro ⟨⟨hd,hdN⟩,hdn⟩
    exact ⟨hdn,hn.ne'⟩

lemma sum_multiples (b : ℕ → ℂ) (N d : ℕ) (hd : 0<d) :
    (∑n∈(Finset.Ioc 0 N).filter (fun n => d∣n),b (n/d))=∑m∈Finset.Ioc 0 (N/d),b m := by
  apply sum_bij (fun n hn => n/d)
  · intro n hn
    rcases mem_filter.mp hn with ⟨hn,hdn⟩
    rcases Finset.mem_Ioc.mp hn with ⟨hn,hnN⟩
    exact Finset.mem_Ioc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hn hdn) hd,Nat.div_le_div_right hnN⟩
  · intro n hn n' hn' he
    have hd1 := (mem_filter.mp hn).2
    have hd2 := (mem_filter.mp hn').2
    calc
      n = (n/d)*d := (Nat.div_mul_cancel hd1).symm
      _ = (n'/d)*d := congrArg (fun k => k*d) he
      _ = n' := Nat.div_mul_cancel hd2
  · intro m hm
    rcases Finset.mem_Ioc.mp hm with ⟨hm,hmN⟩
    refine ⟨d*m,mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hd hm,?_⟩,dvd_mul_right d m⟩,?_⟩
    · have hh := (Nat.le_div_iff_mul_le hd).mp hmN
      simpa only [Nat.mul_comm] using hh
    · exact Nat.mul_div_right m hd
  · intro n hn
    rfl

lemma sum_convolution (a b : ArithmeticFunction ℂ) (N : ℕ) :
    (∑n∈Finset.Ioc 0 N,(a*b) n)=∑d∈Finset.Ioc 0 N,a d*∑m∈Finset.Ioc 0 (N/d),b m := by
  classical
  calc
    _ = ∑n∈Finset.Ioc 0 N, ∑d∈Finset.Ioc 0 N,if d∣n then a d*b (n/d) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun x y => a x*b y),
        divisors_eq_filter_Ioc (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2,sum_filter]
    _ = ∑d∈Finset.Ioc 0 N, ∑n∈Finset.Ioc 0 N,if d∣n then a d*b (n/d) else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [←sum_filter,sum_multiples (fun m => a d*b m) N d (Finset.mem_Ioc.mp hd).1,mul_sum]

lemma sum_norm_le_card (b : ℕ → ℂ) (hb : ∀n, ‖b n‖≤1) (M : ℕ) :
    ‖∑m∈Finset.Ioc 0 M,b m‖≤(M:ℝ) := by
  calc
    _ ≤ ∑m∈Finset.Ioc 0 M,‖b m‖ := norm_sum_le _ _
    _ ≤ ∑m∈Finset.Ioc 0 M,(1:ℝ) := sum_le_sum (fun m hm => hb m)
    _ = _ := by simp

lemma normalized_div_norm (b : ℕ → ℂ) (N d : ℕ) :
    ‖(N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),b m‖≤
      ‖((N/d:ℕ):ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),b m‖/(d:ℝ) := by
  by_cases hm : N/d=0
  · simp [hm]
  have hd : 0<d := by
    by_contra h
    have hd0 : d=0 := by omega
    simp [hd0] at hm
  have hN : 0<N := by
    by_contra h
    have hN0 : N=0 := by omega
    simp [hN0] at hm
  have hMr : (0:ℝ)<(N/d:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hdr : (0:ℝ)<d := by exact_mod_cast hd
  rw [norm_mul,norm_mul,norm_inv,norm_inv,Complex.norm_natCast,Complex.norm_natCast]
  have hdiv : ((N/d:ℕ):ℝ)*(d:ℝ)≤(N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N d
  have hi : (N:ℝ)⁻¹≤(((N/d:ℕ):ℝ))⁻¹/(d:ℝ) := by
    simpa only [one_div,mul_inv,div_eq_mul_inv,one_mul] using
      one_div_le_one_div_of_le (mul_pos hMr hdr) hdiv
  calc
    _ ≤ ((((N/d:ℕ):ℝ))⁻¹/(d:ℝ))*‖∑m∈Finset.Ioc 0 (N/d),b m‖ :=
      mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _ = _ := by ring

lemma normalized_div_bound (b : ℕ → ℂ) (hb : ∀n, ‖b n‖≤1) (N d : ℕ) :
    ‖(N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),b m‖≤1/(d:ℝ) := by
  calc
    _ ≤ ‖((N/d:ℕ):ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),b m‖/(d:ℝ) := normalized_div_norm b N d
    _ ≤ 1/(d:ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
      rw [norm_mul,norm_inv,Complex.norm_natCast]
      calc
        _ ≤ (((N/d:ℕ):ℝ))⁻¹*((N/d:ℕ):ℝ) := mul_le_mul_of_nonneg_left
          (sum_norm_le_card b hb _) (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ ≤ 1 := by
          by_cases hM : N/d=0
          · simp [hM]
          · rw [inv_mul_cancel₀ (by exact_mod_cast hM)]

lemma normalized_div_tendsto (b : ℕ → ℂ)
    (hmean : Tendsto (fun M : ℕ => (M:ℂ)⁻¹*∑m∈Finset.Ioc 0 M,b m) atTop (nhds 0)) (d : ℕ) :
    Tendsto (fun N : ℕ => (N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),b m) atTop (nhds 0) := by
  by_cases hd : d=0
  · simp [hd]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) (fun N => normalized_div_norm b N d)
  have h := (hmean.comp (Nat.tendsto_div_const_atTop hd)).norm.div_const (d:ℝ)
  simpa only [Function.comp_apply,norm_zero,zero_div] using h

theorem mean_convolution {a b : ArithmeticFunction ℂ} (hb : ∀n, ‖b n‖≤1)
    (ha : Summable (fun d : ℕ => ‖a d‖/(d:ℝ)))
    (hmean : Tendsto (fun M : ℕ => (M:ℂ)⁻¹*∑m∈Finset.Ioc 0 M,b m) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (N:ℂ)⁻¹*∑n∈Finset.Ioc 0 N,(a*b) n) atTop (nhds 0) := by
  have he (N : ℕ) : (N:ℂ)⁻¹*∑n∈Finset.Ioc 0 N,(a*b) n=
      ∑'d : ℕ,a d*((N:ℂ)⁻¹*∑m∈Finset.Ioc 0 (N/d),b m) := by
    rw [sum_convolution,mul_sum]
    rw [tsum_eq_sum (s:=Finset.Ioc 0 N)]
    · apply sum_congr rfl
      intro d hd
      ring
    · intro d hd
      have h : d=0 ∨ N<d := by simpa only [Finset.mem_Ioc,not_and_or,not_lt,not_le,Nat.le_zero] using hd
      rcases h with rfl | hd
      · simp
      · simp [Nat.div_eq_of_lt hd]
  simp_rw [he]
  have h := tendsto_tsum_of_dominated_convergence ha
    (g:=fun d : ℕ => (0:ℂ)) (fun d => by simpa using (normalized_div_tendsto b hmean d).const_mul (a d))
    (Filter.Eventually.of_forall (fun N d => ?_))
  · simpa using h
  · rw [norm_mul]
    calc
      _ ≤ ‖a d‖*(1/(d:ℝ)) := mul_le_mul_of_nonneg_left (normalized_div_bound b hb N d) (norm_nonneg _)
      _ = _ := by ring

end OrdinaryConvolution

end

end OAI
