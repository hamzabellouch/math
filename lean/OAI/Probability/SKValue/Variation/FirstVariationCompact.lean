import Mathlib
import OAI.Probability.SKValue.Evolution.IntegralPrimitiveTerminal
import OAI.Probability.SKValue.Processes.CrossValueBound
import OAI.Probability.SKValue.Variation.OrderVariations

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma IsMinimizer.compact_variation_inequality {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    (η : OrderParameter) {T : ℝ} (hT : 0<T) (hT1 : T<1) :
    (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤
      (3/2 : ℝ)*(∫ t in T..1,|η.cutoff t-γ.cutoff t|)+
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..T,(η.coeff t-γ.coeff t)*gradientMoment W γ X t) := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  let A := ∫ t in (0 : ℝ)..1,|η.cutoff t-γ.cutoff t|
  let C := η.coeff T+γ.coeff T
  let R (h : ℝ) := T*(h^2*C+γ.coeff T*(h*(Lu+3*A)))*Real.exp (T*γ.coeff T*Lu)
  let B := (3/2 : ℝ)*(∫ t in T..1,|η.cutoff t-γ.cutoff t|)+
    (1/2 : ℝ)*(∫ t in (0 : ℝ)..T,(η.coeff t-γ.coeff t)*gradientMoment W γ X t)
  have hA : 0≤A := intervalIntegral.integral_nonneg (by norm_num) (fun t ht ↦ abs_nonneg _)
  have hC : 0≤C := add_nonneg (η.nonneg T ⟨hT.le,hT1⟩) (γ.nonneg T ⟨hT.le,hT1⟩)
  have hAi : IntervalIntegrable (fun t ↦ |η.cutoff t-γ.cutoff t|) volume 0 1 :=
    (η.cutoff_integrable.sub γ.cutoff_integrable).norm.intervalIntegrable
  have htA (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      (∫ s in t..1,|η.cutoff s-γ.cutoff s|)≤A := by
    exact intervalIntegral.integral_mono_interval ht.1 (ht.2.trans hT1.le) le_rfl
      (Eventually.of_forall (fun s ↦ abs_nonneg _)) hAi
  have hul (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x y : ℝ) :
      |gradient W γ t x-gradient W γ t y|≤Lu*|x-y| := by
    simpa only [sub_self,abs_zero,zero_add] using hu t ht t ht x y
  have hh (h : ℝ) (hh0 : 0<h) (hh1 : h≤1) :
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤B+T*C*Lv*R h := by
    have hε : h^2∈Icc (0 : ℝ) 1 := ⟨sq_nonneg _,(sq_le_one_iff_abs_le_one _).mpr (by rw [abs_of_pos hh0]; exact hh1)⟩
    let β := γ.mix η (h^2) hε
    have hph (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |phi W β t x-phi W γ t x|≤(3/2 : ℝ)*h^2*A := by
      have hb := phi_difference_bound W γ β ⟨ht.1,ht.2.trans hT1.le⟩ x
      rw [γ.mix_difference_integral η hε] at hb
      exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left (htA t ht) (sq_nonneg h)])
    have hgs (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |gradient W β t x-gradient W γ t x|≤h*(Lu+3*A) := by
      have hb := phi_gradient_difference_bound W γ β ⟨hT.le,hT1⟩ hul hph hh0 ht x
      have heq : Lu*h+2*((3/2 : ℝ)*h^2*A)/h=h*(Lu+3*A) := by field_simp
      rwa [heq] at hb
    have hv := hX.cross_value_bound β hT hT1 hV hLu
      (mul_nonneg (sq_nonneg h) hC) (mul_nonneg hh0.le (by positivity : 0≤Lu+3*A))
      (fun t ht ↦ γ.mix_strip_difference_bound η hε ⟨hT.le,hT1⟩ ht) hul hgs
    rw [γ.mix_difference_integral η hε,hX.mix_moment_integral η hε ⟨hT.le,hT1.le⟩] at hv
    have hm := hγ.mix_value_inequality η hε
    have hv' : (h^2/2)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))≤
        h^2*(B+T*C*Lv*R h) := by
      calc
        _≤phi W β 0 0-phi W γ 0 0 := hm
        _≤_ := hv
        _=h^2*(B+T*C*Lv*R h) := by dsimp only [B,R,C] at *; ring
    have heq : (h^2/2)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))=
        h^2*((1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t))) := by ring
    rw [heq] at hv'
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hh0)).mp hv'
  have hzero : Tendsto (fun h : ℝ ↦ h) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hRlim : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [R,zero_pow (by norm_num : (2 : ℕ)≠0),zero_mul,mul_zero,add_zero] using
      (((hzero.pow 2).mul_const C).add ((hzero.mul_const (Lu+3*A)).const_mul (γ.coeff T))).const_mul T |>.mul_const (Real.exp (T*γ.coeff T*Lu))
  have hlim := (hRlim.const_mul (T*C*Lv)).const_add B
  have hb := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ)<1)] with h hhs
    exact hh h hhs.1 hhs.2.le)
  simpa only [mul_zero,add_zero,B] using hb

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma tail_integral_tendsto_zero {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    Tendsto (fun T ↦ ∫ t in T..1,f t) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hlim := (integral_primitive_terminal hf).const_sub (∫ t in (0 : ℝ)..1,f t)
  have hlim' : Tendsto (fun T ↦ (∫ t in (0 : ℝ)..1,f t)-(∫ t in (0 : ℝ)..T,f t))
      (𝓝[<] (1 : ℝ)) (𝓝 0) := by simpa only [sub_self] using hlim
  apply hlim'.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
  have hi : IntervalIntegrable f volume 0 T := hf.mono_set (by simpa only [uIcc_of_le hT.1.le,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using Icc_subset_Icc le_rfl hT.2.le)
  have hi' : IntervalIntegrable f volume T 1 := hf.mono_set (by simpa only [uIcc_of_le hT.2.le,uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using Icc_subset_Icc hT.1.le le_rfl)
  linarith [intervalIntegral.integral_add_adjacent_intervals hi hi']

lemma IsMinimizer.variation_inequality {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hγ : IsMinimizer W γ) (hX : IsDiffusion W γ X)
    (η : OrderParameter) :
    0≤∫ t in (0 : ℝ)..1,(η.coeff t-γ.coeff t)*(gradientMoment W γ X t-t) := by
  have hAi : IntervalIntegrable (fun t ↦ |η.cutoff t-γ.cutoff t|) volume 0 1 :=
    (η.cutoff_integrable.sub γ.cutoff_integrable).norm.intervalIntegrable
  have hqi : IntervalIntegrable (fun t ↦ (η.coeff t-γ.coeff t)*gradientMoment W γ X t) volume 0 1 := by
    simpa only [sub_mul] using (hX.weightedMoment_integrable η).sub (hX.weightedMoment_integrable γ)
  have hti : IntervalIntegrable (fun t ↦ t*(η.coeff t-γ.coeff t)) volume 0 1 := by
    simpa only [mul_sub] using η.weighted_intervalIntegrable.sub γ.weighted_intervalIntegrable
  have hlim := ((tail_integral_tendsto_zero hAi).const_mul (3/2 : ℝ)).add
    ((integral_primitive_terminal hqi).const_mul (1/2 : ℝ))
  have hh := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with T hT
    exact hγ.compact_variation_inequality hX η hT.1 hT.2)
  have heq : (∫ t in (0 : ℝ)..1,(η.coeff t-γ.coeff t)*(gradientMoment W γ X t-t))=
      (∫ t in (0 : ℝ)..1,(η.coeff t-γ.coeff t)*gradientMoment W γ X t)-
        (∫ t in (0 : ℝ)..1,t*(η.coeff t-γ.coeff t)) := by
    rw [←intervalIntegral.integral_sub hqi hti]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [heq]
  linarith

end SKValue

end

end OAI
