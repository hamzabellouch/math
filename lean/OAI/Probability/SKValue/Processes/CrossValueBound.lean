import Mathlib
import OAI.Probability.SKValue.Processes.CrossMeshComparison
import OAI.Probability.SKValue.Variation.WeightedMoments

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma ordinaryMeshSource_eq (W : BrownianSpace) (γ β : OrderParameter) (T : ℝ) (N : ℕ) :
    ordinaryMeshSource T N γ.coeff β.coeff (phi W γ)=
      weightedEulerMoment W γ β T N-weightedEulerMoment W γ γ T N := by
  have he : gradient W γ=(fun t ↦ deriv (phi W γ t)) := rfl
  simp only [ordinaryMeshSource,weightedEulerMoment,he,←mul_sub,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma IsDiffusion.cross_value_bound {W : BrownianSpace} {γ : OrderParameter}
    {X : ℝ → W.Ω → ℝ} (hX : IsDiffusion W γ X) (β : OrderParameter)
    {T Kv Lv Lu d e : ℝ} (hT : 0<T) (hT1 : T<1)
    (hV : ValueStrip T γ.coeff (phi W γ) Kv Lv)
    (hLu : 0≤Lu) (hd : 0≤d) (he : 0≤e)
    (hc : ∀ t∈Icc (0 : ℝ) T,|(β.coeff t)-(γ.coeff t)|≤d)
    (hu : ∀ t∈Icc (0 : ℝ) T,∀ x y,|gradient W γ t x-gradient W γ t y|≤Lu*|x-y|)
    (hs : ∀ t∈Icc (0 : ℝ) T,∀ x,|gradient W β t x-gradient W γ t x|≤e) :
    phi W β 0 0-phi W γ 0 0≤
      (3/2 : ℝ)*(∫ t in T..1,|β.cutoff t-γ.cutoff t|)+
      ((∫ t in (0 : ℝ)..T,β.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ))-
       (∫ t in (0 : ℝ)..T,γ.coeff t*(∫ ω,(1/2 : ℝ)*(gradient W γ t (X t ω))^2 ∂W.μ)))+
      T*d*Lv*(T*(d+γ.coeff T*e)*Real.exp (T*γ.coeff T*Lu)) := by
  obtain ⟨Kv',Lv',K',L',D',Lu',La',hU,rest⟩ := sourceStripRegularity W β T ⟨hT.le,hT1⟩
  let G := max (γ.coeff T) (β.coeff T)
  let R := T*(d+γ.coeff T*e)*Real.exp (T*γ.coeff T*Lu)
  let B := (3/2 : ℝ)*(∫ t in T..1,|β.cutoff t-γ.cutoff t|)
  let err (N : ℕ) :=
    T*Real.sqrt (stepSize T N)*(cubicEnvelopeMean G Kv ((1/2+G)*Lv)+
      cubicEnvelopeMean G Kv' ((1/2+G)*Lv'))+
      stepSize T N*Kv*(γ.coeff T-γ.coeff 0)+stepSize T N*Kv'*(β.coeff T-β.coeff 0)
  have hγT : 0≤γ.coeff T := γ.nonneg T ⟨hT.le,hT1⟩
  have hR : 0≤R := by dsimp [R]; positivity
  have heN (N : ℕ) (hN : 0<N) : phi W β 0 0-phi W γ 0 0≤
      B+(weightedEulerMoment W γ β T N-weightedEulerMoment W γ γ T N)+T*d*Lv*R+err N := by
    have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
    have hfb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |crossFeedback (phi W γ) (phi W β) t x|≤1 :=
      crossFeedback_bound (hV.bounded t ht x) (hU.bounded t ht x)
    have hfs (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
        |crossFeedback (phi W γ) (phi W β) t x-gradient W γ t x|≤e := by
      have hh := hs t ht x
      have hh' : |crossFeedback (phi W γ) (phi W β) t x-gradient W γ t x|=
          |gradient W β t x-gradient W γ t x|/2 := by
        dsimp only [crossFeedback,gradient]
        rw [show (deriv (phi W β t) x+deriv (phi W γ t) x)/2-deriv (phi W γ t) x=
          (deriv (phi W β t) x-deriv (phi W γ t) x)/2 by ring,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      rw [hh']
      linarith
    have hY (z : Fin (N+1) → ℝ) (j : ℕ) (hj : j≤N) :
        |euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z j-
          euler T N γ.coeff (gradient W γ) z j|≤R := by
      apply euler_same_noise_bound hT.le hN hγT hLu hd he
      · intro k hk
        rw [abs_of_nonneg (γ.nonneg _ ⟨(htime k hk.le).1,(htime k hk.le).2.trans_lt hT1⟩)]
        exact γ.monotone ⟨(htime k hk.le).1,(htime k hk.le).2.trans_lt hT1⟩ ⟨hT.le,hT1⟩ (htime k hk.le).2
      · intro k hk; exact hc _ (htime k hk.le)
      · intro k hk; exact hfb _ (htime k hk.le)
      · intro k hk; exact hfs _ (htime k hk.le)
      · intro k hk; exact hu _ (htime k hk.le)
      · exact hj
    have htelescope := cross_value_mesh_expectation hV hU hT hT1.le
      (le_max_left _ _ : γ.coeff T≤G) (le_max_right _ _ : β.coeff T≤G) hN
    have hcompare := crossMeshSource_difference_bound hV hU hT.le hN hd hR hc hY
    rw [ordinaryMeshSource_eq] at hcompare
    have hterminal : (∫ z,phi W β T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N)-
        phi W γ T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N)
        ∂gaussianProduct (Fin (N+1)))≤B := by
      apply (le_abs_self _).trans
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
        (norm_integral_le_of_norm_le_const (μ := gaussianProduct (Fin (N+1))) (C := B)
          (f := fun z ↦ phi W β T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N)-
            phi W γ T (euler T N β.coeff (crossFeedback (phi W γ) (phi W β)) z N))
          (Eventually.of_forall (fun z ↦ phi_difference_bound W γ β ⟨hT.le,hT1.le⟩ _)))
    have htlow := (abs_le.mp htelescope).1
    have hcup := (abs_le.mp hcompare).2
    dsimp only [err]
    linarith
  have hδ : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) := tendsto_const_div_atTop_nhds_zero_nat T
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hδ
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err,Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,zero_add] using
      (((hsqrt.const_mul T).mul_const (cubicEnvelopeMean G Kv ((1/2+G)*Lv)+
        cubicEnvelopeMean G Kv' ((1/2+G)*Lv'))).add
        ((hδ.mul_const Kv).mul_const (γ.coeff T-γ.coeff 0))).add
        ((hδ.mul_const Kv').mul_const (β.coeff T-β.coeff 0))
  have hlim := (((((hX.weightedEulerMoment_tendsto β hT hT1).sub
    (hX.weightedEulerMoment_tendsto γ hT hT1)).const_add B).add_const (T*d*Lv*R)).add herr)
  have hh := ge_of_tendsto hlim (by filter_upwards [eventually_gt_atTop 0] with N hN using heN N hN)
  simpa only [add_zero,B,R] using hh

end SKValue

end

end OAI
