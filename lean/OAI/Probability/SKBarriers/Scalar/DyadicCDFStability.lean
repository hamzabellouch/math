import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def dyadicCDFDistance (α γ : ℝ → ℝ) : ℕ → ℝ → ℝ≥0 → ℝ
  | 0,s,t => (t:ℝ)*|α s-γ s|
  | n+1,s,t => dyadicCDFDistance α γ n s (t/2) +
      dyadicCDFDistance α γ n (s+(t:ℝ)/2) (t/2)

theorem dyadicCDFDistance_integral_bound {α γ : ℝ → ℝ}
    (hα : Monotone α) (hγ : Monotone γ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    dyadicCDFDistance α γ n s t ≤ (∫ z in s..s+t, |α z-γ z|) +
      (t:ℝ)/(2:ℝ)^n*((α (s+t)-α s)+(γ (s+t)-γ s)) := by
  have hi (a b : ℝ) : IntervalIntegrable (fun z => |α z-γ z|) volume a b :=
    (hα.intervalIntegrable.sub hγ.intervalIntegrable).abs
  induction n generalizing s t with
  | zero =>
    have hb (z : ℝ) (hz : z ∈ Icc s (s+t)) :
        |α s-γ s| ≤ |α z-γ z|+((α (s+t)-α s)+(γ (s+t)-γ s)) := by
      have H := abs_sub_le (α s) (α z) (γ s)
      have H' := abs_sub_le (α z) (γ z) (γ s)
      rw [abs_of_nonpos (sub_nonpos.mpr (hα hz.1))] at H
      rw [abs_of_nonneg (sub_nonneg.mpr (hγ hz.1))] at H'
      linarith [hα hz.2,hγ hz.2]
    have H := intervalIntegral.integral_mono_on (show s ≤ s+(t:ℝ) by linarith [t.coe_nonneg])
      (intervalIntegrable_const) ((hi s (s+t)).add intervalIntegrable_const) hb
    rw [intervalIntegral.integral_add (hi s (s+t)) intervalIntegrable_const,
      intervalIntegral.integral_const,intervalIntegral.integral_const] at H
    simpa only [dyadicCDFDistance,pow_zero,div_one,add_sub_cancel_left,smul_eq_mul] using H
  | succ n ih =>
    have hc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have he : s+(t:ℝ)/2+(t:ℝ)/2=s+t := by ring
    have H := add_le_add (ih s (t/2)) (ih (s+(t:ℝ)/2) (t/2))
    simp only [hc,he] at H
    rw [dyadicCDFDistance]
    apply H.trans_eq
    have hint := intervalIntegral.integral_add_adjacent_intervals
      (hi s (s+(t:ℝ)/2)) (hi (s+(t:ℝ)/2) (s+t))
    rw [pow_succ]
    calc
      _ = ((∫ z in s..s+(t:ℝ)/2, |α z-γ z|)+
          (∫ z in s+(t:ℝ)/2..s+t, |α z-γ z|))+
          (t:ℝ)/((2:ℝ)^n*2)*((α (s+t)-α s)+(γ (s+t)-γ s)) := by ring
      _ = _ := by rw [hint]

theorem dyadicScalar_cdf_mass_bound {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (hLip : LipschitzWith 1 f) (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |dyadicScalar β α n s t f x-dyadicScalar β γ n s t f x| ≤
      scalarTimeMassConstant β*dyadicCDFDistance α γ n s t := by
  induction n generalizing f s t x with
  | zero =>
    simp only [dyadicScalar_zero,dyadicCDFDistance]
    have H := scalarTimeStep_mass_lipschitz hf hLip β ht (hγ s) (hα s) x
    exact H.trans_eq (by dsimp [scalarTimeMassConstant]; ring)
  | succ n ih =>
    rw [dyadicScalar_succ β α n s t f,dyadicScalar_succ β γ n s t f,dyadicCDFDistance]
    have hhalf : t/2 ≤ 1 := (div_le_self (show (0:ℝ≥0) ≤ t from bot_le) (by norm_num)).trans ht
    let fα := dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f
    let fγ := dyadicScalar β γ n (s+(t:ℝ)/2) (t/2) f
    have hfα : BoundedDerivs fα := dyadicScalar_regular hf β α _ _ _
    have hfγ : BoundedDerivs fγ := dyadicScalar_regular hf β γ _ _ _
    have hlγ : LipschitzWith 1 fγ := dyadicScalar_lipschitz hf hLip β hγ _ _ _
    have H₁ := dyadicScalar_uniform_nonexpansive hfα hfγ β hα n s (t/2)
      (fun z => ih hf hLip (s+(t:ℝ)/2) (t/2) hhalf z) x
    have H₂ := ih hfγ hlγ s (t/2) hhalf x
    calc
      _ ≤ |dyadicScalar β α n s (t/2) fα x-dyadicScalar β α n s (t/2) fγ x|+
          |dyadicScalar β α n s (t/2) fγ x-dyadicScalar β γ n s (t/2) fγ x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ H₂
      _ = _ := by ring

theorem scalarCDFValue_cdf_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFValue β α s t x-scalarCDFValue β γ s t x| ≤
      scalarTimeMassConstant β*(∫ z in s..s+t, |α z-γ z|) := by
  have H (n : ℕ) := (dyadicScalar_cdf_mass_bound scalarSpinTerminal_regular
    scalarSpinTerminal_lipschitz β hα hγ n s t ht x).trans
    (mul_le_mul_of_nonneg_left (dyadicCDFDistance_integral_bound hαm hγm n s t)
      (scalarTimeMassConstant_nonneg β))
  have hv := ((dyadicScalar_value_uniform β hα hαm s t ht).tendsto_at x).sub
    ((dyadicScalar_value_uniform β hγ hγm s t ht).tendsto_at x)
  have hzero : Tendsto (fun n : ℕ => (t:ℝ)/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hr := (((hzero.mul_const ((α (s+t)-α s)+(γ (s+t)-γ s))).const_add
    (∫ z in s..s+t, |α z-γ z|)).const_mul (scalarTimeMassConstant β))
  have Hlim := le_of_tendsto_of_tendsto hv.abs hr (Eventually.of_forall H)
  simpa only [zero_mul,add_zero] using Hlim

end SK.Analytic

end
end

end OAI
