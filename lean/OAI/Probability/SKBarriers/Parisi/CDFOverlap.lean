import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFTiltedStability
import OAI.Probability.SKBarriers.Parisi.CDFSpinRegularity
import OAI.Probability.SKBarriers.Parisi.CDFTerminalStability

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def cdfDistance (α γ : ℝ → ℝ) : ℝ := ∫ z in Icc (0:ℝ) 1, |α z-γ z|

theorem cdfDistance_nonneg (α γ : ℝ → ℝ) : 0 ≤ cdfDistance α γ :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem cdfDistance_integrable {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ) :
    IntegrableOn (fun z => |α z-γ z|) (Icc (0:ℝ) 1) :=
  ((MonotoneOn.integrableOn_isCompact isCompact_Icc (hα.monotoneOn _)).sub
    (MonotoneOn.integrableOn_isCompact isCompact_Icc (hγ.monotoneOn _))).abs

theorem cdfDistance_subinterval_le {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ)
    {s : ℝ} {t : ℝ≥0} (hs : 0 ≤ s) (hst : s+t ≤ 1) :
    (∫ z in s..s+t, |α z-γ z|) ≤ cdfDistance α γ := by
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right t.coe_nonneg),← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_set (cdfDistance_integrable hα hγ) (Eventually.of_forall (fun _ => abs_nonneg _))
  exact Eventually.of_forall (fun _ hx => ⟨hs.trans hx.1,hx.2.trans hst⟩)

def scalarCDFOverlap (β : ℝ) (α : ℝ → ℝ) (q : ℝ) : ℝ :=
  scalarCDFAverage β α 0 (Real.toNNReal q)
    (scalarCDFValue β α q (Real.toNNReal (1-q)))
    (fun z => (scalarCDFGradient β α q (Real.toNNReal (1-q)) z)^2) 0

theorem abs_sq_sub_sq_le_two {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a^2-b^2| ≤ 2*|a-b| := by
  calc
    _ = |a-b| *|a+b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |a-b| *(|a|+|b|) := mul_le_mul_of_nonneg_left (abs_add_le a b) (abs_nonneg _)
    _ ≤ |a-b| *2 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = _ := mul_comm _ _

theorem scalarCDFOverlap_cdf_stability (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (h : ℝ) (hh : 0<h) :
    |scalarCDFOverlap β α q-scalarCDFOverlap β γ q| ≤
      (4*scalarTimeMassConstant β+2*scalarTimeMassConstantK β 3)*cdfDistance α γ/h+
        12*h+2*(Real.exp (2*(scalarTimeMassConstant β*cdfDistance α γ))-1) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal (1-q) (sub_nonneg.mpr hq.2)
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  let fα := scalarCDFValue β α q r
  let fγ := scalarCDFValue β γ q r
  let uα := scalarCDFGradient β α q r
  let uγ := scalarCDFGradient β γ q r
  have HA := scalarCDFGradient_sq_regular β hα hαm q r hr1
  have HG := scalarCDFGradient_sq_regular β hγ hγm q r hr1
  have hind : (∫ z in q..q+r, |α z-γ z|) ≤ cdfDistance α γ :=
    cdfDistance_subinterval_le hαm hγm hq.1 (by rw [hr]; linarith)
  have hfg (z : ℝ) : |fα z-fγ z| ≤ scalarTimeMassConstant β*cdfDistance α γ :=
    (scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm q r hr1 z).trans
      (mul_le_mul_of_nonneg_left hind (scalarTimeMassConstant_nonneg β))
  have hug (z : ℝ) : |uα z-uγ z| ≤ 2*(scalarTimeMassConstant β*cdfDistance α γ)/h+2*h :=
    (scalarCDFGradient_cdf_stability β hα hαm hγ hγm q r hr1 z h hh).trans
      (add_le_add (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hind (scalarTimeMassConstant_nonneg β))
          (by norm_num : (0:ℝ) ≤ 2)) hh.le) le_rfl)
  have hsquare (z : ℝ) : |(uα z)^2-(uγ z)^2| ≤
      2*(2*(scalarTimeMassConstant β*cdfDistance α γ)/h+2*h) :=
    (abs_sq_sub_sq_le_two (scalarCDF_derivative_bounds β hα hαm q r hr1 z).1
      (scalarCDF_derivative_bounds β hγ hγm q r hr1 z).1).trans (mul_le_mul_of_nonneg_left (hug z) (by norm_num))
  have H₁ := scalarCDFAverage_terminal_stability β hα hαm
    (scalarCDFValue_regular β hα hαm q r hr1) (scalarCDFValue_regular β hγ hγm q r hr1)
    (scalarCDFValue_lipschitz β hα hαm q r hr1) (scalarCDFValue_lipschitz β hγ hγm q r hr1)
    HA.1 HG.1 HA.2.1 HG.2.1
    (B:=1) (C:=2) HA.2.2.1 HG.2.2.1 HA.2.2.2 HG.2.2.2
    (mul_nonneg (scalarTimeMassConstant_nonneg β) (cdfDistance_nonneg α γ)) hfg hsquare 0 t ht1 0
  have H₂ := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm
    (scalarCDFValue_regular β hγ hγm q r hr1) HG.1 HG.2.1
    (scalarCDFValue_lipschitz β hγ hγm q r hr1) (B:=1) (C:=2) HG.2.2.1 HG.2.2.2 0 t ht1 0 h hh
  have hprefix : (∫ z in (0:ℝ)..0+t, |α z-γ z|) ≤ cdfDistance α γ :=
    cdfDistance_subinterval_le hαm hγm le_rfl (by simpa only [zero_add,ht] using hq.2)
  norm_num only [NNReal.coe_one,NNReal.coe_ofNat,one_pow,one_add_one_eq_two] at H₁ H₂
  have H₂' : |scalarCDFAverage β α 0 t fγ (fun z => (uγ z)^2) 0-
      scalarCDFAverage β γ 0 t fγ (fun z => (uγ z)^2) 0| ≤
      2*(scalarTimeMassConstantK β 3*cdfDistance α γ)/h+8*h := by
    apply H₂.trans
    have H := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprefix (scalarTimeMassConstantK_nonneg β 3)) (by norm_num : (0:ℝ) ≤ 2)) hh.le
    exact add_le_add H le_rfl
  calc
    _ ≤ |scalarCDFAverage β α 0 t fα (fun z => (uα z)^2) 0-
          scalarCDFAverage β α 0 t fγ (fun z => (uγ z)^2) 0|+
        |scalarCDFAverage β α 0 t fγ (fun z => (uγ z)^2) 0-
          scalarCDFAverage β γ 0 t fγ (fun z => (uγ z)^2) 0| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add H₁ H₂').trans_eq (by ring)

end SK.Analytic

end
end

end OAI
