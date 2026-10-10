import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition
import Mathlib.Analysis.MellinTransform

namespace OAI

/-! The compact correction between the smooth main-term cutoff and the
sharp cutoff at one. Its Mellin transform is entire; the sharp part has
the exact simple-pole transform. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPoleCorrection (x : ℝ) : ℂ :=
  ((x^(5/6:ℝ):ℝ):ℂ)*(normPartitionStep x:ℂ)-
    (Ioi (1:ℝ)).indicator (fun x => ((x^(5/6:ℝ):ℝ):ℂ)) x

lemma metaplecticPoleCorrection_local : LocallyIntegrable metaplecticPoleCorrection := by
  have hp : Continuous (fun x : ℝ => ((x^(5/6:ℝ):ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))
  have hs : Continuous (fun x : ℝ => (normPartitionStep x:ℂ)) := by
    unfold normPartitionStep
    fun_prop
  exact (hp.mul hs).locallyIntegrable.sub (hp.locallyIntegrable.indicator measurableSet_Ioi)

lemma metaplecticPoleCorrection_zero_low {x : ℝ} (hx : x ≤ 1) :
    metaplecticPoleCorrection x = 0 := by
  simp only [metaplecticPoleCorrection,normPartitionStep_zero hx,Complex.ofReal_zero,mul_zero]
  rw [indicator_of_notMem (show x ∉ Ioi (1:ℝ) from not_lt.mpr hx),sub_zero]

lemma metaplecticPoleCorrection_zero_high {x : ℝ} (hx : 4/3 ≤ x) :
    metaplecticPoleCorrection x = 0 := by
  simp only [metaplecticPoleCorrection,normPartitionStep_one hx,Complex.ofReal_one,mul_one]
  rw [indicator_of_mem (show x ∈ Ioi (1:ℝ) by change 1 < x; linarith),sub_self]

lemma metaplecticPoleCorrection_mellin_entire : Differentiable ℂ (mellin metaplecticPoleCorrection) := by
  have ht : metaplecticPoleCorrection =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (4/3:ℝ)] with x hx
    exact metaplecticPoleCorrection_zero_high hx
  have hb : metaplecticPoleCorrection =ᶠ[𝓝[>] (0:ℝ)] 0 := by
    filter_upwards [(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with x hx
    exact metaplecticPoleCorrection_zero_low hx.le
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow
    (metaplecticPoleCorrection_local.locallyIntegrableOn _)
    ((isBigO_zero (fun x : ℝ => x^(-(s.re+1))) atTop).congr' ht.symm Filter.EventuallyEq.rfl)
    (by linarith)
    ((isBigO_zero (fun x : ℝ => x^(-(s.re-1))) (𝓝[>] (0:ℝ))).congr' hb.symm Filter.EventuallyEq.rfl)
    (by linarith)

lemma metaplecticPoleCorrection_mellin_convergent (s : ℂ) :
    MellinConvergent metaplecticPoleCorrection s := by
  have ht : metaplecticPoleCorrection =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop (4/3:ℝ)] with x hx
    exact metaplecticPoleCorrection_zero_high hx
  have hb : metaplecticPoleCorrection =ᶠ[𝓝[>] (0:ℝ)] 0 := by
    filter_upwards [(eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with x hx
    exact metaplecticPoleCorrection_zero_low hx.le
  exact mellinConvergent_of_isBigO_rpow
    (metaplecticPoleCorrection_local.locallyIntegrableOn _)
    ((isBigO_zero (fun x : ℝ => x^(-(s.re+1))) atTop).congr' ht.symm Filter.EventuallyEq.rfl)
    (by linarith)
    ((isBigO_zero (fun x : ℝ => x^(-(s.re-1))) (𝓝[>] (0:ℝ))).congr' hb.symm Filter.EventuallyEq.rfl)
    (by linarith)

lemma metaplecticSharpPole_integrand (s : ℂ) (x : ℝ) :
    (x:ℂ)^(-s-1)*(Ioi (1:ℝ)).indicator (fun x => ((x^(5/6:ℝ):ℝ):ℂ)) x =
      (Ioi (1:ℝ)).indicator (fun x => (x:ℂ)^(5/6-s-1)) x := by
  by_cases hx : x ∈ Ioi (1:ℝ)
  · simp only [indicator_of_mem hx]
    rw [Complex.ofReal_cpow (by change 1 < x at hx; linarith),
      ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (by change 1 < x at hx; linarith))]
    congr 1
    push_cast
    ring
  · simp only [indicator_of_notMem hx,mul_zero]

lemma metaplecticSharpPole_mellin {s : ℂ} (hs : (5/6:ℝ) < s.re) :
    mellin ((Ioi (1:ℝ)).indicator (fun x => ((x^(5/6:ℝ):ℝ):ℂ))) (-s) =
      1/(s-5/6) := by
  have he := metaplecticSharpPole_integrand s
  simp only [mellin,smul_eq_mul,he]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hint : Ioi (1:ℝ) ∩ Ioi 0 = Ioi 1 := by ext x; simp
  rw [hint,integral_Ioi_cpow_of_lt (by simp; linarith : (5/6-s-1:ℂ).re < -1)
    (by norm_num : (0:ℝ) < 1)]
  simp only [Complex.ofReal_one,Complex.one_cpow]
  have heq : (5/6-s-1+1:ℂ) = -(s-5/6) := by ring
  rw [heq,div_neg,neg_div,neg_neg]


lemma metaplecticSharpPole_mellin_convergent {s : ℂ} (hs : (5/6:ℝ) < s.re) :
    MellinConvergent ((Ioi (1:ℝ)).indicator (fun x => ((x^(5/6:ℝ):ℝ):ℂ))) (-s) := by
  unfold MellinConvergent
  simp only [smul_eq_mul,metaplecticSharpPole_integrand]
  rw [IntegrableOn,integrable_indicator_iff measurableSet_Ioi,IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioi]
  have hint : Ioi (1:ℝ) ∩ Ioi 0 = Ioi 1 := by ext x; simp
  rw [hint]
  exact integrableOn_Ioi_cpow_of_lt (by simp; linarith) (by norm_num)

end CubicFirstMoment

end

end OAI
