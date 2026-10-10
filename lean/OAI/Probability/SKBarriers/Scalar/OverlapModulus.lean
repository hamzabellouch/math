import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileTransport
import OAI.Probability.SKBarriers.Parisi.CDFOverlapConvergence

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarOverlapModulus_continuous (β h : ℝ) :
    Continuous (fun D : ℝ => scalarOverlapModulus β D h) := by
  unfold scalarOverlapModulus
  fun_prop

theorem scalarOverlapModulus_mono (β : ℝ) {h : ℝ} (hh : 0≤h) :
    Monotone (fun D : ℝ => scalarOverlapModulus β D h) := by
  intro D E hDE
  unfold scalarOverlapModulus
  have hc : 0≤4*scalarTimeMassConstant β+2*scalarTimeMassConstantK β 3 :=
    add_nonneg (mul_nonneg (by norm_num) (scalarTimeMassConstant_nonneg β))
      (mul_nonneg (by norm_num) (scalarTimeMassConstantK_nonneg β 3))
  apply add_le_add
  · exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDE hc) hh) le_rfl
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDE (scalarTimeMassConstant_nonneg β)) (by norm_num)

theorem scalarOverlapModulus_nonneg (β : ℝ) {D h : ℝ} (hD : 0≤D) (hh : 0≤h) :
    0 ≤ scalarOverlapModulus β D h := by
  have H := scalarOverlapModulus_mono β hh hD
  simp only [scalarOverlapModulus,mul_zero,zero_div,Real.exp_zero,sub_self,add_zero,zero_add] at H
  exact (mul_nonneg (by norm_num : (0:ℝ)≤12) hh).trans H

theorem quantileCDF_segment_distance {k : ℕ} (A B : Fin (k+1) → ℝ)
    (hA : A∈admissibleQuantiles k) (hB : B∈admissibleQuantiles k)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hQ : (1-t) • A+t • B∈admissibleQuantiles k) :
    cdfDistance (quantileCDF k ((1-t) • A+t • B)) (quantileCDF k A)=
      t*cdfDistance (quantileCDF k B) (quantileCDF k A) := by
  rw [cdfDistance,cdfDistance,quantileCDF_L1_eq _ _ hQ hA,quantileCDF_L1_eq _ _ hB hA,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : ((1-t) • A+t • B) j-A j=t*(B j-A j) := by
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; ring
  rw [he,abs_mul,abs_of_nonneg ht.1]
  ring

def cdfGradientTest (β : ℝ) (α : ℝ → ℝ) (s : ℝ) : ℝ :=
  s-scalarCDFOverlap β α (projIcc 0 1 (by norm_num) s)

theorem cdfGradientTest_continuous {β : ℝ} {α : ℝ → ℝ}
    (hΓ : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    Continuous (cdfGradientTest β α) :=
  continuous_id.sub ((continuousOn_iff_continuous_domRestrict.mp hΓ).comp continuous_projIcc)

theorem cdfGradientTest_eq {β : ℝ} {α : ℝ → ℝ} {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    cdfGradientTest β α s=s-scalarCDFOverlap β α s := by
  simp only [cdfGradientTest,projIcc_of_mem _ hs]

end SK.Analytic

end
end

end OAI
