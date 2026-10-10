import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkThermal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma integral_sqrt_le_sqrt_integral_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Ω→ℝ}
    (hF : Measurable F) (hI : Integrable F P) (h0 : ∀ x, 0≤F x) :
    (∫ x, Real.sqrt (F x) ∂P)≤Real.sqrt (∫ x, F x ∂P) := by
  have hs : (fun x => (Real.sqrt (F x))^2)=F := funext fun x => Real.sq_sqrt (h0 x)
  have hLp : MemLp (fun x => Real.sqrt (F x)) 2 P :=
    (memLp_two_iff_integrable_sq hF.sqrt.aestronglyMeasurable).mpr (by simpa only [hs] using hI)
  have hv := variance_nonneg (fun x => Real.sqrt (F x)) P
  rw [variance_eq_sub hLp] at hv
  simp only [Pi.pow_apply] at hv
  change 0≤(∫ x, (Real.sqrt (F x))^2 ∂P)-(∫ x, Real.sqrt (F x) ∂P)^2 at hv
  rw [hs] at hv
  exact (Real.le_sqrt (integral_nonneg fun x => Real.sqrt_nonneg _) (integral_nonneg h0)).mpr (by linarith)

lemma annealed_centered_energy_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (μ : Measure S) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    {H Y : Ω→S→ℝ} (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    {A B : Ω→ℝ} (hA : ∀ a, 0≤A a) (hB : ∀ a, 0≤B a)
    (hHA : ∀ a x, |H a x|≤A a) (hYB : ∀ a x, |Y a x|≤B a)
    (hB2 : MemLp B 2 P) :
    (∫ a, tiltMean μ (H a) (fun x => |Y a x-∫ b, tiltMean μ (H b) (Y b) 1 ∂P|) 1 ∂P) ≤
      Real.sqrt (∫ a, thermalVar μ (H a) (Y a) 0 ∂P)+
      ∫ a, |tiltMean μ (H a) (Y a) 1-∫ b, tiltMean μ (H b) (Y b) 1 ∂P| ∂P := by
  let M := fun a => tiltMean μ (H a) (Y a) 1
  let E := ∫ a, M a ∂P
  let U := fun a => tiltMean μ (H a) (fun x => |Y a x-M a|) 1
  have hM : Measurable M := measurable_tiltMean_param μ hH hY
  have hU : Measurable U := measurable_tiltMean_param μ hH (hY.sub (hM.comp measurable_fst)).abs
  have hHm (a) : Measurable (H a) := hH.comp (measurable_const.prodMk measurable_id)
  have hYm (a) : Measurable (Y a) := hY.comp (measurable_const.prodMk measurable_id)
  have hMB (a) : |M a|≤B a := tilt_mean_bound μ (hHm a) (hYm a) (hA a) (hB a) (hHA a) (hYB a) 1
  have hBI := hB2.integrable (by norm_num)
  have hUI : Integrable U P := by
    apply (hBI.const_mul 2).mono' hU.aestronglyMeasurable
    exact ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs] using tilt_mean_bound μ (hHm a)
        ((hYm a).sub_const (M a) |>.abs) (hA a) (mul_nonneg (by norm_num) (hB a)) (hHA a)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (by linarith [hYB a x,hMB a])) 1
  have hMI : Integrable (fun a => |M a-E|) P :=
    ((hBI.mono' hM.aestronglyMeasurable (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using hMB a)).sub (integrable_const E)).abs
  have hQI : Integrable (fun a => tiltMean μ (H a) (fun x => |Y a x-E|) 1) P := by
    apply (hBI.add (integrable_const |E|)).mono'
      (measurable_tiltMean_param μ hH
        (show Measurable (Function.uncurry (fun a x => |Y a x-E|)) from (hY.sub_const E).abs)).aestronglyMeasurable
    exact ae_of_all _ fun a => by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using tilt_mean_bound μ (hHm a)
        ((hYm a).sub_const E |>.abs) (hA a) (add_nonneg (hB a) (abs_nonneg E)) (hHA a)
        (fun x => by rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hYB a x) le_rfl)) 1
  have hs : (∫ a, U a ∂P)^2≤∫ a, thermalVar μ (H a) (Y a) 0 ∂P := by
    simpa only [zero_mul,add_zero] using annealed_thermal_abs_sq_le μ P hH hY hA hB hHA hYB hB2 0
  have hu : (∫ a, U a ∂P)≤Real.sqrt (∫ a, thermalVar μ (H a) (Y a) 0 ∂P) :=
    (Real.le_sqrt (integral_nonneg fun a => tiltMean_nonneg μ (fun _ => abs_nonneg _) 1)
      ((sq_nonneg _).trans hs)).mpr hs
  have ht : (∫ a, tiltMean μ (H a) (fun x => |Y a x-E|) 1 ∂P)≤
      (∫ a, U a ∂P)+(∫ a, |M a-E| ∂P) := by
    rw [← integral_add hUI hMI]
    exact integral_mono hQI (hUI.add hMI) fun a =>
      tilt_mean_center_triangle μ (hHm a) (hYm a) (hA a) (hHA a) (hYB a) E (M a)
  exact ht.trans (add_le_add hu le_rfl)

lemma bulkThermalSqrt_intervalIntegrable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) (a b : ℝ) :
    IntervalIntegrable (fun u => Real.sqrt (∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M)) volume a b := by
  have hm := (bulkExpectedThermalVar_measurable n M f v p).sqrt
  have hs (u : ℝ) : (Real.sqrt (∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M))^2=
      ∫ x, bulkThermalVar n M f v p u x ∂bulkDisorderLaw (n+1) M :=
    Real.sq_sqrt (integral_nonneg (bulkThermalVar_nonneg n M f v p u))
  have hi := bulkExpectedThermalVar_intervalIntegrable n M f v p a b
  constructor
  · exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (by simpa only [IntegrableOn,hs] using hi.1)).integrable (by norm_num)
  · exact ((memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr (by simpa only [IntegrableOn,hs] using hi.2)).integrable (by norm_num)

lemma bulkThermalSqrt_integrated_bound (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (p : Fin (n+1)) :
    (∫ u in (1:ℝ)..2, Real.sqrt (∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M))≤
      Real.sqrt 6*bulkCoefficient (n+1) p := by
  let P := volume.restrict (Ioc (1:ℝ) 2)
  have : IsProbabilityMeasure P := ⟨by norm_num [P]⟩
  have hi : Integrable (fun u => ∫ a, bulkThermalVar n M f v p u a ∂bulkDisorderLaw (n+1) M) P :=
    (bulkExpectedThermalVar_intervalIntegrable n M f v p 1 2).1
  have he := integral_sqrt_le_sqrt_integral_probability P
    (bulkExpectedThermalVar_measurable n M f v p) hi
    (fun u => integral_nonneg (bulkThermalVar_nonneg n M f v p u))
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)]
  apply he.trans
  have hb := bulkThermalVar_integrated_bound n M f v p
  rw [intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2)] at hb
  calc
    _ ≤ Real.sqrt (6*bulkCoefficient (n+1) p^2) := Real.sqrt_le_sqrt hb
    _ = _ := by rw [Real.sqrt_mul (by norm_num),Real.sqrt_sq (bulkCoefficient_pos n p).le]

end SphericalPerceptronFreeEnergy
end

end OAI
