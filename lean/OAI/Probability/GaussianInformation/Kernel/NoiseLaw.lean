import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Reweighting

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open Projection.Support Projection Reweight

noncomputable def noiseLaw (k : ℕ) (η : ℝ) : Measure (Fin k → ℝ) :=
  volume.withDensity (boxKernel η 0)

lemma measurable_noise_density {k : ℕ} (η : ℝ) : Measurable (boxKernel (k := k) η 0) :=
  (measurable_boxKernel η).comp (measurable_const.prodMk measurable_id)

lemma noise_probability (k : ℕ) {η : ℝ} (hη : 0 < η) : IsProbabilityMeasure (noiseLaw k η) := by
  constructor
  rw [noiseLaw,withDensity_apply _ MeasurableSet.univ]
  simpa using lintegral_boxKernel (k := k) η hη 0

lemma noise_support (k : ℕ) (η : ℝ) : ∀ᵐ e ∂noiseLaw k η, e ∈ closedBox 0 η := by
  rw [noiseLaw,ae_withDensity_iff (measurable_noise_density η)]
  filter_upwards [] with e
  intro he
  exact boxKernel_ne_zero_mem he

lemma boxScale_pos (k : ℕ) {η : ℝ} (_hη : 0 < η) : 0 < boxScale k η := by
  unfold boxScale
  exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top

lemma boxScale_ne_top (k : ℕ) {η : ℝ} (hη : 0 < η) : boxScale k η ≠ ∞ := by
  unfold boxScale
  exact ENNReal.inv_ne_top.mpr (by positivity)

lemma boxScale_dilate (k : ℕ) {η : ℝ} (hη : 0 < η) :
    boxScale k η = ENNReal.ofReal ((2:ℝ)^k)*boxScale k (2*η) := by
  have he : ENNReal.ofReal ((2*(2*η))^k) =
      ENNReal.ofReal ((2:ℝ)^k)*ENNReal.ofReal ((2*η)^k) := by
    rw [← ENNReal.ofReal_mul' (pow_nonneg (mul_nonneg (by norm_num) hη.le) k)]
    congr 1
    rw [← mul_pow]
  unfold boxScale
  rw [he,ENNReal.mul_inv,← mul_assoc,
    ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,one_mul]
  · exact Or.inl (by positivity)
  · exact Or.inl ENNReal.ofReal_ne_top

lemma shifted_box_le {k : ℕ} {η : ℝ} (hη : 0 < η) (a b e : Fin k → ℝ)
    (he : e ∈ closedBox 0 η) :
    boxKernel η a (b+e) ≤ ENNReal.ofReal ((2:ℝ)^k)*boxKernel (2*η) (a-b) 0 := by
  by_cases hab : b+e ∈ closedBox a η
  · have hd : (0 : Fin k → ℝ) ∈ closedBox (a-b) (2*η) := by
      intro i
      have ha := hab i
      have hb := he i
      simp only [Pi.add_apply,Pi.sub_apply,Pi.zero_apply,sub_zero] at ha hb ⊢
      have hx := abs_add_le (b i+e i-a i) (-e i)
      have hid : b i+e i-a i+-e i=b i-a i := by ring
      rw [hid,abs_neg] at hx
      rw [show (0:ℝ)-(a i-b i)=b i-a i by ring]
      linarith
    rw [boxKernel,Set.indicator_of_mem hab,boxKernel,Set.indicator_of_mem hd]
    exact (boxScale_dilate k hη).le
  · rw [boxKernel,Set.indicator_of_notMem hab]
    exact bot_le

noncomputable def projectedReference {k d : ℕ} (ν : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) (y z : Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ u,boxKernel η (projectVector X u) y*boxKernel η (projectVector Z u) z ∂rho ν

lemma projectedReference_measurable {k d : ℕ} (ν : Measure (Ambient d)) [SFinite (rho ν)]
    (η : ℝ) : Measurable (fun t : ((Fin k → Fin d → ℝ) × (Fin k → Fin d → ℝ)) ×
      ((Fin k → ℝ) × (Fin k → ℝ)) => projectedReference ν η t.1.1 t.1.2 t.2.1 t.2.2) := by
  unfold projectedReference
  apply Measurable.lintegral_prod_right
  have hA := measurable_boxKernel (k := k) η
  have hP := continuous_projectVector (k := k) (d := d)
  fun_prop

lemma projectedReference_le {k d : ℕ} (ν : Measure (Ambient d)) (η : ℝ)
    (X Z : Fin k → Fin d → ℝ) (y z : Fin k → ℝ) :
    projectedReference ν η X Z y z ≤ boxScale k η^2*(rho ν Set.univ) := by
  calc
    _ ≤ ∫⁻ _u,boxScale k η*boxScale k η ∂rho ν :=
      lintegral_mono (fun _ => mul_le_mul' (boxKernel_le η _ _) (boxKernel_le η _ _))
    _ = _ := by simp [pow_two]

lemma projectedReference_shift_le {k d : ℕ} (ν : Measure (Ambient d))
    {η : ℝ} (hη : 0 < η) (X Z : Fin k → Fin d → ℝ) (s : Ambient d)
    (e e' : Fin k → ℝ) (he : e ∈ closedBox 0 η) (he' : e' ∈ closedBox 0 η) :
    projectedReference ν η X Z (projectVector X s+e) (projectVector Z s+e') ≤
      ENNReal.ofReal ((2:ℝ)^(2*k))*mixedCubeAverage (centeredRho ν s) (2*η) X Z := by
  have hm : Measurable (fun u : Ambient d => boxKernel (2*η) (projectVector X u) 0*
      boxKernel (2*η) (projectVector Z u) 0) := by
    have hX : Measurable (fun u : Ambient d => projectVector X u) := by unfold projectVector; fun_prop
    have hZ : Measurable (fun u : Ambient d => projectVector Z u) := by unfold projectVector; fun_prop
    exact ((measurable_boxKernel (2*η)).comp (hX.prodMk measurable_const)).mul
      ((measurable_boxKernel (2*η)).comp (hZ.prodMk measurable_const))
  have hshift : Measurable (fun u : Ambient d => u-s) := by fun_prop
  rw [mixedCubeAverage,centeredRho,lintegral_map hm hshift]
  have hms : Measurable (fun u : Ambient d => boxKernel (2*η) (projectVector X (u-s)) 0 *
      boxKernel (2*η) (projectVector Z (u-s)) 0) := hm.comp hshift
  rw [← lintegral_const_mul _ hms]
  unfold projectedReference
  apply lintegral_mono
  intro u
  have hX := shifted_box_le hη (projectVector X u) (projectVector X s) e he
  have hZ := shifted_box_le hη (projectVector Z u) (projectVector Z s) e' he'
  have hprod := mul_le_mul' hX hZ
  rw [← projectVector_sub,← projectVector_sub] at hprod
  calc
    _ ≤ _ := hprod
    _ = _ := by
      rw [show 2*k=k+k by omega,pow_add,ENNReal.ofReal_mul (by positivity)]
      ring

end KernelPotential.Noise

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end OAI
