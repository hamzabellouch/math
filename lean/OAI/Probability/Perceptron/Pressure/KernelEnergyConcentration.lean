import Mathlib
import OAI.Probability.Perceptron.Variational.UnboundedContact

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable {H Y : A → S → ℝ}

lemma kernel_coupling_energy_concentration
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    (he : ∀ᵐ a ∂P, ∀ r : ℝ, Integrable (fun x => Real.exp (H a x+r*Y a x)) (κ a))
    (hm : Integrable (fun a => tiltMean (κ a) (H a) (Y a) 1) P)
    (ht : Integrable (fun a => tiltMean (κ a) (H a)
      (fun x => |Y a x-tiltMean (κ a) (H a) (Y a) 1|) 1) P) :
    let EY := ∫ a, tiltMean (κ a) (H a) (Y a) 1 ∂P
    Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x|) 1) P ∧
      Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x-EY|) 1) P ∧
      (∫ a, tiltMean (κ a) (H a) (fun x => |Y a x-EY|) 1 ∂P) ≤
        (∫ a, tiltMean (κ a) (H a) (fun x => |Y a x-tiltMean (κ a) (H a) (Y a) 1|) 1 ∂P)+
        ∫ a, |tiltMean (κ a) (H a) (Y a) 1-EY| ∂P := by
  dsimp only
  let m := fun a => tiltMean (κ a) (H a) (Y a) 1
  let U := fun a => tiltMean (κ a) (H a) (fun x => |Y a x-m a|) 1
  have ht' : Integrable U P := ht
  have hbound (c : ℝ) : ∀ᵐ a ∂P,
      tiltMean (κ a) (H a) (fun x => |Y a x-c|) 1 ≤ U a+|m a-c| := by
    filter_upwards [he] with a he
    simpa only [zero_mul,add_zero] using
      coupling_tilt_center_triangle (κ a) hH.of_uncurry_left hY.of_uncurry_left he 0 (m a) c
  have hib (c : ℝ) : Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x-c|) 1) P := by
    apply (ht'.add ((hm.sub (integrable_const c)).abs)).mono'
      (kernel_tiltMean_measurable κ (Y := fun a x => |Y a x-c|) hH (hY.sub measurable_const |>.abs)).aestronglyMeasurable
    filter_upwards [hbound c] with a ha
    simpa only [Pi.add_apply,Pi.sub_apply,Real.norm_of_nonneg (tiltMean_nonneg (κ a) (fun _ => abs_nonneg _) 1)] using ha
  refine ⟨by simpa only [sub_zero] using hib 0,hib (∫ a, m a ∂P),?_⟩
  calc
    _ ≤ ∫ a, U a+|m a-∫ b, m b ∂P| ∂P := integral_mono_ae (hib _) (ht'.add ((hm.sub (integrable_const _)).abs)) (hbound _)
    _ = _ := integral_add ht' ((hm.sub (integrable_const _)).abs)

lemma kernel_scaled_energy_concentration
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))
    (he : ∀ᵐ a ∂P, ∀ r : ℝ, Integrable (fun x => Real.exp (H a x+r*Y a x)) (κ a))
    {v C D : ℝ} (hv : 0<v)
    (hm : Integrable (fun a => v*tiltMean (κ a) (H a) (Y a) 1) P)
    (ht : Integrable (fun a => Real.sqrt v*tiltMean (κ a) (H a)
      (fun x => |Y a x-tiltMean (κ a) (H a) (Y a) 1|) 1) P)
    (hC : (∫ a, Real.sqrt v*tiltMean (κ a) (H a)
      (fun x => |Y a x-tiltMean (κ a) (H a) (Y a) 1|) 1 ∂P) ≤ C)
    (hD : (∫ a, |v*tiltMean (κ a) (H a) (Y a) 1-
      ∫ b, v*tiltMean (κ b) (H b) (Y b) 1 ∂P| ∂P) ≤ D) :
    let EY := ∫ a, tiltMean (κ a) (H a) (Y a) 1 ∂P
    Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x|) 1) P ∧
      Integrable (fun a => tiltMean (κ a) (H a) (fun x => |Y a x-EY|) 1) P ∧
      (∫ a, tiltMean (κ a) (H a) (fun x => |Y a x-EY|) 1 ∂P) ≤ C/Real.sqrt v+D/v := by
  have hm' : Integrable (fun a => tiltMean (κ a) (H a) (Y a) 1) P := by
    convert hm.div_const v using 1
    funext a
    exact (mul_div_cancel_left₀ _ hv.ne').symm
  have ht' : Integrable (fun a => tiltMean (κ a) (H a)
      (fun x => |Y a x-tiltMean (κ a) (H a) (Y a) 1|) 1) P := by
    convert ht.div_const (Real.sqrt v) using 1
    funext a
    exact (mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hv).ne').symm
  have hres := kernel_coupling_energy_concentration κ P hH hY he hm' ht'
  refine ⟨hres.1,hres.2.1,hres.2.2.trans (add_le_add ?_ ?_)⟩
  · rw [integral_const_mul] at hC
    exact (le_div_iff₀ (Real.sqrt_pos.mpr hv)).mpr (by simpa only [mul_comm] using hC)
  · simp_rw [integral_const_mul,← mul_sub,abs_mul,abs_of_pos hv] at hD
    rw [integral_const_mul] at hD
    exact (le_div_iff₀ hv).mpr (by simpa only [mul_comm] using hD)

end SphericalPerceptronFreeEnergy
end

end OAI
