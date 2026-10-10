import Mathlib
import OAI.Probability.Perceptron.Interpolation.KernelReplicaGibbs

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy
section
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
lemma coupling_tiltIntegral_continuous {H Y G : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => tiltIntegral μ (fun x => H x+a*Y x) G 1) := by
  rw [continuous_iff_continuousAt]
  intro a
  simp only [tiltIntegral,one_mul]
  change Tendsto (fun b => ∫ x, Real.exp (H x+b*Y x)*G x ∂μ) (𝓝 a)
    (𝓝 (∫ x, Real.exp (H x+a*Y x)*G x ∂μ))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => (Real.exp (H x+(a-1)*Y x)+Real.exp (H x+(a+1)*Y x))*B)
  · exact Eventually.of_forall fun b => ((hH.add (hY.const_mul b)).exp.mul hG).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (by linarith : a-1<a) (by linarith : a<a+1)] with b hb
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),
      mul_comm (Real.exp (H x+b*Y x)) |G x|,mul_comm (_+_) B]
    apply mul_le_mul (hGB x) _ (Real.exp_pos _).le hB
    by_cases hy : 0 ≤ Y x
    · exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_right hb.2.le hy) _)).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    · exact (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonpos_right hb.1.le (le_of_not_ge hy)) _)).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
  · exact ((he (a-1)).add (he (a+1))).mul_const B
  · exact ae_of_all _ fun x => (show Continuous (fun b : ℝ => Real.exp (H x+b*Y x)*G x) from by fun_prop).continuousAt

lemma coupling_tiltMean_continuous {H Y G : S → ℝ}
    (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => tiltMean μ (fun x => H x+a*Y x) G 1) := by
  have hp : Continuous (fun a => tiltPartition μ (fun x => H x+a*Y x) 1) := by
    simpa only [tiltIntegral,tiltPartition,mul_one] using
      coupling_tiltIntegral_continuous μ hH hY measurable_const he (by norm_num : (0:ℝ) ≤ 1)
        (fun _ => by norm_num : ∀ x : S, |(fun _ : S => (1:ℝ)) x| ≤ 1)
  exact (coupling_tiltIntegral_continuous μ hH hY hG he hB hGB).div hp
    (fun a => (tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he a)).ne')

lemma coupling_gibbsReplicaMean_continuous {H Y : S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable H) (hY : Measurable Y) (hG : Measurable G)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => gibbsReplicaMean μ (fun x => H x+a*Y x) n G) := by
  have hr (a : ℝ) : replicaPotential (fun x => H x+a*Y x) n =
      fun x => replicaPotential H n x+a*replicaPotential Y n x := by
    funext x
    simp [replicaPotential,Finset.sum_add_distrib,Finset.mul_sum]
  have hi (a : ℝ) : Integrable (fun x => Real.exp (replicaPotential H n x+a*replicaPotential Y n x))
      (Measure.pi (fun _ : Fin n => μ)) := by
    simpa only [one_mul,hr] using replica_exp_integrable μ (H := fun x => H x+a*Y x) (t := 1) (by simpa only [one_mul] using he a) n
  simpa only [gibbsReplicaMean,hr] using coupling_tiltMean_continuous (Measure.pi (fun _ : Fin n => μ))
    (replicaPotential_measurable hH n) (replicaPotential_measurable hY n) hG hi hB hGB

end
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (P : Measure A) [IsFiniteMeasure P] (μ : Measure S) [IsProbabilityMeasure μ]

lemma annealedCoupling_tiltMean_continuous {H Y : A → S → ℝ} {G : S → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (hG : Measurable G)
    (he : ∀ᵐ g ∂P, ∀ a : ℝ, Integrable (fun x => Real.exp (H g x+a*Y g x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => ∫ g, tiltMean μ (fun x => H g x+a*Y g x) G 1 ∂P) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun b => (kernel_tiltMean_measurable (Kernel.const A μ) (H := fun g x => H g x+b*Y g x) (Y := fun _ => G)
      (hH.add (hY.const_mul b)) (hG.comp measurable_snd)).aestronglyMeasurable
  · exact Eventually.of_forall fun b => ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using tiltMean_bound_general μ (H := fun x => H g x+b*Y g x)
        (hH.of_uncurry_left.add (hY.of_uncurry_left.const_mul b)) hG hB hGB
  · exact integrable_const _
  · filter_upwards [he] with g hg
    exact (coupling_tiltMean_continuous μ hH.of_uncurry_left hY.of_uncurry_left hG hg hB hGB).continuousAt

lemma annealedCoupling_replicaMean_continuous {H Y : A → S → ℝ} {n : ℕ} {G : (Fin n → S) → ℝ}
    (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y)) (hG : Measurable G)
    (he : ∀ᵐ g ∂P, ∀ a : ℝ, Integrable (fun x => Real.exp (H g x+a*Y g x)) μ)
    {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B) :
    Continuous (fun a => ∫ g, gibbsReplicaMean μ (fun x => H g x+a*Y g x) n G ∂P) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun b => (kernel_replicaMean_measurable (Kernel.const A μ) (H := fun g x => H g x+b*Y g x) (G := fun _ => G)
      (hH.add (hY.const_mul b)) (hG.comp measurable_snd)).aestronglyMeasurable
  · exact Eventually.of_forall fun b => ae_of_all _ fun g => by
      simpa only [Real.norm_eq_abs,gibbsReplicaMean,Pi.add_apply] using tiltMean_bound_general
        (Measure.pi (fun _ : Fin n => μ))
        (replicaPotential_measurable (v := fun x => H g x+b*Y g x) (hH.of_uncurry_left.add (hY.of_uncurry_left.const_mul b)) n) hG hB hGB
  · exact integrable_const _
  · filter_upwards [he] with g hg
    exact (coupling_gibbsReplicaMean_continuous μ hH.of_uncurry_left hY.of_uncurry_left hG hg hB hGB).continuousAt

lemma sqrt_coupling_derivative {M C : ℝ → ℝ}
    (hd : ∀ a, HasDerivAt M (a*C a) a) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun s => M (Real.sqrt s)) (C (Real.sqrt t)/2) t := by
  have hh := (hd (Real.sqrt t)).comp t (Real.hasDerivAt_sqrt ht.ne')
  have hp := (Real.sqrt_pos.mpr ht).ne'
  have he : Real.sqrt t*C (Real.sqrt t)*(1/(2*Real.sqrt t))=C (Real.sqrt t)/2 := by
    field_simp [hp]
  simpa only [Function.comp_def,he] using hh

lemma sqrt_coupling_right_derivative {M C : ℝ → ℝ}
    (hd : ∀ a, HasDerivAt M (a*C a) a) (hC : Continuous C) :
    HasDerivWithinAt (fun s => M (Real.sqrt s)) (C 0/2) (Ici 0) 0 := by
  have hm : Continuous M := continuous_iff_continuousAt.mpr fun a => (hd a).continuousAt
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
  · intro t ht
    exact (sqrt_coupling_derivative hd ht).differentiableAt.differentiableWithinAt
  · exact (hm.comp Real.continuous_sqrt).continuousWithinAt
  · exact self_mem_nhdsWithin
  · have hh : Tendsto (fun t => C (Real.sqrt t)/2) (𝓝[>] 0) (𝓝 (C 0/2)) := by
      simpa only [Function.comp_def,Real.sqrt_zero] using
        (((hC.comp Real.continuous_sqrt).div_const 2).continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (sqrt_coupling_derivative hd ht).deriv.symm

end SphericalPerceptronFreeEnergy
end

end OAI
