import Mathlib
import OAI.Probability.Perceptron.Variational.CouplingAffine
import OAI.Probability.Perceptron.Variational.ContactFatou

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma quadratic_contact_thermal_disorder_separate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F D : ℝ → Ω → ℝ} {J U : Ω → ℝ}
    (hF : ∀ t, MemLp (F t) 2 P) (hD : ∀ t, AEStronglyMeasurable (D t) P)
    (hJ : AEStronglyMeasurable J P) (hU : AEStronglyMeasurable U P)
    (hU0 : 0 ≤ᵐ[P] U) (hUsq : ∀ᵐ ω ∂P, (U ω)^2 ≤ J ω)
    (hc : ∀ᵐ ω ∂P, ContDiff ℝ 2 (fun t => F t ω) ∧ ConvexOn ℝ univ (fun t => F t ω) ∧
      ∀ t, HasDerivAt (fun t => F t ω) (D t ω) t)
    {u a c s V : ℝ} (hs : 0 < s)
    (he : ∀ᵐ ω ∂P, iteratedDeriv 2 (fun t => F t ω) u = J ω)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-∫ ω, F t ω ∂P) u)
    (hp : c*(u-a)^2-(∫ ω, F u ω ∂P) ≤ c*(u+s-a)^2-(∫ ω, F (u+s) ω ∂P))
    (hm : c*(u-a)^2-(∫ ω, F u ω ∂P) ≤ c*(u-s-a)^2-(∫ ω, F (u-s) ω ∂P))
    (hVp : variance (F (u+s)) P ≤ V) (hV0 : variance (F u) P ≤ V)
    (hVm : variance (F (u-s)) P ≤ V) :
    MemLp U 2 P ∧ Integrable (D u) P ∧
    (∫ ω, U ω ∂P) ≤ Real.sqrt (2*c) ∧
      (∫ ω, |D u ω-∫ η, D u η ∂P| ∂P) ≤ c*s+4*Real.sqrt V/s := by
  have hi (t) := (hF t).integrable (by norm_num)
  have hcurv := quadratic_contact_curvature_bound P hJ hi (hc.mono fun ω hω => ⟨hω.1,hω.2.1⟩) he hmin
  have hUI2 : Integrable (fun ω => U ω^2) P := by
    apply hcurv.1.mono' (hU.pow 2)
    filter_upwards [hUsq] with ω hω
    simpa only [Pi.pow_apply,Real.norm_of_nonneg (sq_nonneg _)] using hω
  have hULp := (memLp_two_iff_integrable_sq hU).mpr hUI2
  have hv := variance_nonneg U P
  rw [variance_eq_sub hULp] at hv
  have hsq : (∫ ω, U ω ∂P)^2 ≤ 2*c := by
    have hh := integral_mono_ae hUI2 hcurv.1 hUsq
    simp only [Pi.pow_apply] at hv
    linarith [hcurv.2]
  have htherm : (∫ ω, U ω ∂P) ≤ Real.sqrt (2*c) :=
    (Real.le_sqrt (integral_nonneg_of_ae hU0) ((sq_nonneg _).trans hsq)).mpr hsq
  have hd := annealed_convex_hasDerivAt P (fun t => (hF t).aestronglyMeasurable) hD hi
    (hc.mono fun ω hω => ⟨hω.2.1,hω.2.2⟩) u
  have hr := quadratic_contact_remainders hd.2 hmin hp hm
  have hAerr (t) (ht : variance (F t) P ≤ V) :
      (∫ ω, |F t ω-∫ η, F t η ∂P| ∂P) ≤ Real.sqrt V :=
    (integral_centered_abs_le_sqrt_variance P (hF t)).trans (Real.sqrt_le_sqrt ht)
  have hdis := integral_convex_contact_bound P (A := fun t => ∫ ω, F t ω ∂P)
    (f := fun ω t => F t ω) (dA := ∫ ω, D u ω ∂P) (C := c) (δ := Real.sqrt V) hs (hD u)
    (hc.mono fun ω hω => ⟨hω.2.1,hω.2.2 u⟩)
    hr.1 hr.2 (hi (u+s)) (hi u) (hi (u-s))
    (hAerr (u+s) hVp) (hAerr u hV0) (hAerr (u-s) hVm)
  exact ⟨hULp,hd.1,htherm,hdis⟩

section
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A)
variable {W : A → S → ℝ} {v w : ℕ → S → ℝ} {L : S → ℕ}
variable (hW : Measurable (Function.uncurry W)) (hv : ∀ i, Measurable (v i))
variable (hw : ∀ i, Measurable (w i)) (hL : Measurable L)
variable {B : A → ℝ} {D E : ℝ} (hB : ∀ a x, |W a x| ≤ B a)
variable (hD : ∀ x, (∑ i : Fin (L x), v i.val x^2) ≤ D)
variable (hE : ∀ x, (∑ i : Fin (L x), w i.val x^2) ≤ E)

include hW hv hw hL

lemma kernelGaussian_coupling_joint_measurable (r : ℝ) :
    Measurable (fun a : (A × (ℕ → ℝ)) × S =>
      countableGaussianHamiltonian (W a.1.1) v L a.1.2 a.2+
        r*countableGaussianField w L a.1.2 a.2) := by
  apply (hW.comp (measurable_fst.fst.prodMk measurable_snd) |>.add
    ((countableGaussianField_measurable hv hL).comp (measurable_fst.snd.prodMk measurable_snd))).add
  exact ((countableGaussianField_measurable hw hL).comp
    (measurable_fst.snd.prodMk measurable_snd)).const_mul r

include hB hD hE

lemma kernelGaussian_coupling_exp_ae (r : ℝ) :
    ∀ᵐ a : A × (ℕ → ℝ) ∂P.prod countableGaussianLaw,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ a.1) := by
  let κ' : Kernel (A × (ℕ → ℝ)) S := κ.comap (Prod.fst : A × (ℕ → ℝ) → A) measurable_fst
  have hm : MeasurableSet {a : A × (ℕ → ℝ) | Integrable
      (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ' a)} :=
    measurableSet_kernel_integrable (kernelGaussian_coupling_joint_measurable hW hv hw hL r).exp.stronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  exact ae_of_all _ fun a => countableGaussian_coupling_exp_ae (κ a)
    (hW.comp (measurable_const.prodMk measurable_id)) hv hw hL (hB a) hD hE r

lemma kernelGaussian_all_coupling_exp_ae :
    ∀ᵐ a : A × (ℕ → ℝ) ∂P.prod countableGaussianLaw, ∀ r : ℝ,
      Integrable (fun x => Real.exp (countableGaussianHamiltonian (W a.1) v L a.2 x+
        r*countableGaussianField w L a.2 x)) (κ a.1) := by
  have hp := ae_all_iff.mpr (fun j : ℕ => kernelGaussian_coupling_exp_ae κ P hW hv hw hL hB hD hE (j:ℝ))
  have hn := ae_all_iff.mpr (fun j : ℕ => kernelGaussian_coupling_exp_ae κ P hW hv hw hL hB hD hE (-(j:ℝ)))
  filter_upwards [hp,hn] with a hp hn r
  apply coupling_integrable_of_integer_endpoints (κ a.1)
    ((hW.comp (measurable_const.prodMk measurable_id)).add
      ((countableGaussianField_measurable hv hL).comp (measurable_const.prodMk measurable_id)))
    ((countableGaussianField_measurable hw hL).comp (measurable_const.prodMk measurable_id)) _ r
  intro j
  exact ⟨hp j,by simpa only [neg_mul,sub_eq_add_neg,Function.comp_apply,Function.uncurry_apply_pair,
    id_eq,Pi.add_apply,countableGaussianHamiltonian] using hn j⟩

end

variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable (κ : Kernel A S) [IsSFiniteKernel κ] {H Y : A → S → ℝ}
variable (hH : Measurable (Function.uncurry H)) (hY : Measurable (Function.uncurry Y))

include hH

lemma kernel_tiltPartition_measurable : Measurable (fun a => tiltPartition (κ a) (H a) 1) := by
  unfold tiltPartition
  exact (hH.const_mul 1 |>.exp.stronglyMeasurable.integral_kernel_prod_right).measurable

include hY

lemma kernel_tiltMean_measurable : Measurable (fun a => tiltMean (κ a) (H a) (Y a) 1) := by
  unfold tiltMean tiltIntegral
  exact ((hH.const_mul 1 |>.exp.mul hY).stronglyMeasurable.integral_kernel_prod_right).measurable.div
    (kernel_tiltPartition_measurable κ hH)

lemma kernel_tiltCenteredVariance_measurable : Measurable (fun a => tiltMean (κ a) (H a)
    (fun x => (Y a x-tiltMean (κ a) (H a) (Y a) 1)^2) 1) := by
  apply kernel_tiltMean_measurable κ hH
  exact (hY.sub ((kernel_tiltMean_measurable κ hH hY).comp measurable_fst)).pow_const 2

lemma kernel_tiltCenteredAbs_measurable : Measurable (fun a => tiltMean (κ a) (H a)
    (fun x => |Y a x-tiltMean (κ a) (H a) (Y a) 1|) 1) := by
  apply kernel_tiltMean_measurable κ hH
  exact (hY.sub ((kernel_tiltMean_measurable κ hH hY).comp measurable_fst)).abs

end SphericalPerceptronFreeEnergy

end

end OAI
