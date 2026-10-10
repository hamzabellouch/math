import Mathlib
import OAI.Probability.LogConcave.Analysis.Law

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ}

lemma posterior_joint_integral_zero {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) {u : Point d × Point d → ℝ}
    (hi : Integrable u (jointPosteriorLaw V h))
    (hu : ∀y,(∫z,u (z,y) ∂gibbs (posteriorPotential V h y))=0) :
    (∫p,u p ∂jointPosteriorLaw V h)=0 := by
  let c := (partition V)⁻¹*EulerDensity.noiseCoefficient d (Real.sqrt h)
  have hs := (Real.sqrt_pos.mpr hh).ne'
  have hc0 : c≠0 := mul_ne_zero (ENNReal.inv_ne_zero.mpr hV.partition_ne_top)
    (EulerDensity.noiseCoefficient_positive d hs).ne'
  have hct : c≠⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hV.partition_pos.ne')
    (EulerDensity.noiseCoefficient_finite _ _)
  let w := fun p : Point d × Point d => Real.exp (-posteriorPotential V h p.2 p.1)
  have hw0 : ∀p,0≤w p := fun p => (Real.exp_pos _).le
  have hw : Measurable w := by
    have hm := hV.smooth.continuous.measurable
    dsimp [w,posteriorPotential]
    fun_prop
  have hden : Measurable (fun p => ENNReal.ofReal (w p)) := hw.ennreal_ofReal
  have hd := EulerDensity.joint_density hV.smooth.continuous.measurable
    (fun z : Point d => z) measurable_id hs
  simp only [Real.sq_sqrt hh.le] at hd
  have hd' : jointPosteriorLaw V h=
      c • ((volume : Measure (Point d)).prod volume).withDensity (fun p => ENNReal.ofReal (w p)) := by
    have hw' : w=(fun p : Point d × Point d =>
        Real.exp (-V p.1-‖p.2-p.1‖^2/(2*h))) := by
      funext p
      simp only [w,posteriorPotential,norm_sub_rev p.1 p.2]
      congr 1
      ring
    simpa only [jointPosteriorLaw,c,hw'] using hd
  rw [hd'] at hi ⊢
  have hif : Integrable (fun p => w p • u p) ((volume : Measure (Point d)).prod volume) := by
    have hi' := (integrable_smul_measure hc0 hct).mp hi
    rw [integrable_withDensity_iff_integrable_smul' hden
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)] at hi'
    simpa only [ENNReal.toReal_ofReal (hw0 _)] using hi'
  rw [integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    hden (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hw0 _)]
  rw [integral_prod_symm _ hif]
  have hz : ∀y,(∫z,w (z,y) • u (z,y))=0 := by
    intro y
    exact weighted_integral_zero_of_gibbs (posterior_smooth hV h y).continuous
      ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous) (hu y)
  simp_rw [hz]
  simp

lemma posterior_reconstruction_integral {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0<h) {f : Point d → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : 0≤C) (hb : ∀x,|f x|≤C) :
    (∫y,(∫z,f z ∂gibbs (posteriorPotential V h y)) ∂noisedLaw V h)=∫z,f z ∂gibbs V := by
  let := hV.isProbabilityMeasure_gibbs
  let := noisedLaw_probability hV h
  let := jointPosteriorLaw_probability hV h
  let : ∀y : Point d,IsProbabilityMeasure (gibbs (posteriorPotential V h y)) := fun y =>
    probability_gibbs_of_partition (partition_pos_of_continuous (posterior_smooth hV h y).continuous).ne'
      (partition_ne_top_of_integrable ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous))
  let g := fun y => ∫z,f z ∂gibbs (posteriorPotential V h y)
  have hg : Measurable g := (hf.stronglyMeasurable.integral_kernel
    (κ:=posteriorKernel V hV h)).measurable
  have hgb (y : Point d) : |g y|≤C := bounded_integral hC hb
  have hiz : Integrable (fun p : Point d × Point d => f p.1) (jointPosteriorLaw V h) :=
    bounded_integrable (hf.comp measurable_fst) (fun p => hb p.1)
  have hiy : Integrable (fun p : Point d × Point d => g p.2) (jointPosteriorLaw V h) :=
    bounded_integrable (hg.comp measurable_snd) (fun p => hgb p.2)
  have hz := posterior_joint_integral_zero hV hh (hiz.sub hiy) (fun y => by
    simp only [Pi.sub_apply]
    rw [integral_sub (bounded_integrable hf hb) (integrable_const (g y))]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,g,sub_self])
  simp only [Pi.sub_apply] at hz
  rw [integral_sub hiz hiy] at hz
  have hfz : (∫p : Point d × Point d,f p.1 ∂jointPosteriorLaw V h)=∫z,f z ∂gibbs V := by
    rw [←jointPosterior_fst (V:=V) h,integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
  have hgy : (∫p : Point d × Point d,g p.2 ∂jointPosteriorLaw V h)=∫y,g y ∂noisedLaw V h := by
    rw [←jointPosterior_snd (V:=V) h,integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]
  rw [hfz,hgy] at hz
  exact (sub_eq_zero.mp hz).symm

end LogConcaveSampling

end

end

end OAI
