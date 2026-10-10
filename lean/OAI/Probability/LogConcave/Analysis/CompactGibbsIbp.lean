import Mathlib
import OAI.Probability.LogConcave.JetEstimates.PolyC1
import OAI.Probability.LogConcave.Analysis.GaussianProposalPotential

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Function
open scoped RealInnerProductSpace

lemma compact_gibbs_ibp {d : ℕ} {H g : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,directional v g z ∂gibbs H)=
      ∫z,(inner ℝ (gradient H z) v)*g z ∂gibbs H := by
  have he : ContDiff ℝ 1 (fun z => Real.exp (-H z)) := hH.neg.exp
  have hdg : Continuous (directional v g) := (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdgc : HasCompactSupport (directional v g) := hgc.fderiv_apply ℝ v
  have hD (z : Point d) : fderiv ℝ (fun z => Real.exp (-H z)) z v=
      -(Real.exp (-H z)*inner ℝ (gradient H z) v) := by
    change (fderiv ℝ (fun z => Real.exp ((-H) z)) z) v=_
    rw [((hH.differentiable (by norm_num) z).hasFDerivAt.neg.exp).fderiv]
    simp only [smul_apply,neg_apply,smul_eq_mul,←toDual_gradient,
      InnerProductSpace.toDual_apply_apply,Pi.neg_apply]
    ring
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume)
    (f:=fun z => Real.exp (-H z)) (g:=g) (v:=v)
    (((he.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hg.continuous
      |>.integrable_of_hasCompactSupport hgc.mul_left)
    ((he.continuous.mul hdg).integrable_of_hasCompactSupport hdgc.mul_left)
    ((he.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left)
    (fun z _ => he.differentiable (by norm_num) z)
    (fun z _ => hg.differentiable (by norm_num) z)
  simp only [hD,neg_mul,mul_assoc,integral_neg,neg_neg] at hh
  rw [integral_gibbs_vector hH.continuous hi,integral_gibbs_vector hH.continuous hi]
  simpa only [smul_eq_mul,directional] using congrArg (fun a => (∫z,Real.exp (-H z))⁻¹*a) hh

lemma adjointCoordinate_compact_pairing {d : ℕ} {H f g : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,adjointCoordinate H v f z*g z ∂gibbs H)=
      ∫z,f z*directional v g z ∂gibbs H := by
  have hdf : Continuous (directional v f) := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : Continuous (directional v g) := (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdH : Continuous (directional v H) := (hH.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let := probability_gibbs_of_partition (partition_pos_of_continuous hH.continuous).ne'
    (partition_ne_top_of_integrable hi)
  have h1 : Integrable (fun z => directional v f z*g z) (gibbs H) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h2 : Integrable (fun z => f z*directional v g z) (gibbs H) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  have h3 : Integrable (fun z => (directional v H z*f z)*g z) (gibbs H) :=
    ((hdH.mul hf.continuous).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hh := compact_gibbs_ibp hH hi (hf.mul hg) hgc.mul_left v
  rw [directional_mul (hf.differentiable (by norm_num)) (hg.differentiable (by norm_num)),integral_add h1 h2] at hh
  simp only [←directional_gradient,mul_assoc] at h3 ⊢ hh
  change (∫z,(-directional v f z+directional v H z*f z)*g z ∂gibbs H)=_
  simp_rw [add_mul,neg_mul,mul_assoc]
  rw [integral_add (f:=fun z => -(directional v f z*g z)) h1.neg h3,integral_neg]
  linarith
lemma tensorAdjoint_compact_pairing {d : ℕ} {ι : Type*} [Fintype ι]
    {H g : Point d → ℝ} {V : ι → Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    (hV : ∀i,ContDiff ℝ 1 (V i)) (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (b : ι → Point d) :
    (∫z,tensorAdjoint H b V z*g z ∂gibbs H)=
      ∫z,∑i,V i z*directional (b i) g z ∂gibbs H := by
  let := probability_gibbs_of_partition (partition_pos_of_continuous hH.continuous).ne'
    (partition_ne_top_of_integrable hi)
  have h1 (i : ι) : Integrable (fun z => adjointCoordinate H (b i) (V i) z*g z) (gibbs H) :=
    ((((hV i).continuous_fderiv (by norm_num)).clm_apply continuous_const).neg.add
      (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)
      |>.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h2 (i : ι) : Integrable (fun z => V i z*directional (b i) g z) (gibbs H) :=
    ((hV i).continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hgc.fderiv_apply ℝ (b i)).mul_left
  simp only [tensorAdjoint,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ => h1 i),integral_finsetSum Finset.univ (fun i _ => h2 i)]
  exact Finset.sum_congr rfl (fun i _ => adjointCoordinate_compact_pairing hH hi (hV i) hg hgc (b i))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory EulerDensity
open scoped RealInnerProductSpace ENNReal

lemma standardGaussian_eq_gibbs (d : ℕ) :
    stdGaussian (Point d)=gibbs (gaussianProposalPotential d) := by
  have he : (fun z : Point d => ENNReal.ofReal (Real.exp (-‖z‖^2/2)))=
      gibbsDensity (gaussianProposalPotential d) := by
    funext z
    simp only [gibbsDensity,gaussianProposalPotential_eq,neg_div]
  have hd := standard_density d
  rw [he] at hd
  have hp := congrArg (fun μ : Measure (Point d) => μ Set.univ) hd
  rw [measure_univ,Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,smul_eq_mul] at hp
  change (1:ℝ≥0∞)=gaussianCoefficient d*partition (gaussianProposalPotential d) at hp
  rw [hd,ENNReal.eq_inv_of_mul_eq_one_left hp.symm]
  rfl

lemma compact_gaussian_ibp {d : ℕ} {g : Point d → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : Point d) :
    (∫z,fderiv ℝ g z v ∂stdGaussian (Point d))=
      ∫z,inner ℝ z v*g z ∂stdGaussian (Point d) := by
  rw [standardGaussian_eq_gibbs]
  have hH := (gaussianProposalPotential_admissible d).smooth.of_le (by norm_num : (1:WithTop ℕ∞)≤2)
  simpa only [directional,gaussianProposalPotential_gradient,id_eq] using
    compact_gibbs_ibp hH (gaussianProposalPotential_admissible d).integrable_exp_neg hg hgc v
end LogConcaveSampling

end

end

end

end OAI
