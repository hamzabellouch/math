import Mathlib
import OAI.Probability.LogConcave.Sampling.QuadraticExpectation

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma growth_inner_gradient {d : ℕ} {H : Point d → ℝ} {K : ℝ≥0}
    (hL : LipschitzWith K (gradient H)) (v : Point d) :
    HasPolynomialGrowth (fun z => inner ℝ (gradient H z) v) := by
  have hh := growth_of_lipschitz (((innerSL ℝ v).lipschitzWith).comp hL)
  simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using hh

theorem polynomial_gibbs_ibp {d : ℕ} {H g : Point d → ℝ} {K : ℝ≥0}
    (hH : ContDiff ℝ 1 H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hg : ContDiff ℝ 1 g)
    (hgg : HasPolynomialGrowth g) (v : Point d)
    (hgd : HasPolynomialGrowth (fun z => fderiv ℝ g z v)) :
    (∫ z,fderiv ℝ g z v ∂gibbs H)=
      ∫ z,(inner ℝ (gradient H z) v)*g z ∂gibbs H := by
  have hgc : Continuous (fun z => fderiv ℝ g z v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hSc : Continuous (fun z => inner ℝ (gradient H z) v) :=
    hL.continuous.inner continuous_const
  have hSg : HasPolynomialGrowth (fun z => (inner ℝ (gradient H z) v)*g z) :=
    Appell.HasGrowth.mul (growth_inner_gradient hL v) hgg
  have hf'g : Integrable (fun z => Real.exp (-H z)*((inner ℝ (gradient H z) v)*g z)) := by
    simpa using integrable_tilted H hH.continuous (hSc.mul hg.continuous) ht hSg 0
  have hfg' : Integrable (fun z => Real.exp (-H z)*fderiv ℝ g z v) := by
    simpa using integrable_tilted H hH.continuous hgc ht hgd 0
  have hfg : Integrable (fun z => Real.exp (-H z)*g z) := by
    simpa using integrable_tilted H hH.continuous hg.continuous ht hgg 0
  have hD (z : Point d) : fderiv ℝ (fun z => Real.exp (-H z)) z v=
      -(Real.exp (-H z)*inner ℝ (gradient H z) v) := by
    change (fderiv ℝ (fun z => Real.exp ((-H) z)) z) v=_
    rw [((hH.differentiable (by norm_num) z).hasFDerivAt.neg.exp).fderiv]
    simp only [smul_apply,neg_apply,smul_eq_mul,←toDual_gradient,
      InnerProductSpace.toDual_apply_apply,Pi.neg_apply]
    ring
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ:=volume)
    (f:=fun z => Real.exp (-H z)) (g:=g) (v:=v)
    (by
      convert! hf'g.neg using 1
      funext z
      rw [hD]
      change -(Real.exp (-H z)*inner ℝ (gradient H z) v)*g z=
        -(Real.exp (-H z)*(inner ℝ (gradient H z) v*g z))
      ring) hfg' hfg
    (fun z _ => ((hH.differentiable (by norm_num) z).neg).exp)
    (fun z _ => hg.differentiable (by norm_num) z)
  simp only [hD,neg_mul,mul_assoc,integral_neg,neg_neg] at hh
  have hi : Integrable (fun z => Real.exp (-H z)) := by
    simpa using integrable_tilted H hH.continuous continuous_const ht (growth_const (1:ℝ)) 0
  rw [integral_gibbs_vector hH.continuous hi,integral_gibbs_vector hH.continuous hi]
  simp only [smul_eq_mul,hh]
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
