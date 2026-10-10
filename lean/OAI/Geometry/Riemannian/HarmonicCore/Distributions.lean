import OAI.Geometry.Riemannian.HarmonicCore.HigherDerivative

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
open scoped SchwartzMap
open LineDeriv TemperedDistribution

noncomputable def complexifyL2 : ValueL2 →L[ℝ] Lp ℂ 2 (volume : Measure E3) :=
  Complex.ofRealCLM.compLpL 2 volume

lemma complexifyL2_coe (u : ValueL2) :
    (complexifyL2 u : E3 → ℂ) =ᵐ[volume] fun x ↦ Complex.ofReal (u x) :=
  Complex.ofRealCLM.coeFn_compLpL u

noncomputable def realDistribution : ValueL2 →L[ℝ] 𝓢'(E3,ℂ) :=
  ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp complexifyL2

noncomputable def DirichletTest.schwartz {R : ℝ} (u : DirichletTest R) : 𝓢(E3,ℂ) :=
  (u.property.2.1.comp_left (show Complex.ofRealCLM (0:ℝ) = 0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp u.property.1)

lemma complexify_test (R : ℝ) (u : DirichletTest R) :
    complexifyL2 (testValueLinear R u) = (u.schwartz : Lp ℂ 2 (volume : Measure E3)) := by
  apply Lp.ext
  filter_upwards [complexifyL2_coe (testValueLinear R u),u.value_memLp.coeFn_toLp,
    u.schwartz.coeFn_toLp 2 (volume : Measure E3)] with x h1 h2 h3
  rw [h1,h3]
  change Complex.ofReal ((u.value_memLp.toLp _) x) = Complex.ofReal ((u:E3 → ℝ) x)
  rw [h2]

lemma realDistribution_test (R : ℝ) (u : DirichletTest R) :
    realDistribution (testValueLinear R u) = (u.schwartz : 𝓢'(E3,ℂ)) := by
  change (complexifyL2 (testValueLinear R u) : 𝓢'(E3,ℂ)) = _
  rw [complexify_test,Lp.toTemperedDistribution_toLp_eq]

lemma complexify_test_derivative (R : ℝ) (u : DirichletTest R) (a : E3) :
    complexifyL2 (componentL2 a (testDerivativeLinear R u)) =
      ((∂_{a} u.schwartz : 𝓢(E3,ℂ)).toLp 2 (volume : Measure E3)) := by
  apply Lp.ext
  filter_upwards [complexifyL2_coe (componentL2 a (testDerivativeLinear R u)),
    componentL2_coe a (testDerivativeLinear R u),u.derivative_memLp.coeFn_toLp,
    (∂_{a} u.schwartz).coeFn_toLp 2 (volume : Measure E3)] with x h1 h2 h3 h4
  rw [h1,h2,h4,SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hx : (testDerivativeLinear R u) x = gradient (u:E3 → ℝ) x := h3
  rw [hx]
  change Complex.ofReal ⟪a,gradient (u:E3 → ℝ) x⟫_ℝ =
    fderiv ℝ (Complex.ofRealCLM ∘ (u:E3 → ℝ)) x a
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    (u.property.1.differentiable (by simp) x).hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,inner_gradient_right,conj_trivial]
  rfl

lemma realDistribution_test_derivative (R : ℝ) (u : DirichletTest R) (a : E3) :
    realDistribution (componentL2 a (testDerivativeLinear R u)) =
      ∂_{a} (realDistribution (testValueLinear R u)) := by
  rw [realDistribution_test]
  change (complexifyL2 (componentL2 a (testDerivativeLinear R u)) : 𝓢'(E3,ℂ)) = _
  rw [complexify_test_derivative,Lp.toTemperedDistribution_toLp_eq]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq u.schwartz a).symm

theorem sobolev_distribution_derivative (R : ℝ) (u : ZeroSobolev R) (a : E3) :
    realDistribution (componentL2 a (sobolevDerivative R u)) =
      ∂_{a} (realDistribution (sobolevValue R u)) := by
  have hc : IsClosed {z : SobolevPair |
      realDistribution (componentL2 a z.snd) = ∂_{a} (realDistribution z.fst)} :=
    isClosed_eq
      (realDistribution.continuous.comp ((componentL2 a).continuous.comp
        (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous))
      ((lineDerivOpCLM ℂ 𝓢'(E3,ℂ) a).continuous.comp
        (realDistribution.continuous.comp (WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous))
  apply closure_minimal (t:={z : SobolevPair |
      realDistribution (componentL2 a z.snd) = ∂_{a} (realDistribution z.fst)}) _ hc u.property
  rintro z ⟨v,rfl⟩
  exact realDistribution_test_derivative R v a

open Laplacian in

theorem graph_laplacian {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E3) (R Q : ℝ) (u : ZeroSobolev R)
    (w : ι → ZeroSobolev Q)
    (hw : ∀ i, sobolevValue Q (w i) = componentL2 (b i) (sobolevDerivative R u)) :
    Δ (realDistribution (sobolevValue R u)) =
      realDistribution (∑ i, componentL2 (b i) (sobolevDerivative Q (w i))) := by
  rw [laplacian_eq_sum b,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sobolev_distribution_derivative R u (b i),← hw i,
    ← sobolev_distribution_derivative Q (w i) (b i)]

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
