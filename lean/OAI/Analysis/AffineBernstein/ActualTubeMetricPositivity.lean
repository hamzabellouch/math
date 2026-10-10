import Mathlib
import OAI.Analysis.AffineBernstein.MatrixMetric
import OAI.Analysis.AffineBernstein.ActualInvariantTube
import OAI.Analysis.AffineBernstein.TensorIntegration
import OAI.Analysis.AffineBernstein.RoundSliceContractions
import OAI.Analysis.AffineBernstein.JointTubeMetrics

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ActualTubeMetricPositivity
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem affineEpigraph_tube_angular_pair_nonneg {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {g : S × E → ℝ} (hg : DifferentiableAt ℝ g (s,e)) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    0 ≤ tubeAngularPair H bE g g (s,e) := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  obtain ⟨c,hc⟩ := exists_orthonormalBasis_last bE he
  have hH : ContDiffAt ℝ ∞ H (s,e) := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hen).1
  have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs hen bS bE
  have hRp := (affineEpigraph_tube_positive hΩ hcv hu hp a L hD hK hzero hs bS c hc).2
  have hrad : ∀ v, fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 :=
    affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs hen
  change 0 ≤ H (s,e)/tubeAngularDensity H (s,e) bE * _
  rw [supportNewtonPair_slice bE c hH hc hrad hRp.det_pos.ne' hg hg]
  exact mul_nonneg (div_pos hpos.2.2 hpos.2.1).le
    (mul_nonneg hRp.det_pos.le (inverseMatrixPair_self_nonneg hRp _))
end ActualTubeMetricPositivity

open Metric
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gradient_exp_linear_combination {P F : E → ℝ} {e : E}
    (hP : DifferentiableAt ℝ P e) (hF : DifferentiableAt ℝ F e) (a c : ℝ) :
    gradient (fun y => Real.exp (a*P y+c*F y)) e =
      Real.exp (a*P e+c*F e) • (a • gradient P e+c • gradient F e) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hh : HasFDerivAt (fun y => Real.exp (a*P y+c*F y))
      (Real.exp (a*P e+c*F e) • (a • fderiv ℝ P e+c • fderiv ℝ F e)) e :=
    ((hP.hasFDerivAt.const_mul a).add (hF.hasFDerivAt.const_mul c)).exp
  rw [hh.fderiv]
  simp [inner_add_left,real_inner_smul_left,inner_gradient_left,mul_left_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tangentProjection_smul_add (e v w : E) (a b : ℝ) :
    tangentProjection e (a • v+b • w) = a • tangentProjection e v+b • tangentProjection e w := by
  simp only [tangentProjection,inner_add_right,real_inner_smul_right,add_smul,
    mul_smul,smul_sub]
  abel

/- Exact angular weighted integration by parts for the source exponential
weight. The cofactor divergence and radial cancellations are proved by the
Newton calculus, not included as additional hypotheses. -/
theorem integral_supportNewtonTensor_exp_weight (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {H P F : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    (hP : ContDiffOn ℝ ∞ P U) (hF : ContDiffOn ℝ ∞ F U) (a c : ℝ) :
    (∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      roundHessianContraction b (supportNewtonTensor b H) F e ∂volume.toSphere) =
      -(∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
        (a * supportNewtonTensor b H e (tangentProjection e (gradient P e))
            (tangentProjection e (gradient F e)) +
         c * supportNewtonTensor b H e (tangentProjection e (gradient F e))
            (tangentProjection e (gradient F e))) ∂volume.toSphere) := by
  rw [integral_supportNewtonTensor_by_parts b hU hSU hH hr
    (((contDiffOn_const.mul hP).add (contDiffOn_const.mul hF)).exp) hF]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro e
  dsimp only
  rw [gradient_exp_linear_combination
    ((hP.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))
    ((hF.contDiffAt (hU.mem_nhds (hSU e.property))).differentiableAt (by simp))]
  change supportNewtonTensor b H e
    (tangentProjectionCLM (e : E) (Real.exp (a*P e+c*F e) • (a • gradient P e+c • gradient F e))) _ = _
  simp only [map_smul,map_add,smul_apply,add_apply,smul_eq_mul,tangentProjectionCLM_apply]

omit [MeasurableSpace E] [BorelSpace E] in
lemma sphere_tangent_gradient_continuous {U : Set E} (hU : IsOpen U)
    (hSU : sphere (0:E) 1 ⊆ U) {F : E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    Continuous (fun e : sphere (0:E) 1 => tangentProjection (e : E) (gradient F (e : E))) := by
  have hgc : Continuous (fun e : sphere (0:E) 1 => gradient F (e : E)) := by
    refine ContinuousOn.comp_continuous (g := gradient F) ?_ continuous_subtype_val (fun e => hSU e.property)
    intro e he
    exact (contDiffAt_gradient (hF.contDiffAt (hU.mem_nhds he))).continuousAt.continuousWithinAt
  exact hgc.sub ((continuous_subtype_val.inner hgc).smul continuous_subtype_val)

omit [MeasurableSpace E] [BorelSpace E] in
lemma sphere_supportNewtonTensor_continuous (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0:E) 1 ⊆ U)
    {H : E → ℝ} (hH : ContDiffOn ℝ ∞ H U) :
    Continuous (fun e : sphere (0:E) 1 => supportNewtonTensor b H e) := by
  refine ContinuousOn.comp_continuous (g := supportNewtonTensor b H) ?_ continuous_subtype_val (fun e => hSU e.property)
  intro e he
  exact (contDiffAt_supportNewtonTensor b (hH.contDiffAt (hU.mem_nhds he))).continuousAt.continuousWithinAt

/- The angular drift coefficient after integration is exactly `1-c`.
At `c=(n+2)/2` this is `-n/2`, as in tubes.tex. -/
theorem integral_supportNewtonTensor_weighted_drift (b : OrthonormalBasis ι ℝ E)
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    {H P F : E → ℝ} (hH : ContDiffOn ℝ ∞ H U)
    (hr : ∀ q ∈ U, ∀ v, fderiv ℝ (fderiv ℝ H) q v q = 0)
    (hP : ContDiffOn ℝ ∞ P U) (hF : ContDiffOn ℝ ∞ F U) (a c : ℝ) :
    (∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      roundHessianContraction b (supportNewtonTensor b H) F e ∂volume.toSphere) +
    a*(∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      supportNewtonTensor b H e (tangentProjection e (gradient P e))
        (tangentProjection e (gradient F e)) ∂volume.toSphere) +
    (∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      supportNewtonTensor b H e (tangentProjection e (gradient F e))
        (tangentProjection e (gradient F e)) ∂volume.toSphere) =
    (1-c)*(∫ e : sphere (0 : E) 1, Real.exp (a*P e+c*F e) *
      supportNewtonTensor b H e (tangentProjection e (gradient F e))
        (tangentProjection e (gradient F e)) ∂volume.toSphere) := by
  have hpc := hP.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hfc := hF.continuousOn.comp_continuous continuous_subtype_val (fun e => hSU e.property)
  have hwc : Continuous (fun e : sphere (0:E) 1 => Real.exp (a*P e+c*F e)) :=
    Real.continuous_exp.comp ((continuous_const.mul hpc).add (continuous_const.mul hfc))
  have htc := sphere_supportNewtonTensor_continuous b hU hSU hH
  have hdpc := sphere_tangent_gradient_continuous hU hSU hP
  have hdfc := sphere_tangent_gradient_continuous hU hSU hF
  have hi1 := (hwc.mul ((htc.clm_apply hdpc).clm_apply hdfc)).integrable_of_hasCompactSupport (μ := volume.toSphere)
    (HasCompactSupport.of_compactSpace _)
  have hi2 := (hwc.mul ((htc.clm_apply hdfc).clm_apply hdfc)).integrable_of_hasCompactSupport (μ := volume.toSphere)
    (HasCompactSupport.of_compactSpace _)
  simp only [Pi.mul_def] at hi1 hi2
  rw [integral_supportNewtonTensor_exp_weight b hU hSU hH hr hP hF a c]
  have hsplit : (∫ e : sphere (0:E) 1, Real.exp (a*P e+c*F e) *
      (a * supportNewtonTensor b H e (tangentProjection e (gradient P e)) (tangentProjection e (gradient F e)) +
       c * supportNewtonTensor b H e (tangentProjection e (gradient F e)) (tangentProjection e (gradient F e))) ∂volume.toSphere) =
      a*(∫ e : sphere (0:E) 1, Real.exp (a*P e+c*F e) * supportNewtonTensor b H e
        (tangentProjection e (gradient P e)) (tangentProjection e (gradient F e)) ∂volume.toSphere) +
      c*(∫ e : sphere (0:E) 1, Real.exp (a*P e+c*F e) * supportNewtonTensor b H e
        (tangentProjection e (gradient F e)) (tangentProjection e (gradient F e)) ∂volume.toSphere) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hi1.const_mul a) (hi2.const_mul c)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => by ring
  rw [hsplit]
  ring

end AffineBernstein
end

end OAI
