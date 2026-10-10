import OAI.Geometry.NodalSets.Coefficients.GaussianCoefficientVariance
import OAI.Geometry.NodalSets.Waves.GaussianFactorBound

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def pairJetMap (z : κ → ι → ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ ↦ ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun k ↦ ∑ p : ι × Fin 2,
      (if p.2 = 0 then (z k p.1).re else -(z k p.1).im) • EuclideanSpace.proj p)

omit [Fintype κ] in
lemma pairJetMap_apply (z : κ → ι → ℂ) (a : ι × Fin 2 → ℝ) (k : κ) :
    pairJetMap z (WithLp.toLp 2 a) k = pairLinearSum (z k) a := by
  change (∑ p : ι × Fin 2,
    (if p.2 = 0 then (z k p.1).re else -(z k p.1).im) • EuclideanSpace.proj p)
      (WithLp.toLp 2 a) = _
  simp only [sum_apply, smul_apply]
  rfl

lemma pairJetMap_law (z : κ → ι → ℂ) :
    (gaussianPairs (ι := ι)).map (fun a ↦ pairJetMap z (WithLp.toLp 2 a)) =
      (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map (pairJetMap z) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma variance_gaussianMap_inner (T : EuclideanSpace ℝ (ι × Fin 2) →L[ℝ] EuclideanSpace ℝ κ)
    (v : EuclideanSpace ℝ κ) :
    Var[fun a : ι × Fin 2 → ℝ ↦ ⟪v,T (WithLp.toLp 2 a)⟫; gaussianPairs] =
      ‖T.adjoint v‖^2 := by
  have hm : (gaussianPairs (ι := ι)).map (WithLp.toLp 2) =
      stdGaussian (EuclideanSpace ℝ (ι × Fin 2)) := map_pi_eq_stdGaussian
  have hv := covarianceBilin_self (μ := (stdGaussian (EuclideanSpace ℝ (ι × Fin 2))).map T)
    IsGaussian.memLp_two_id v
  rw [covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
    innerSL_apply_apply,real_inner_self_eq_norm_sq] at hv
  rw [variance_map (by fun_prop) (by fun_prop),← hm,
    variance_map (by fun_prop) (by fun_prop)] at hv
  exact hv.symm

end
end Yau.Probability

end OAI
