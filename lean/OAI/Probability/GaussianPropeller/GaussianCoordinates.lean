import OAI.Probability.GaussianPropeller.CellBounds

namespace OAI

universe uE uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Analytic
section FamilyLaw
variable {E : Type uE} {ι : Type uι} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

lemma covariance_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u,x⟫, fun x => ⟪v,x⟫; stdGaussian E] = ⟪u,v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

lemma hasGaussianLaw_innerFamily (v : ι → E) :
    HasGaussianLaw (fun x : E => fun i => ⟪v i,x⟫) (stdGaussian E) := by
  exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
    (ContinuousLinearMap.pi (fun i => InnerProductSpace.toDual ℝ E (v i)))

lemma indep_innerFamily (v : ι → E) (hv : Pairwise (fun i j => ⟪v i,v j⟫ = 0)) :
    iIndepFun (fun i x => ⟪v i,x⟫) (stdGaussian E) := by
  exact (hasGaussianLaw_innerFamily v).iIndepFun_of_covariance_eq_zero
    (fun i j hij => (covariance_inner_stdGaussian _ _).trans (hv hij))

lemma map_inner_stdGaussian (v : E) :
    (stdGaussian E).map (fun x => ⟪v,x⟫) = gaussianReal 0 (‖v‖^2).toNNReal := by
  change (stdGaussian E).map (InnerProductSpace.toDual ℝ E v) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, LinearIsometryEquiv.norm_map]

lemma map_orthonormal_stdGaussian (v : ι → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => fun i => ⟪v i,x⟫) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  rw [hi.map_fun_eq_pi_map (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [map_inner_stdGaussian, hv.1 i]
  norm_num

end FamilyLaw

end GaussianPropeller.Analytic

namespace GaussianPropeller.Analytic

open scoped ENNReal

section TripleLaw
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma map_orthonormal_triple_stdGaussian (v : Fin 3 → E) (hv : Orthonormal ℝ v) :
    (stdGaussian E).map (fun x => (⟪v 0,x⟫, ⟪v 1,x⟫, ⟪v 2,x⟫)) =
      (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hi := indep_innerFamily v (fun _ _ hij => hv.2 hij)
  have hm (i : Fin 3) : (stdGaussian E).map (fun x => ⟪v i,x⟫) = gaussianReal 0 1 := by
    rw [map_inner_stdGaussian, hv.1 i]
    norm_num
  have hp := hi.indepFun_prodMk (fun _ => by fun_prop) 1 2 0 (by decide) (by decide)
  rw [hp.symm.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hm,
    (hi.indepFun (by decide : (1:Fin 3) ≠ 2)).map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop), hm, hm]

lemma lintegral_orthonormal_triple (v : Fin 3 → E) (hv : Orthonormal ℝ v)
    (f : ℝ × ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f (⟪v 0,x⟫,⟪v 1,x⟫,⟪v 2,x⟫) ∂stdGaussian E =
      ∫⁻ s : ℝ, (∫⁻ u : ℝ, (∫⁻ w : ℝ, f (s,u,w) ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) ∂gaussianReal 0 1 := by
  rw [← lintegral_map hf (by fun_prop), map_orthonormal_triple_stdGaussian v hv,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro s
  exact lintegral_prod _ (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable

end TripleLaw
end GaussianPropeller.Analytic

end OAI
