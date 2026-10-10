import Mathlib
import OAI.Probability.SKBarriers.Replicas.CommonBranch
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment
import OAI.Probability.SKBarriers.Scalar.VectorAverageRegular
import OAI.Probability.SKBarriers.Gaussian.AffineCoordinateMean

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarWeightedField_eq (n : ℕ) (v a : Fin n → ℝ) (z : ParameterSpace n) :
    (parameter n z,(0:ℝ))+∑ i, coordinateProjection n i z • (v i,a i)=
      (scalarSpinField n v z,coordinateLinear n a z) := by
  apply Prod.ext
  · have H := map_sum (ContinuousLinearMap.fst ℝ ℝ ℝ)
      (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    simpa only [Prod.fst_add,ContinuousLinearMap.coe_fst',Prod.smul_fst,smul_eq_mul,
      scalarSpinField,add_apply,coordinateLinear_apply,mul_comm] using congrArg (parameter n z+·) H
  · have H := map_sum (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (fun i => coordinateProjection n i z • (v i,a i)) Finset.univ
    simpa only [Prod.snd_add,zero_add,ContinuousLinearMap.coe_snd',Prod.smul_snd,smul_eq_mul,
      coordinateLinear_apply,mul_comm] using H

theorem scalarWeightedTest_integral (n : ℕ) (m v a : Fin n → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    vectorHierarchyAverage n m (fun i => (v i,a i)) (fun p : ℝ × ℝ => f p.1) g (x,0)=
      ∫ z, g (scalarSpinField n v z,coordinateLinear n a z)
        ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have H := congrFun (hierarchyAverage_vector_linear n m (fun i => (v i,a i))
    (fun p : ℝ × ℝ => f p.1) g (fun x => (x,0))) x
  simp only [scalarWeightedField_eq] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v)) _
    (hg.comp ((scalarSpinField n v).prod (coordinateLinear n a)).continuous)
    (hE.compCLM ((scalarSpinField n v).prod (coordinateLinear n a))) x

theorem scalarHierarchyAverage_pathIntegral_exp (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (scalarSpinField n v z) ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have H := congrFun (hierarchyAverage_vector_linear n m v f g id) x
  have he (z : ParameterSpace n) : parameter n z+∑ i, coordinateProjection n i z • v i=scalarSpinField n v z := by
    simp only [scalarSpinField,add_apply,coordinateLinear_apply,smul_eq_mul,mul_comm]
  simp only [id_eq] at H
  simp only [he,vectorHierarchyAverage_real] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v)) _
    (hg.comp (scalarSpinField n v).continuous) (hE.compCLM (scalarSpinField n v)) x

theorem scalarPath_weighted_mean (n : ℕ) (m v a : Fin n → ℝ) (x : ℝ) :
    (∫ z, coordinateLinear n a z ∂hierarchyPathLaw n m (scalarSpinTerminal ∘ scalarSpinField n v) x)=
      (∑ i, a i*v i*m i)*deriv (scalarHierarchy n m v scalarSpinTerminal) x := by
  let f := affineLogPartition (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  have hf := affineLogPartition_boundedDerivs (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  have he : scalarSpinTerminal ∘ scalarSpinField n v=f := by
    simpa only [f,Function.comp_def,scalarSpinField,add_apply,coordinateLinear_apply] using scalarSpinTerminal_affine n v
  have hmean : (∫ z, affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin z
      ∂hierarchyPathLaw n m f x)=deriv (scalarHierarchy n m v scalarSpinTerminal) x := by
    rw [scalarSpin_affineMoment,scalarSpinRoot_gradient,← he]
    have hs : scalarParameterTerminal n v (fun a y => scalarMagnetization (a+y)) 0=
        scalarMagnetization ∘ scalarSpinField n v := by
      funext z
      simp only [scalarParameterTerminal,zero_add,Function.comp_def,scalarSpinField,
        add_apply,coordinateLinear_apply]
    rw [hs]
    exact (scalarHierarchyAverage_pathIntegral_exp n m v scalarSpinTerminal_regular
      scalarMagnetization_lipschitz.continuous (HasExpGrowth.of_bounded zero_le_one (fun y => by
        simpa only [Real.norm_eq_abs] using scalarMagnetization_abs_le_one y)) x).symm.trans
      (scalarHierarchy_gradient_average n m v scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt x).symm
  rw [he]
  have hi (i : Fin n) : Integrable (fun z => a i*coordinateProjection n i z) (hierarchyPathLaw n m f x) :=
    ((HasExpGrowth.const (a i)).mul (HasExpGrowth.linear (coordinateProjection n i))).integrable_hierarchyPathLaw
      n m hf ((coordinateProjection n i).continuous.const_mul _) x
  simp_rw [coordinateLinear_apply]
  rw [integral_finsetSum _ (fun i _ => hi i),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,affineHierarchy_coordinate_mean n m (fun _ : Bool => 0)
    (fun b => spin b • scalarSpinField n v) spin (v i) i
    (fun b => by simp [scalarSpinField,parameter_coordinateAxis,coordinateLinear_coordinateAxis,mul_comm]) x,hmean]
  ring

end SK.Analytic

end
end

end OAI
