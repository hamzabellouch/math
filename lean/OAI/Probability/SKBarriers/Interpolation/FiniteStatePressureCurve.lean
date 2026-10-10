import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinParameterMoments
import OAI.Probability.SKBarriers.Hierarchy.HierarchyParameterDerivative
import OAI.Probability.SKBarriers.Scalar.PathExponentialAverage
import OAI.Probability.SKBarriers.Hierarchy.WeightedHierarchyCovariance

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

def observableExponent (d : ℕ) (O : Fin d → S → ℝ) (a : Fin d → ℝ)
    (s : S) : ParameterSpace d →L[ℝ] ℝ := coordinateLinear d (fun i => a i*O i s)

def observableCoefficientBilinear (d : ℕ) (O : Fin d → S → ℝ) (s : S) :
    (Fin d → ℝ) →L[ℝ] ParameterSpace d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight (O i s • coordinateProjection d i)

omit [Fintype S] [Nonempty S] in
theorem observableCoefficientBilinear_apply (d : ℕ) (O : Fin d → S → ℝ)
    (s : S) (a : Fin d → ℝ) :
    observableCoefficientBilinear d O s a = observableExponent d O a s := by
  simp only [observableCoefficientBilinear,sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply,observableExponent,coordinateLinear,smul_smul]

theorem observableTerminal_paramRegular (d : ℕ) (O : Fin d → S → ℝ) (c : S → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (observableExponent d O z.1) z.2) := by
  apply paramRegular_log_finite_exp (fun s z => c s+observableExponent d O z.1 s z.2)
  intro s
  apply (paramRegular_const (c s)).add
  simpa only [observableCoefficientBilinear_apply] using
    paramRegular_bilinear (observableCoefficientBilinear d O s)

theorem observableTerminal_parameterDerivative (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (a v : Fin d → ℝ) (z : ParameterSpace d) :
    fderiv ℝ (fun w : (Fin d → ℝ) × ParameterSpace d =>
      affineLogPartition c (observableExponent d O w.1) w.2) (a,z) (v,0) =
      affineMoment c (observableExponent d O a) (fun s => observableExponent d O v s z) z := by
  rw [← parameterFDeriv_at_field ((observableTerminal_paramRegular d O c).1.differentiable (by norm_num)) a v z]
  let L : S → (Fin d → ℝ) →L[ℝ] ℝ := fun s => (observableCoefficientBilinear d O s).flip z
  have he : (fun a : Fin d → ℝ => affineLogPartition c (observableExponent d O a) z) =
      affineLogPartition c L := by
    funext a
    simp only [affineLogPartition,L,ContinuousLinearMap.flip_apply,observableCoefficientBilinear_apply]
  rw [he,fderiv_affineLogPartition_apply]
  simp only [affineMoment,affineGibbs,L,ContinuousLinearMap.flip_apply,observableCoefficientBilinear_apply]

omit [Fintype S] [Nonempty S] in
theorem observableExponent_single (d : ℕ) (O : Fin d → S → ℝ)
    (i : Fin d) (s : S) (z : ParameterSpace d) :
    observableExponent d O (Pi.single i 1) s z = O i s*coordinateProjection d i z := by
  classical
  simp [observableExponent,coordinateLinear_apply,Pi.single_apply]

theorem observablePressure_parameterDerivative_single (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition c (observableExponent d O a)) 0) a (Pi.single i 1) =
      ∫ z, coordinateProjection d i z*affineMoment c (observableExponent d O a) (O i) z
        ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O a)) 0 := by
  classical
  have hP := hierarchyPressure_paramRegular d m _ (observableTerminal_paramRegular d O c)
  rw [parameterFDeriv_at_field (hP.1.differentiable (by norm_num)),
    hierarchyPressure_parameterDerivative d m _ (observableTerminal_paramRegular d O c)]
  simp only [observableTerminal_parameterDerivative,observableExponent_single]
  have he : (fun z : ParameterSpace d => affineMoment c (observableExponent d O a)
      (fun s => O i s*coordinateProjection d i z) z) = fun z =>
        coordinateProjection d i z*affineMoment c (observableExponent d O a) (O i) z := by
    funext z
    simp only [affineMoment,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [he]
  apply hierarchyAverage_eq_integral_exp d m _ (affineLogPartition_boundedDerivs _ _)
  · exact (coordinateProjection d i).continuous.mul (affineMoment_continuous _ _ _)
  · let B := ∑ s, ‖O i s‖
    have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    exact (HasExpGrowth.linear _).mul (HasExpGrowth.of_bounded hB
      (affineMoment_norm_le c _ (O i) (fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s))))

theorem observablePressure_coefficient_variation (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (a : Fin d → ℝ) (m : Fin d → ℝ) (i : Fin d) :
    fderiv ℝ (fun a : Fin d → ℝ =>
      hierarchyPressure d m (affineLogPartition c (observableExponent d O a)) 0) a (Pi.single i 1) =
      a i*((∫ z, affineMoment c (observableExponent d O a) (fun s => (O i s)^2) z
        ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O a)) 0)-
        ∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j*
          (∫ z, (hierarchyMomentLevel d m (affineLogPartition c (observableExponent d O a))
            (affineMoment c (observableExponent d O a) (O i)) j z)^2
              ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O a)) 0) else 0) := by
  rw [observablePressure_parameterDerivative_single]
  apply weightedHierarchy_coordinate_covariance
  intro s
  simp only [observableExponent,coordinateLinear_coordinateAxis]

theorem observablePressure_hasDerivAt_curve (d : ℕ) (O : Fin d → S → ℝ)
    (c : S → ℝ) (m : Fin d → ℝ) (a : ℝ → Fin d → ℝ) {t : ℝ} {a' : Fin d → ℝ}
    (ha : HasDerivAt a a' t) :
    HasDerivAt (fun u => hierarchyPressure d m (affineLogPartition c (observableExponent d O (a u))) 0)
      (∑ i : Fin d, a' i*(a t i*((∫ z, affineMoment c (observableExponent d O (a t)) (fun s => (O i s)^2) z
        ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O (a t))) 0)-
        ∑ j : Fin (d+1), if i.val < j.val then hierarchyAtom d m 1 j*
          (∫ z, (hierarchyMomentLevel d m (affineLogPartition c (observableExponent d O (a t)))
            (affineMoment c (observableExponent d O (a t)) (O i)) j z)^2
              ∂hierarchyPathLaw d m (affineLogPartition c (observableExponent d O (a t))) 0) else 0))) t := by
  have hp := hierarchyPressure_paramRegular d m _ (observableTerminal_paramRegular d O c)
  have hd := (parameter_contDiff_at_field hp.1 (0:ℝ)).differentiable (by norm_num)
  have H := (hd (a t)).hasFDerivAt.comp_hasDerivAt t ha
  apply H.congr_deriv
  symm
  conv_rhs => rw [pi_eq_sum_univ' a',map_sum]
  simp only [map_smul,smul_eq_mul,observablePressure_coefficient_variation]

end
end SK.Analytic

end
end

end OAI
