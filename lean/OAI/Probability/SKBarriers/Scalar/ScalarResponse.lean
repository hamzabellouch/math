import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyIncrementCovariance
import OAI.Probability.SKBarriers.Scalar.ScalarSusceptibilitySum

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarFiniteResponse (n : ℕ) (m v : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  1-∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
    scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0

theorem scalarSpin_affineMoment (n : ℕ) (v : Fin n → ℝ) :
    affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin =
      rootGradient n (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v)) := by
  funext z
  rw [rootGradient,fderiv_affineLogPartition_apply]
  congr 2
  funext b
  simp only [smul_apply,smul_eq_mul,scalarSpinField,add_apply,parameter_axis,coordinateLinear_axis,add_zero,mul_one]

theorem scalarMomentSquare_eq_path_integral (n : ℕ) (m v : Fin n → ℝ)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, (hierarchyMomentLevel n m
      (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v))
      (affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) spin) j z)^2
      ∂hierarchyPathLaw n m
        (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v)) x)=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
  rw [scalarSpin_affineMoment]
  have hf₀ := affineLogPartition_boundedDerivs (fun _ : Bool => (0:ℝ))
    (fun b => spin b • scalarSpinField n v)
  have hM := hierarchyMomentLevel_bounded_continuous n m _ _ hf₀
    (rootGradient_continuous n hf₀) zero_le_one (fun z => (scalarSpinRoot_curvature n v |>.bounds z).1) j
  rw [← hierarchyAverage_eq_integral n m _ hf₀ (fun z =>
    (hierarchyMomentLevel n m _ _ j z)^2) (hM.1.pow 2) zero_le_one (fun z => by
    rw [norm_pow]
    simpa using (pow_le_pow_left₀ (norm_nonneg _) (hM.2 z) 2)) x]
  rw [scalarSpinRoot_gradient n v,← scalarSpinParameter_eq n v]
  have hf : BoundedDerivs (scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0) := by
    rw [scalarSpinParameter_eq]
    exact affineLogPartition_boundedDerivs _ _
  have H := scalarMomentSquare_eq_parameterAverage n m v
    (fun a y => scalarSpinTerminal (a+y)) (fun a y => scalarMagnetization (a+y)) 0 x hf j
  have HE : scalarMomentSquare n m v (fun y => scalarSpinTerminal (x+y))
      (fun y => scalarMagnetization (x+y)) j 0=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
    simpa only [add_zero] using scalarMomentSquare_translate n m v scalarSpinTerminal scalarMagnetization j x 0
  exact (H.symm.trans HE)

theorem affineHierarchyResponse_scalar (n : ℕ) (m v : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    affineHierarchyResponse n m (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v) spin i x = scalarFiniteResponse n m v i x := by
  let f := affineLogPartition (fun _ : Bool => (0:ℝ)) (fun b => spin b • scalarSpinField n v)
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs _ _) x
  have he : affineMoment (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v)
      (fun b => (spin b)^2) = fun _ => (1:ℝ) := by
    funext z
    have hs : (fun b : Bool => (spin b)^2)=fun _ => (1:ℝ) := by funext b; cases b <;> norm_num [spin]
    rw [hs]
    simp only [affineMoment,mul_one,affineGibbs_sum]
  unfold affineHierarchyResponse scalarFiniteResponse
  rw [he]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [scalarMomentSquare_eq_path_integral]

theorem scalarFiniteResponse_eq_hessian_prefix (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (i : Fin n) (x : ℝ) :
    scalarFiniteResponse n m v i x=
      rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x+
        ∑ j : Fin (n+1), if j.val ≤ i.val then hierarchyAtom n m 1 j*
          scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0 := by
  rw [scalarHierarchy_spin_hessian_overlap_sum n m v hm hmono]
  unfold scalarFiniteResponse
  have he : (∑ j : Fin (n+1), hierarchyAtom n m 1 j*
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x)=
      (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0)+
      (∑ j : Fin (n+1), if j.val ≤ i.val then hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i.val < j.val
    · simp only [ite_eq_left h,ite_eq_right (not_le.mpr h),add_zero]
    · simp only [ite_eq_right h,ite_eq_left (le_of_not_gt h),zero_add]
  linarith

end SK.Analytic

end
end

end OAI
