import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOneAtom
import OAI.Probability.SKBarriers.Hierarchy.RootSusceptibilitySum
import OAI.Probability.SKBarriers.Calculus.ParameterMomentSquare

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSpinParameter_eq (n : ℕ) (v : Fin n → ℝ) :
    scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0=
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
  rw [← scalarSpinTerminal_affine]
  funext z
  simp only [scalarParameterTerminal,zero_add,coordinateLinear_apply]

theorem scalarSpinRoot_gradient (n : ℕ) (v : Fin n → ℝ) :
    rootGradient n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v))=
      scalarParameterTerminal n v (fun a y => scalarMagnetization (a+y)) 0 := by
  rw [← scalarSpinParameter_eq]
  funext z
  have HE : scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0=
      fun z => scalarSpinTerminal (scalarSpinField n v z) := by
    funext z
    simp only [scalarParameterTerminal,zero_add,scalarSpinField,add_apply]
  have HD := (scalarSpinTerminal_hasDerivAt (scalarSpinField n v z)).comp_hasFDerivAt z
    (scalarSpinField n v).hasFDerivAt
  have HD' : fderiv ℝ (fun z => scalarSpinTerminal (scalarSpinField n v z)) z=
      scalarMagnetization (scalarSpinField n v z) • scalarSpinField n v := by
    convert HD.fderiv using 1; rfl
  rw [rootGradient,HE,HD']
  simp only [smul_apply,smul_eq_mul,scalarSpinField,add_apply,parameter_axis,
    coordinateLinear_axis,add_zero,mul_one,scalarParameterTerminal,zero_add]

theorem scalarStepAverage_translate (m v c : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    scalarStepAverage m v (fun t => f (c+t)) (fun t => g (c+t)) x=
      scalarStepAverage m v f g (c+x) := by
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw,add_assoc]

theorem scalarHierarchyAverage_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v (fun y => f (c+y)) (fun y => g (c+y)) x=
      scalarHierarchyAverage n m v f g (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchyAverage]
    rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
    exact ih _ _ _ _

theorem scalarMomentSquare_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (j : Fin (n+1)) (c x : ℝ) :
    scalarMomentSquare n m v (fun y => f (c+y)) (fun y => g (c+y)) j x=
      scalarMomentSquare n m v f g j (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last]
      exact scalarHierarchyAverage_translate (n+1) m v f (fun x => (g x)^2) c x
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
      exact ih _ _ _ _ j

theorem scalarHierarchy_spin_hessian_overlap_sum (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (x : ℝ) :
    rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x=
      1-∑ j, hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
  rw [scalarHierarchy_spin_eq,hierarchyPressure_rootHessian_overlap_sum n m hm hmono
    (affineLogPartition_boundedDerivs _ _) (scalarSpinRoot_curvature n v)
    (scalarSpinRoot_curvature_eq n v)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
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

end SK.Analytic

end
end

end OAI
