import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinSiteTensorization
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchy
import OAI.Probability.SKBarriers.Scalar.ScalarCurvature

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarSpinTerminal (z : ℝ) : ℝ := Real.log (2*Real.cosh z)

def scalarSpinField (n : ℕ) (v : Fin n → ℝ) : ParameterSpace n →L[ℝ] ℝ :=
  parameter n+coordinateLinear n v

theorem scalarSpinTerminal_affine (n : ℕ) (v : Fin n → ℝ) :
    (fun z => scalarSpinTerminal (parameter n z+∑ j, v j*coordinateProjection n j z)) =
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
  funext z
  rw [affineLogPartition_bool]
  simp only [scalarSpinTerminal,scalarSpinField,add_apply,coordinateLinear_apply]

theorem scalarHierarchy_spin_eq (n : ℕ) (m v : Fin n → ℝ) :
    scalarHierarchy n m v scalarSpinTerminal =
      hierarchyPressure n m (affineLogPartition (fun _ : Bool => 0)
        (fun b => spin b • scalarSpinField n v)) := by
  rw [← scalarSpinTerminal_affine]
  exact (hierarchyPressure_scalar_linear n m v scalarSpinTerminal id).symm

theorem scalarHierarchy_spin_regular (n : ℕ) (m v : Fin n → ℝ) :
    BoundedDerivs (scalarHierarchy n m v scalarSpinTerminal) := by
  rw [scalarHierarchy_spin_eq]
  exact hierarchyPressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs _ _)

theorem hierarchy_spin_curvature (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (hm : ∀ i, m i ∈ Set.Icc 0 1)
    (hH : ∀ z, 0 < fderiv ℝ (fderiv ℝ f) z (parameterAxis n) (parameterAxis n) ∧
      fderiv ℝ (fderiv ℝ f) z (parameterAxis n) (parameterAxis n) ≤
        1-(fderiv ℝ f z (parameterAxis n))^2) (x : ℝ) :
    0 < fderiv ℝ (fderiv ℝ (hierarchyPressure n m f)) x 1 1 ∧
      fderiv ℝ (fderiv ℝ (hierarchyPressure n m f)) x 1 1 ≤
        1-(fderiv ℝ (hierarchyPressure n m f) x 1)^2 := by
  induction n with
  | zero => exact hH x
  | succ n ih =>
    apply ih (fun i => m i.castSucc) _ (hf.gaussianStep _) (fun i => hm i.castSucc)
    intro z
    apply gaussianStep_spin_curvature hf (hm (Fin.last n)) (parameterAxis n) z
    intro y
    exact hH (z,y)

theorem scalarHierarchy_spin_derivative_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Set.Icc 0 1) (z : ℝ) :
    let f := scalarHierarchy n m v scalarSpinTerminal
    |fderiv ℝ f z 1| ≤ 1 ∧
      0 < fderiv ℝ (fderiv ℝ f) z 1 1 ∧
      fderiv ℝ (fderiv ℝ f) z 1 1 ≤ 1-(fderiv ℝ f z 1)^2 := by
  dsimp only
  have hL : scalarSpinField n v (parameterAxis n) = 1 := by
    simp [scalarSpinField,coordinateLinear_axis]
  have H := hierarchy_spin_curvature n m
    (affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v))
    (affineLogPartition_boundedDerivs _ _) hm (fun x => by
      have H := affineLogPartition_bool_curvature (scalarSpinField n v) x (parameterAxis n) hL
      exact ⟨H.1,H.2.le⟩) z
  rw [← scalarHierarchy_spin_eq] at H
  refine ⟨?_,H⟩
  exact (sq_le_one_iff_abs_le_one _).mp (by linarith [H.1])

def siteScalarCoefficients {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N)
    (t : Fin (blockDimension D N k)) : ℝ :=
  ∑ b, if fieldIndex D N k b i = t then v b else 0

theorem siteScalarCoefficients_field {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (z : ParameterSpace (blockDimension D N k)) :
    (∑ t, siteScalarCoefficients (D := D) v i t*coordinateProjection (blockDimension D N k) t z) =
      siteField (D := D) v i z := by
  simp only [siteScalarCoefficients,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [siteField,sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem hierarchyPressure_site_scalar {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    hierarchyPressure (blockDimension D N k) (blockMass D N k)
      (siteLogPartition (D := D) v i) =
    fun _ => scalarHierarchy (blockDimension D N k) (blockMass D N k)
      (siteScalarCoefficients (D := D) v i) scalarSpinTerminal 0 := by
  have he : siteLogPartition (D := D) v i = fun z =>
      scalarSpinTerminal (0+∑ t, siteScalarCoefficients (D := D) v i t*
        coordinateProjection (blockDimension D N k) t z) := by
    funext z
    rw [zero_add,siteScalarCoefficients_field]
    exact affineLogPartition_bool (siteField (D := D) v i) z
  rw [he]
  exact hierarchyPressure_scalar_linear _ _ _ scalarSpinTerminal (fun _ => 0)
end SK.Analytic

end
end

end

end OAI
