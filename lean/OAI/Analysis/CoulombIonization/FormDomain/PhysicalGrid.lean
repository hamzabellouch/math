import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.PressureWeak
import OAI.Analysis.CoulombIonization.FieldAnalysis.PhysicalGridMeasurable

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators unitInterval ContDiff

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma rotationIsometry_inv (R : CubeRotation) : rotationIsometry R⁻¹ = (rotationIsometry R).symm :=
  map_inv Unitary.linearIsometryEquiv R

lemma flatRotation_symm_coordinates (R : Space ≃ₗᵢ[ℝ] Space) (x : Configuration N) :
    (flatRotation R).symm (configurationCoordinates N x) =
      configurationCoordinates N (fun i => R.symm (x i)) := by
  apply (flatRotation R).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext q
  change x q.1 q.2 = R (R.symm (x q.1)) q.2
  rw [LinearIsometryEquiv.apply_symm_apply]

lemma physicalGridPressure_eq {b : ℝ} (hb : 0 < b) (R : CubeRotation)
    (t : Fin 3 → I) (x : Configuration N) :
    physicalGridPressure b R t x =
      rotatedGridPressure b (fun a => b*(t a:ℝ)) (rotationIsometry R) (configurationCoordinates N x) := by
  unfold physicalGridPressure rotatedGridPressure gridPressure
  rw [flatRotation_symm_coordinates]
  congr 1
  congr 1
  funext i a
  change ⌊(rotationIsometry R⁻¹ (b⁻¹ • x i)) a-(t a:ℝ)⌋ =
    ⌊b⁻¹*((rotationIsometry R).symm (x i) a-b*(t a:ℝ))⌋
  rw [rotationIsometry_inv,map_smul]
  congr 1
  change b⁻¹*((rotationIsometry R).symm (x i) a)-(t a:ℝ) = _
  field_simp [hb.ne']

lemma physicalGridPressure_value_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (b : ℝ) (R : CubeRotation) (t : Fin 3 → I) (s : Spins N) :
    Integrable (fun x => physicalGridPressure b R t x*‖ψ.value s x‖^2) := by
  apply (hψ.1 s).norm.integrable_sq.bdd_mul (physicalGridPressure_fixed_measurable b R t).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    change ‖physicalGridPressure b R t x‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (physicalGridPressure_nonneg _ _ _ _)]
    exact physicalGridPressure_le _ _ _ _)

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann
variable {N : ℕ}

def formDensity (ψ : FormVector N) (x : Configuration N) : ℝ := ∑ s, ‖ψ.value s x‖^2
lemma formDensity_nonneg (ψ : FormVector N) (x : Configuration N) : 0 ≤ formDensity ψ x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)
lemma SobolevFermion.formDensity_integrable {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    Integrable (formDensity ψ) := integrable_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)
lemma SobolevFermion.integral_formDensity {ψ : FormVector N} (hψ : SobolevFermion ψ) :
    (∫ x, formDensity ψ x) = formMass ψ :=
  integral_finsetSum _ (fun s _ => (hψ.1 s).norm.integrable_sq)

theorem SobolevFermion.neumann_physical_grid {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (R : CubeRotation) (t : Fin 3 → I) :
    tfKinetic*(∫ x, physicalGridPressure b R t x*formDensity ψ x) ≤ formKinetic ψ+
      b⁻¹^2*neumannRemainderConstant*((N:ℝ)^(4/3:ℝ)+(N:ℝ))*formMass ψ := by
  have hm (s : Spins N) : MemLp (cartesianValue ψ s) 2 :=
    (hψ.1 s).comp_measurePreserving (configurationCoordinates_symm_preserving N)
  have hg (s : Spins N) (q : Fin N × Fin 3) : MemLp (cartesianGradient ψ s q) 2 :=
    (hψ.2.1 s q.1 q.2).comp_measurePreserving (configurationCoordinates_symm_preserving N)
  have hh := neumann_rotated_weak hm hg hψ.cartesian_anti hψ.cartesian_weak hb
    (fun a => b*(t a:ℝ)) (rotationIsometry R)
  have he (s : Spins N) :
      (∫ x, rotatedGridPressure b (fun a => b*(t a:ℝ)) (rotationIsometry R) x*‖cartesianValue ψ s x‖^2) =
        ∫ x : Configuration N, physicalGridPressure b R t x*‖ψ.value s x‖^2 := by
    rw [←integral_configurationCoordinates (fun x => rotatedGridPressure b (fun a => b*(t a:ℝ)) (rotationIsometry R) x*‖cartesianValue ψ s x‖^2)]
    simp only [cartesianValue,ContinuousLinearEquiv.symm_apply_apply,←physicalGridPressure_eq hb]
  have heg (s : Spins N) (q : Fin N × Fin 3) :
      (∫ x, ‖cartesianGradient ψ s q x‖^2) = ∫ x, ‖ψ.gradient s q.1 q.2 x‖^2 :=
    integral_configurationCoordinates_symm (fun x => ‖ψ.gradient s q.1 q.2 x‖^2)
  have hem (s : Spins N) : (∫ x, ‖cartesianValue ψ s x‖^2) = ∫ x, ‖ψ.value s x‖^2 :=
    integral_configurationCoordinates_symm (fun x => ‖ψ.value s x‖^2)
  simp_rw [he,heg,hem] at hh
  unfold formDensity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun s _ => physicalGridPressure_value_integrable hψ b R t s)]
  simpa only [Fintype.sum_prod_type,formKinetic,formMass] using hh

end CoulombAtom

end

end OAI
