import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPeriodizationNS
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.PeriodicCalculus
import OAI.MathematicalPhysics.RapidForcing.JointSmoothness

namespace OAI

/-! Coordinate change from the Euclidean rapid-field convention to the
coordinate convention used for periodic fluid fields and cube integrals. -/

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RapidForcing.CompactEmbedding

def piCoordinates : Space ≃L[ℝ] ShearFlows.Space :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

@[simp] theorem piCoordinates_apply (x : Space) (i : Fin 3) :
    piCoordinates x i = x i := rfl

@[simp] theorem piCoordinates_symm_apply (x : ShearFlows.Space) (i : Fin 3) :
    piCoordinates.symm x i = x i := rfl

@[simp] theorem piCoordinates_basis (i : Fin 3) :
    piCoordinates (basis i) = ShearFlows.basis i := by
  ext j
  simp [basis, ShearFlows.basis, piCoordinates, Pi.single_apply]

@[simp] theorem piCoordinates_symm_basis (i : Fin 3) :
    piCoordinates.symm (ShearFlows.basis i) = basis i := by
  apply piCoordinates.injective
  simp

@[simp] theorem piCoordinates_symm_lattice (k : Fin 3 → ℤ) :
    piCoordinates.symm (ShearFlows.latticeVector 1 k) = latticeVector k := by
  ext i
  simp [ShearFlows.latticeVector]

def piField (f : Field Space) : ShearFlows.Velocity :=
  fun p => piCoordinates (f p.1 (piCoordinates.symm p.2))

theorem piField_smooth {f : Field Space}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) : ContDiff ℝ ∞ (piField f) :=
  piCoordinates.contDiff.comp
    (hf.comp (contDiff_fst.prodMk (piCoordinates.symm.contDiff.comp contDiff_snd)))

theorem piField_derivative (f : Field Space) (t : ℝ) (x : ShearFlows.Space)
    (i : Fin 3) :
    ShearFlows.derivative (fun y => piField f (t, y)) i x =
      piCoordinates (spatialD i f t (piCoordinates.symm x)) := by
  change fderiv ℝ (piCoordinates ∘ (f t ∘ piCoordinates.symm)) x
    (ShearFlows.basis i) = _
  rw [piCoordinates.comp_fderiv, piCoordinates.symm.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    piCoordinates_symm_basis, spatialD]

theorem piField_divergence (f : Field Space) (t : ℝ) (x : ShearFlows.Space) :
    ShearFlows.divergence (fun y => piField f (t, y)) x =
      divergence f t (piCoordinates.symm x) := by
  simp only [ShearFlows.divergence, piField_derivative, piCoordinates_apply, divergence]

theorem piField_advection (f : Field Space) (t : ℝ) (x : ShearFlows.Space) :
    ShearFlows.advection (fun y => piField f (t, y)) x =
      piCoordinates (advection f t (piCoordinates.symm x)) := by
  have hex : piField f (t, x) =
      ∑ i, piField f (t, x) i • ShearFlows.basis i :=
    (ShearFlows.sum_coordinates_basis _).symm
  unfold ShearFlows.advection
  change (fderiv ℝ (fun y => piField f (t, y)) x) (piField f (t, x)) = _
  rw [hex, map_sum]
  simp only [map_smul]
  change (∑ i, piField f (t, x) i •
    ShearFlows.derivative (fun y => piField f (t, y)) i x) = _
  simp_rw [piField_derivative]
  simp only [advection, map_sum, map_smul, piField, piCoordinates_apply]

theorem piField_laplacian (f : Field Space) (t : ℝ) (x : ShearFlows.Space) :
    ShearFlows.laplacian (fun y => piField f (t, y)) x =
      piCoordinates (laplace f t (piCoordinates.symm x)) := by
  have hd (i : Fin 3) : ShearFlows.derivative (fun y => piField f (t, y)) i =
      fun y => piField (spatialD i f) (t, y) := funext (fun y => piField_derivative f t y i)
  unfold ShearFlows.laplacian
  simp only [hd]
  change (∑ i, ShearFlows.derivative (fun y => piField (spatialD i f) (t, y)) i x) = _
  simp only [piField_derivative, laplace, map_sum]

theorem piField_timeDerivative {f : Field Space}
    (hf : ContDiff ℝ ∞ (Function.uncurry f)) {t : ℝ} (ht : 0 ≤ t)
    (x : ShearFlows.Space) :
    ShearFlows.timeDerivative (piField f) t x =
      piCoordinates (timeD f t (piCoordinates.symm x)) := by
  rw [timeD_eq_ordinary hf ht]
  change fderiv ℝ (piCoordinates ∘ (fun s : ℝ => f s (piCoordinates.symm x))) t 1 =
    piCoordinates (fderiv ℝ (fun s : ℝ => f s (piCoordinates.symm x)) t 1)
  rw [piCoordinates.comp_fderiv]
  rfl

theorem piField_periodic {f : Field Space}
    (hf : ∀ t x k, f t (x + latticeVector k) = f t x) :
    ShearFlows.SpatiallyPeriodic 1 (piField f) := by
  intro t x k
  unfold piField
  rw [map_add, piCoordinates_symm_lattice, hf]

theorem piField_periodic_extension (f : Field Space) :
    ShearFlows.SpatiallyPeriodic 1 (piField (periodic f)) :=
  piField_periodic (periodic_add_lattice f)

end RapidForcing.CompactEmbedding

end

end OAI
