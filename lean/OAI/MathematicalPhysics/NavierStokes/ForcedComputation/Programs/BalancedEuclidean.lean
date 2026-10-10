import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactEuclideanEnergy
import OAI.MathematicalPhysics.AlternatingFlow.DerivativeBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ResidualScaling

namespace OAI

/-! The compact Euclidean solution uses the prescribed coordinate residual.
The coordinate change commutes with all spatial derivatives and with the
right time derivative on the nonnegative time axis. -/

noncomputable section
namespace ForcedComputation.CompactEuclidean
open ShearFlows Set RapidForcing.CompactEmbedding
open scoped ContDiff

theorem velocity_residual {V : ShearFlows.Velocity} (hV : ContDiff ℝ ∞ V)
    (ν : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : AlternatingNS.Space) :
    velocity (ForcedComputation.residual ν V) t x =
      AlternatingNS.residual ν (velocity V) t x := by
  let U := velocity V
  have hU := velocity_smooth hV
  have ht' := piField_timeDerivative hU ht (piCoordinates x)
  have ha := piField_advection U t (piCoordinates x)
  have hl := piField_laplacian U t (piCoordinates x)
  rw [piField_velocity] at ht' ha hl
  simp only [ContinuousLinearEquiv.symm_apply_apply] at ht' ha hl
  have ha' : ShearFlows.advection (fun y => V (t,y)) (piCoordinates x) =
      piCoordinates (AlternatingNS.advection U t x) := by
    rw [AlternatingNS.Bounds.advection_eq_sum]
    simpa only [RapidForcing.advection, RapidForcing.spatialD, RapidForcing.basis,
      AlternatingNS.dx, AlternatingNS.e] using ha
  apply piCoordinates.injective
  change ForcedComputation.residual ν V (t,piCoordinates x) =
    piCoordinates (AlternatingNS.residual ν U t x)
  rw [ForcedComputation.residual, AlternatingNS.residual, map_sub, map_add, map_smul,
    ht', ha']
  congr 2

theorem compact_prescribed_solution {ν : ℝ} (hν : 0 < ν)
    {V : ShearFlows.Velocity} (hV : ContDiff ℝ ∞ V)
    {K : Set ShearFlows.Space} (hK : IsCompact K)
    (hs : ∀ t, Function.support (fun x => V (t,x)) ⊆ K)
    (h0 : ∀ x, V (0,x) = 0) (hd : Solenoidal V) :
    let U := velocity V
    let f := velocity (ForcedComputation.residual ν V)
    AlternatingNS.NavierStokes ν f U (fun _ _ => 0) ∧
    AlternatingNS.EnergyClass U (fun _ _ => 0) ∧
    ∀ v p, IsEnergySolutionModuloConstants ν f v p →
      ∃ c : ℝ → ℝ, ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = c t := by
  dsimp only
  obtain ⟨hsol,hE,_⟩ := compact_velocity_solution hν hV hK hs h0 hd
  have hsol' : AlternatingNS.NavierStokes ν (velocity (ForcedComputation.residual ν V))
      (velocity V) (fun _ _ => 0) := by
    refine ⟨hsol.1,hsol.2.1,?_⟩
    intro t ht x
    simpa only [velocity_residual hV ν ht x] using hsol.2.2 t ht x
  exact ⟨hsol',hE,fun v p hv => energy_unique_modulo_constants hν.le hsol' hE hv⟩

end ForcedComputation.CompactEuclidean

end

end OAI
