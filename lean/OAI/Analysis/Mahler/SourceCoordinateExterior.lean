import OAI.Analysis.Mahler.SourceRealExterior
import OAI.Analysis.Mahler.SourceTopCoordinates

namespace OAI

open ContinuousAlternatingMap
namespace Mahler
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem extDeriv_sourceCoordinateForm {d : ℕ}
    (Ψ : (Fin d → ℝ) ≃L[ℝ] E) {u : E → ℂ} {x : Fin d → ℝ}
    (hu : ContDiffAt ℝ 3 u (Ψ x)) (k : ℕ) (v : Fin ((2*k+1)+1) → (Fin d → ℝ)) :
    extDeriv (sourceCoordinateForm Ψ u k) x v =
      (wedgePower (extDeriv (oneForm (dcLinear u)) (Ψ x)).toAlternatingMap (k+1)
        (fun s => Ψ (v (sourceTopSlots k s)))).re := by
  have hω := (contDiffAt_sourceRealBoundaryForm hu k).differentiableAt one_ne_zero
  have hp := extDeriv_pullback hω (Ψ.contDiff.contDiffAt : ContDiffAt ℝ 2 Ψ x) (by norm_num)
  have hd (y : Fin d → ℝ) : fderiv ℝ Ψ y = Ψ.toContinuousLinearMap := Ψ.hasFDerivAt.fderiv
  simp only [hd] at hp
  change extDeriv (fun y => (sourceRealBoundaryForm u k (Ψ y)).compContinuousLinearMap
    Ψ.toContinuousLinearMap) x v = _
  rw [hp]
  exact extDeriv_sourceRealBoundaryForm hu k (fun i => Ψ (v i))

variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

theorem MassHypotheses.coordinate_energy_extDeriv (h : MassHypotheses (k+1) N m U f G)
    {x : Fin ((2*k+1)+1) → ℝ} (hx : sourceCoordinates k x ∈ U) :
    extDeriv (sourceCoordinateForm (sourceCoordinates k) (energy f) k) x
      (MahlerStokes.coordinateBasis ((2*k+1)+1)) = massDensity f (sourceCoordinates k x) := by
  rw [extDeriv_sourceCoordinateForm _ (h.contDiffAt_energy hx 3)]
  simp only [sourceCoordinates_top_basis]
  exact (h.massDensity_eq_topForm hx).symm

/-- The punctured Stokes integrand is nonnegative, using
the nonnegative logarithmic complex Hessian in the positive frame. -/
theorem MassHypotheses.coordinate_log_extDeriv_nonneg (h : MassHypotheses (k+1) N m U f G)
    {x : Fin ((2*k+1)+1) → ℝ} (hx : sourceCoordinates k x ∈ U) (hne : x ≠ 0) :
    0 ≤ extDeriv (sourceCoordinateForm (sourceCoordinates k) (logTau f) k) x
      (MahlerStokes.coordinateBasis ((2*k+1)+1)) := by
  have hz : sourceCoordinates k x ≠ 0 := by
    intro he
    apply hne
    exact (sourceCoordinates k).injective (by simpa using he)
  rw [extDeriv_sourceCoordinateForm _ (h.contDiffAt_logTau hx hz 3)]
  simp only [sourceCoordinates_top_basis]
  simpa only [complexCoordinates_wedge_basis] using source_log_top_coefficient_nonneg h hx hz

end
end Mahler

end OAI
