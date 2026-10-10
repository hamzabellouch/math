import OAI.Geometry.SurfaceImmersion.Atlas.ConvexPhaseDecomposition

namespace OAI

/-! Actual point-dependent phase bases. Outside the region of invertible
phase triples a fixed basis supplies harmless global values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def admissiblePhaseCovectors (P : PhaseBasis) (xi : Fin 3 → Base) : Prop :=
  (perturbedPhaseOperator P xi).IsInvertible ∧ ∀ i, xi i ≠ 0

lemma admissiblePhaseCovectors_eventually {P : PhaseBasis} {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) :
    ∀ᶠ z in 𝓝 xi, admissiblePhaseCovectors P z := by
  have hA : ∀ᶠ z in 𝓝 xi, (perturbedPhaseOperator P z).IsInvertible :=
    (perturbedPhaseOperator_smooth P).continuous.continuousAt.eventually hxi.1.eventually_nhds
  have hn : ∀ᶠ z in 𝓝 xi, ∀ i, z i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply i).continuousAt.eventually_ne (hxi.2 i)
  exact hA.and hn

def resolvedPhaseBasis (P : PhaseBasis) (xi : Fin 3 → Base) : PhaseBasis := by
  classical
  exact if h : admissiblePhaseCovectors P xi then
    ⟨xi,perturbedPhaseCoefficient P xi,perturbedPhase_decomposition P h.1,h.2⟩
  else P

lemma resolvedPhaseBasis_covectors (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) : (resolvedPhaseBasis P xi).ξ = xi := by
  simp only [resolvedPhaseBasis,dite_eq_left hxi]

lemma resolvedPhaseBasis_coefficients (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) (i : Fin 3) :
    (resolvedPhaseBasis P xi).Q i = perturbedPhaseCoefficient P xi i := by
  simp only [resolvedPhaseBasis,dite_eq_left hxi]

lemma resolvedPhaseBasis_coefficient_smoothAt (P : PhaseBasis)
    {xi : Base → Fin 3 → Base} {p : Base} (hxi : ContDiffAt ℝ ∞ xi p)
    (hp : admissiblePhaseCovectors P (xi p)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (resolvedPhaseBasis P (xi x)).Q i) p := by
  have he : (fun x => (resolvedPhaseBasis P (xi x)).Q i) =ᶠ[𝓝 p]
      (fun x => perturbedPhaseCoefficient P (xi x) i) := by
    have hnear : ∀ᶠ x in 𝓝 p, admissiblePhaseCovectors P (xi x) :=
      hxi.continuousAt.eventually (admissiblePhaseCovectors_eventually hp)
    filter_upwards [hnear] with x hx
    exact resolvedPhaseBasis_coefficients P hx i
  exact ((perturbedPhaseCoefficient_smoothAt P hp.1 i).comp p hxi).congr_of_eventuallyEq he

def convexSpatialBasis (P : PhaseBasis) (ell : Fin 3 → Base) (L : ℝ) (p : Base) : PhaseBasis :=
  resolvedPhaseBasis P (fun i => phaseDerivative (convexQuadraticPhase (ell i) L) p)

lemma convexSpatialBasis_coefficient_smoothAt (P : PhaseBasis) (ell : Fin 3 → Base) (L : ℝ)
    {p : Base}
    (hp : admissiblePhaseCovectors P (fun i => phaseDerivative (convexQuadraticPhase (ell i) L) p))
    (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (convexSpatialBasis P ell L x).Q i) p := by
  have hs : ContDiffAt ℝ ∞
      (fun x : Base => fun j : Fin 3 => phaseDerivative (convexQuadraticPhase (ell j) L) x) p := by
    apply contDiffAt_pi.mpr
    intro j
    simp only [convexQuadraticPhase_phaseDerivative]
    exact contDiffAt_const.add (contDiffAt_id.const_smul L)
  exact resolvedPhaseBasis_coefficient_smoothAt P hs hp i

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
