import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedGeometricSolver
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartBounds

namespace OAI

/-! Add a fixed polynomial perturbation to an existing geometric solver.
The polynomial bound is obtained uniformly from a fixed compact jet range
and fixed coordinate profiles, before the map and scales are supplied. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

namespace PolynomialSolveData

/-- Reuse all geometric and reconstruction data.  The uniform theorem below
provides the polynomial estimate required by this constructor. -/
def withPolynomial {n : ℕ} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {K : Compacts Base} {τ : ℝ} {s : ℝ≥0}
    (c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {O : Set LowJet}
    (hO : IsOpen O) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (hGO : Set.MapsTo (lowJet G) c₀.U O) (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hpoly : ∀ m Z, supportedWeightedSeminorm
      (chartSupport c₀.e (modeSupport K) c₀.supportChart) s m
      (phaseChartPolynomialOperator hO c₀.openU P hP hG hGO K c₀.supportU
        c₀.smoothPhase τ ε c₀.e c₀.smoothForward c₀.smoothInverse c₀.supportChart Z) ≤
      ε / τ ^ tensorLoss P * D m * supportedWeightedSeminorm
        (chartSupport c₀.e (modeSupport K) c₀.supportChart) s (m + tensorOrder P) Z) :
    PolynomialSolveData P ε G hG φ K τ s where
  U := c₀.U
  O := O
  openU := c₀.openU
  openO := hO
  smoothP := hP
  mapsG := hGO
  supportU := c₀.supportU
  smoothPhase := c₀.smoothPhase
  e := c₀.e
  smoothForward := c₀.smoothForward
  smoothInverse := c₀.smoothInverse
  supportChart := c₀.supportChart
  phase := c₀.phase
  smoothMap := c₀.smoothMap
  domain := c₀.domain
  C := c₀.C
  D := D
  J := c₀.J
  nonnegC := c₀.nonnegC
  nonnegD := hD
  oneLEJ := c₀.oneLEJ
  coordinates := c₀.coordinates
  coefficients := c₀.coefficients
  polynomial := hpoly

end PolynomialSolveData

theorem uniform_perturbed_solver_transfer {n : ℕ} {U : Set Base}
    {O Q : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (B F J I : ℕ → ℝ) (hB : ∀ m, 1 ≤ B m) (hF : ∀ m, 0 ≤ F m)
    (hJ : ∀ m, 1 ≤ J m) (hI : ∀ m, 1 ≤ I m)
    (hebound : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J m)
    (hibound : ∀ m j, 1 ≤ j → j ≤ m + 1 → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (G : Base → Space) (hG : ContDiff ℝ ∞ G) (φ : Base → ℝ)
        (τ ε : ℝ) (s : ℝ≥0),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      Set.MapsTo (lowJet G) U Q →
      (∀ m, WeightedBound U s (m + tensorOrder P) (B m) (lowJet G)) →
      (∀ m v, WeightedBound U s (m + tensorOrder P) (F m)
        (fun x => fderiv ℝ φ x (coordinateVector v))) →
      ∀ (c₀ : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s),
      c₀.U = U → c₀.e = e →
      ∃ c : PolynomialSolveData P ε G hG φ K τ s,
        c.U = U ∧ c.O = O ∧ c.e = e ∧ c.C = c₀.C ∧ c.D = D ∧ c.J = c₀.J := by
  obtain ⟨D,hD,hd⟩ := phaseChartPolynomialOperator_bounds hU hO hQ hQO
    P hP K hKU e he hi hKe B F J I hB hF hJ hI hebound hibound
  refine ⟨D,hD,?_⟩
  intro G hG φ τ ε s hτ hs hτs hs1 hε hε1 hGQ hGb hφb c₀ hU₀ he₀
  subst U
  subst e
  let c := c₀.withPolynomial P ε hO hP (fun _ hx => hQO (hGQ hx)) D hD
    (hd G φ hG c₀.smoothPhase hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb)
  exact ⟨c,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
