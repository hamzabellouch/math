import OAI.Probability.SLE.Geometry.WaypointRouteProbability

namespace OAI

/-! Finite-window consequences of published conformal invariance of planar
Brownian motion: G. F. Lawler, *Conformally Invariant Processes in the Plane*,
AMS (2005), Theorem 2.2. The half-plane harmonic-measure formula is recorded
in Lawler--Werness, Ann. Probab. 41 (2013), 1513--1555, §2.1, unnumbered
display for S-hat (electronic reprint p. 5, DOI 10.1214/11-AOP695).

Only finite exits during one unit Brownian window are used. Time is
deterministically rescaled from [0,1] to [0,3]. The input states actual
map-out limits and exit-event upper bounds, with no ribbon hypotheses and
no positive lower probability or angle estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target RibbonCoordinates

def UnitWindowFirstExit (D : Set ℂ) (ζ : ℝ → ℂ) (τ : ℝ) : Prop :=
  τ ∈ Ioc (0 : ℝ) 3 ∧ ζ τ ∉ D ∧ MapsTo ζ (Ico 0 τ) D

def unitWindowExitArc (D : Set ℂ) (g : ℂ → ℂ) (w : ℂ) (side : ℝ) :
    Set (Driver × Driver) :=
  {b | ∃ τ : ℝ, UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ ∧
    ∃ x : ℝ, 0 < side * x ∧
      Tendsto (fun t => g (physicalUnitBrownianPath w b t)) (𝓝[<] τ) (𝓝 (x : ℂ))}

def PublishedHalfPlaneConformalExitLaw : Prop :=
  ∀ (W : WienerLaw), IsWiener W → ∀ (D : Set ℂ) (g f : ℂ → ℂ),
    IsOpen D → D ⊆ upperHalfPlane →
    DifferentiableOn ℂ g D → DifferentiableOn ℂ f upperHalfPlane →
    MapsTo g D upperHalfPlane → MapsTo f upperHalfPlane D →
    (∀ z ∈ D, f (g z) = z) → (∀ z ∈ upperHalfPlane, g (f z) = z) →
    ∀ w ∈ D,
      (∀ᵐ b ∂(W.prod W), ∀ τ : ℝ,
        UnitWindowFirstExit D (physicalUnitBrownianPath w b) τ →
          ∃ x : ℝ, x ≠ 0 ∧
            Tendsto (fun t => g (physicalUnitBrownianPath w b t))
              (𝓝[<] τ) (𝓝 (x : ℂ))) ∧
      (W.prod W) (unitWindowExitArc D g w (-1)) ≤
        ENNReal.ofReal ((g w).arg / Real.pi) ∧
      (W.prod W) (unitWindowExitArc D g w 1) ≤
        ENNReal.ofReal (1 - (g w).arg / Real.pi)

end SLEExactGauge

end

end OAI
