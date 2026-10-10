import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedGenerator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedSpectralStability
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteGeneratorNoJordan

namespace OAI

/-! The actual linearized evolution splits into a decaying kernel and a diagonal symmetry generator. -/

open Filter Topology
open scoped NNReal
namespace DefocusingNLS
open ProfileCertificate

def HasSymmetryContourGenerator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : ℝ≥0 → E →L[ℂ] E) : Prop :=
    ∃ P : E →L[ℂ] E, IsIdempotentElem P ∧ FiniteDimensional ℂ P.range ∧
      ∃ hcomm : ∀ s, Commute (S s) P,
      (∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ s : ℝ≥0, ∀ u, P u=0 →
        ‖S s u‖ ≤ D * Real.exp (-δ*(s : ℝ)) * ‖u‖) ∧
      ∃ G : P.range →L[ℂ] P.range,
        (∀ s, projectionSemigroupRestriction S P hcomm s=NormedSpace.exp ((s : ℝ) • G)) ∧
        (∀ (lam : ℂ) (u : P.range), u ≠ 0 → G u=lam • u → lam=0 ∨ lam=1 ∨ lam=1/2) ∧
        (⨆ lam : ℂ, Module.End.eigenspace G.toLinearMap lam)=⊤

theorem radialMatched_exists_symmetry_generator (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
        (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z=0) →
      ∃ N : ℕ, ∃ hk : 8 < ((N+1 : ℕ) : ℝ),
        let a := radialShootingA n
        let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
        let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
        let b := radialShootingB (profileMatchingParameter z)
        let m := n+radialInnerShootingThreshold
        ∃ q : HomogeneousY a ((N+1 : ℕ) : ℝ),
          (∀ x : EuclideanSpace ℝ (Fin 12),
            homogeneousPhysicalCLM a ((N+1 : ℕ) : ℝ) ha ha1 hk q x=radialMatchedCartesian n z x) ∧
          HasSymmetryContourGenerator
            (homogeneousComplexLinearizedStep a b ((N+1 : ℕ) : ℝ) ha ha1 hk m q) := by
  filter_upwards [radialMatched_exists_finite_generator,
    radialMatched_contour_spectral_stability hRou] with n hn hs z hX hz
  obtain ⟨N,hk,q,hq,P,hP,hfin,hcomm,hdecay,G,hG,hgap⟩ := hn z hX hz
  obtain ⟨hspec,hJordan⟩ := hs z hX hz (N+1) _ _ hk q hq P hcomm hfin G hG
  have hJ : ∀ (lam : ℂ) (v w : P.range), w ≠ 0 → G w=lam • w → G v ≠ lam • v+w := by
    intro lam v w hw he
    exact hJordan lam v w hw he (hgap lam w hw he).le
  let : FiniteDimensional ℂ P.range := hfin
  refine ⟨N,hk,q,hq,P,hP,hfin,hcomm,hdecay,G,hG,?_,?_⟩
  · intro lam w hw he
    exact hspec lam w hw he (hgap lam w hw he).le
  · exact generator_eigenspaces_span G.toLinearMap hJ

end DefocusingNLS

end OAI
