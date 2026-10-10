import OAI.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

variable {L M σ τ X Ω T : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype Ω] [Fintype T] {d : ℕ}
    (D : RationalFilteredNilmanifold L 0 d) (G : NilpotentLieFiltration M 0)

theorem exists_step_zero_external_marked_candidate_preserving_scores
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ) (v : τ → ℕ)
    (mark : G.realification.PolynomialOrbit w)
    (observable : X → D.Space → ℂ)
    (localOrbit : Ω → D.filtration.realification.PolynomialOrbit v)
    (outer : FiniteProbabilityWeights Ω) (retained : Finset Ω)
    (localLaw : Ω → FiniteProbabilityWeights T)
    (physical : Ω → T → X) (ambientPoint : Ω → T → σ → ℝ)
    (localPoint : Ω → T → τ → ℝ) (input : X → ℝ)
    (massThreshold scoreThreshold : ℝ)
    (hmass : massThreshold ≤ outer.mass retained)
    (hscore : ∀ a ∈ retained, scoreThreshold ≤ (localLaw a).mean (fun t =>
      input (physical a t) * (observable (physical a t) (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitRealEval v (localPoint a t) (localOrbit a)))).re)) :
    ∃ ambient : D.filtration.realification.PolynomialOrbit w,
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) ambient.log = mark.log ∧
      massThreshold ≤ outer.mass retained ∧
      (∀ a, (localLaw a).mean (fun t =>
        input (physical a t) * (observable (physical a t) (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitRealEval w (ambientPoint a t) ambient))).re) =
        (localLaw a).mean (fun t =>
        input (physical a t) * (observable (physical a t) (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitRealEval v (localPoint a t) (localOrbit a)))).re)) ∧
      ∀ a ∈ retained, scoreThreshold ≤ (localLaw a).mean (fun t =>
        input (physical a t) * (observable (physical a t) (QuotientGroup.mk
          (D.filtration.realification.polynomialOrbitRealEval w (ambientPoint a t) ambient))).re) := by
  obtain ⟨ambient, hmark, heval⟩ :=
    D.exists_step_zero_external_marked_candidate G φ w v mark observable localOrbit
  have hmean (a) : (localLaw a).mean (fun t =>
      input (physical a t) * (observable (physical a t) (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitRealEval w (ambientPoint a t) ambient))).re) =
      (localLaw a).mean (fun t =>
      input (physical a t) * (observable (physical a t) (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitRealEval v (localPoint a t) (localOrbit a)))).re) := by
    congr 1
    funext t
    rw [heval a (physical a t) (ambientPoint a t) (localPoint a t)]
  refine ⟨ambient, hmark, hmass, hmean, ?_⟩
  intro a ha
  rw [hmean]
  exact hscore a ha

end Erdos3.RationalFilteredNilmanifold

end

end OAI
