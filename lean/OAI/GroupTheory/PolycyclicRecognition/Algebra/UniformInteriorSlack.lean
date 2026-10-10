import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordInteriorSlack
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformSelection

namespace OAI

/-! # Interior slack uniform in the sampled chart position -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology BigOperators

variable {I L G A : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A common finite-word envelope gives uniform decay, even if the family
parameter has no regularity. In particular it controls every compact set of
sampled chart positions. -/
theorem rescaled_word_conjugation_tendstoUniformly
    {Z : Type*} [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {m k₀ c₀ : ℕ}
    (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hnil : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ)
    (β : ℝ → WordBasisSelections X (boundedBracketWords k₀))
    (hβ : ∀ r, IsMaximizingColumnBasis
      (wordListCoordinates X (boundedBracketWords k₀) b₀)
      (fun w => bracketWordExponent s w) (β r).val)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c₀ 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {δ c lo hi K U : ℝ}
    (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (m : ℝ) * hi < c * lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → boundedBracketWords (I := I) k₀ → ℝ)
    (u : ℝ → Z → boundedBracketWords (I := I) k₀ → ℝ)
    (hkcoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |k r w| ≤ K * Real.exp (r * ((1 + δ) * bracketWordExponent s w + ε r)))
    (hucoeff : ∀ᶠ r : ℝ in atTop, ∀ z w,
      |u r z w| ≤ U * Real.exp (r * ((1 - c * δ) * bracketWordExponent s w + ε r))) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
      (fun i => bracketWordExponent s ((β r).val i)) r
    let x := fun r => (b r).equivFun
      (∑ w, k r w • evalBracketWord X w)
    let y := fun r z => (b r).equivFun
      (∑ w, u r z w • evalBracketWord X w)
    TendstoUniformly (fun r z => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) (x r) (y r z)) (-(x r))) (fun _ => 0) atTop := by
  dsimp only
  apply tendstoUniformly_const_of_all_selections
  intro z
  exact rescaled_word_conjugation_tendsto_zero X hk hnil b₀ s β hβ
    Exp hinj hneg a hm j ρ hρ hmatch hδ hc hhi hK hU hcost hgap ε hε
    k (fun r => u r (z r)) hkcoeff
    (hucoeff.mono (fun r hr w => hr (z r) w))

end PolycyclicRecognition

end

end OAI
