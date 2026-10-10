import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformInteriorSlack
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxWordExpansion

namespace OAI

/-! # Interior slack directly from membership in rescaled boxes -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology BigOperators

variable {I L G A Z : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual logarithms of an enlarged suffix and an interior family
satisfy the uniform conjugation conclusion. The finite word expansions
needed by interior slack are constructed here from the two box bounds. -/
theorem rescaled_box_conjugation_tendstoUniformly
    [Nonempty (Fin (finrank ℝ L))]
    (X : I → L) {m k₀ c₀ : ℕ}
    (hk : lowerCentralSeries ℝ L L k₀ = ⊥)
    (hnil : lowerCentralSeries ℝ L L (m + 1) = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
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
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi)
    (hcost : ∀ w : boundedBracketWords (I := I) k₀,
      lo ≤ bracketWordExponent s w ∧ bracketWordExponent s w ≤ hi)
    (hgap : (m : ℝ) * hi < c * lo)
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℝ → L) (u : ℝ → Z → L)
    (hkbox : ∀ᶠ r : ℝ in atTop,
      ‖(exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
        (fun i => (1 + δ) * bracketWordExponent s ((β r).val i)) r).equivFun (k r)‖ ≤
          Real.exp (r * ε r))
    (hubox : ∀ᶠ r : ℝ in atTop, ∀ z,
      ‖(exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
        (fun i => (1 - c * δ) * bracketWordExponent s ((β r).val i)) r).equivFun (u r z)‖ ≤
          Real.exp (r * ε r)) :
    let b := fun r => exponentialRescaleBasis
      (WordBasisSelections.basis X (boundedBracketWords k₀) (β r))
      (fun i => bracketWordExponent s ((β r).val i)) r
    TendstoUniformly (fun r z => dynkinProduct a (basisBracket (b r))
      (dynkinProduct a (basisBracket (b r)) ((b r).equivFun (k r))
        ((b r).equivFun (u r z))) (-((b r).equivFun (k r)))) (fun _ => 0) atTop := by
  classical
  let S := boundedBracketWords (I := I) k₀
  let cost : S → ℝ := fun w => bracketWordExponent s w
  let bk := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S (β r))
    (fun i => (1 + δ) * cost ((β r).val i)) r
  let bu := fun r => exponentialRescaleBasis (WordBasisSelections.basis X S (β r))
    (fun i => (1 - c * δ) * cost ((β r).val i)) r
  have hek (r : ℝ) := exists_word_expansion_of_rescaled_norm_le X S (β r)
    (fun w => (1 + δ) * cost w) r (norm_nonneg ((bk r).equivFun (k r))) (k r) le_rfl
  have heu (r : ℝ) (z : Z) := exists_word_expansion_of_rescaled_norm_le X S (β r)
    (fun w => (1 - c * δ) * cost w) r (norm_nonneg ((bu r).equivFun (u r z))) (u r z) le_rfl
  choose ak hak hkeq using hek
  choose au hau hueq using heu
  have hkcoeff : ∀ᶠ r : ℝ in atTop, ∀ w,
      |ak r w| ≤ (finrank ℝ L : ℝ) * Real.exp (r * ((1 + δ) * cost w + ε r)) := by
    filter_upwards [hkbox] with r hr w
    apply (hak r w).trans
    calc
      _ ≤ (finrank ℝ L : ℝ) * Real.exp (r * ε r) *
          Real.exp (r * ((1 + δ) * cost w)) := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hucoeff : ∀ᶠ r : ℝ in atTop, ∀ z w,
      |au r z w| ≤ (finrank ℝ L : ℝ) * Real.exp (r * ((1 - c * δ) * cost w + ε r)) := by
    filter_upwards [hubox] with r hr z w
    apply (hau r z w).trans
    calc
      _ ≤ (finrank ℝ L : ℝ) * Real.exp (r * ε r) *
          Real.exp (r * ((1 - c * δ) * cost w)) := by
            gcongr
            exact hr z
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have h := rescaled_word_conjugation_tendstoUniformly X hk hnil b₀ s β hβ
    Exp hinj hneg a hm j ρ hρ hmatch hδ hc hhi (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hcost hgap ε hε ak au hkcoeff hucoeff
  dsimp only [S] at hkeq hueq
  simpa only [hkeq, hueq] using h

end PolycyclicRecognition

end

end OAI
