import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open scoped ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

 theorem exists_quantitative_early_affine_covered_source
    (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a) (hblock : ∀ a, Function.Injective (block a))
    {δ η E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hηE : η⁻¹ ≤ Real.exp E) (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, 0 < ρ P ∧ ρ P ≤ 1 ∧
        (ρ P : ℝ)⁻¹ ≤ Real.exp (allocatedAffineRadiusLog (O := O) (α := α) B A T E F)) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        Real.log t⁻¹ ≤ allocatedAffineToleranceLog (G := G) (O := O) (α := α) B A T E F ∧
        AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  obtain ⟨ρ, hρ, t, ht, htone, hlog, hs⟩ :=
    exists_quantitative_early_affine_reference_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη hE hF hηE hδF
  refine ⟨ρ, hρ, t, ht, htone, hlog, ?_⟩
  apply allocatedAffineCoveredComparison_of_coefficient B rows hδ ρ
    (fun P => (hρ P).1) (fun P => (hρ P).2.1) t htone
  exact allocatedAffineCoefficientComparison_of_reference B rows hrows hcard hδ ρ
    (fun P => (hρ P).1) (fun P => (hρ P).2.1) t htone hs

end Erdos3.VectorPolynomial

end

end OAI
