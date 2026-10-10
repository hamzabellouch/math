import OAI.Combinatorics.Progressions.Lattices.QuantitativeEarlyAffineCoveredSource

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

 theorem exists_polynomial_early_affine_covered_source
    (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a) (hblock : ∀ a, Function.Injective (block a))
    {p : ℝ} (hp : 0 ≤ p) (hq : Fintype.card α ≤ m + 1)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    {δ η E F : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hηE : η⁻¹ ≤ Real.exp E) (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let D := allocatedComparisonDimension m p
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, 0 < ρ P ∧ ρ P ≤ 1 ∧
        (ρ P : ℝ)⁻¹ ≤ Real.exp (2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2)) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        Real.log t⁻¹ ≤ affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F ∧
        AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  intro D
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hrows hp hK hI hn
  have hcost := allocatedAffine_log_costs_le_envelope B A T hd hE hF
  obtain ⟨ρ, hρ, t, ht, htone, hlog, hs⟩ :=
    exists_quantitative_early_affine_covered_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη hE hF hηE hδF
  refine ⟨ρ, ?_, t, ht, htone, hlog.trans hcost.2, hs⟩
  intro partition
  exact ⟨(hρ partition).1, (hρ partition).2.1,
    (hρ partition).2.2.trans (Real.exp_le_exp.mpr hcost.1)⟩

end Erdos3.VectorPolynomial

end

end OAI
