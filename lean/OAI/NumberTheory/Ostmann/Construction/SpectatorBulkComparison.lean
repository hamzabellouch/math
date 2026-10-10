import OAI.NumberTheory.Ostmann.Construction.ArrangementBulkComparison
import OAI.NumberTheory.Ostmann.Characters.QuartetTreeSmallParameters
import OAI.NumberTheory.Ostmann.Construction.SpectatorProductNorm

namespace OAI

/-! # Uniform signed comparison at all spectator primes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def SpectatorDiagram.bulkValue {p n m : ℕ} [Fact p.Prime]
    (d : SpectatorDiagram p n) (g : ZMod p → ℂ)
    (x : TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℂ :=
  indexedRationalAmplitude g d.D d.tree d.XL d.XR d.conjugations (bulkBlockProduct x)

theorem spectator_bulk_comparison {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (n m : ℕ) (hm : 0 < m)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (hgood : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
      3 * Fintype.card (TreeLeafIndex (n + 2)))
    (g : ZMod p → ℂ) (hg : g 0 = 0) (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hflat : MixedFourierBound g ε)
    (d₁ d₂ : SpectatorDiagram p (n + 2)) (cL cR : TreeLeafIndex n → Bool)
    (hconj : ∀ q, quartetBlockEquiv Bool n d₁.conjugations q =
      ((cL q, !(cL q)), (cR q, !(cR q)))) :
    ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
      (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
        d₁.bulkValue g x * conj (d₂.bulkValue g (x ∘ e.symm)))‖ ^ 2 ≤
      quartetTreeConstant n * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  have h := (arrangement_tree_bulk_comparison hp g hg henergy ε hε hflat n m hm e hgood
    d₁.D d₂.D d₁.tree d₂.tree d₁.XL d₁.XR d₂.XL d₂.XR d₁.conjugations d₂.conjugations
    cL cR hconj).trans (quartetTree_error_le hp n ε hε hε1)
  simpa only [bulkPairCorrelation, SpectatorDiagram.bulkValue, finite_univ_canonical,
    Fintype.card_eq_nat_card] using h

theorem exists_uniform_spectator_bulk_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ (p : ℕ) [Fact p.Prime], N ≤ p →
      ∀ (m : ℕ), 0 < m →
      ∀ e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      ∀ g : ZMod p → ℂ, g 0 = 0 → (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ) →
      MixedFourierBound g ε →
      ∀ (d₁ d₂ : SpectatorDiagram p (n + 2)) (cL cR : TreeLeafIndex n → Bool),
      (∀ q, quartetBlockEquiv Bool n d₁.conjugations q = ((cL q, !(cL q)), (cR q, !(cR q)))) →
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ) : ℂ)⁻¹ *
        (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod p)ˣ,
          d₁.bulkValue g x * conj (d₂.bulkValue g (x ∘ e.symm)))‖ ≤ δ := by
  obtain ⟨ε, hε, hε1, N, hN, hnum⟩ :=
    exists_quartet_small_parameters (quartetTreeConstant n) δ (quartetTreeConstant_pos n) hδ
  refine ⟨ε, hε, N, hN, ?_⟩
  intro p hpFact hp m hm e hgood g hg henergy hflat d₁ d₂ cL cR hconj
  have h := (spectator_bulk_comparison (hN.trans hp) n m hm e hgood g hg henergy
    ε hε.le hε1 hflat d₁ d₂ cL cR hconj).trans (hnum p hp)
  exact (sq_le_sq₀ (norm_nonneg _) hδ.le).mp h

theorem product_uniform_mean_complex {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] (F : ∀ i, A i → ℂ) :
    (Fintype.card (∀ i, A i) : ℂ)⁻¹ * (∑ x : ∀ i, A i, ∏ i, F i (x i)) =
      ∏ i, (Fintype.card (A i) : ℂ)⁻¹ * ∑ a, F i a := by
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]

theorem spectator_bulk_product_bound {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, Fact (p i).Prime] (n m : ℕ)
    (e : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
    (g : ∀ i, ZMod (p i) → ℂ) (d₁ d₂ : ∀ i, SpectatorDiagram (p i) (n + 2))
    (δ : ℝ) (_hδ : 0 ≤ δ)
    (hlocal : ∀ i,
      ‖(Fintype.card (TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
        (∑ x : TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ,
          (d₁ i).bulkValue (g i) x * conj ((d₂ i).bulkValue (g i) (x ∘ e.symm)))‖ ≤ δ) :
    ‖(Fintype.card (∀ i, TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) : ℂ)⁻¹ *
      (∑ x : ∀ i, TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ,
        ∏ i, (d₁ i).bulkValue (g i) (x i) * conj ((d₂ i).bulkValue (g i) (x i ∘ e.symm)))‖ ≤
      δ ^ Fintype.card I := by
  have he := product_uniform_mean_complex (fun (i : I)
    (x : TreeLeafIndex (n + 2) × Fin m → (ZMod (p i))ˣ) =>
      (d₁ i).bulkValue (g i) x * conj ((d₂ i).bulkValue (g i) (x ∘ e.symm)))
  rw [he, norm_prod]
  calc
    _ ≤ ∏ _i : I, δ := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hlocal i)
    _ = _ := by simp

end Ostmann

end OAI
