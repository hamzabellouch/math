import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalBulkAction
import OAI.NumberTheory.Ostmann.Characters.MixedBulkSymmetrization

namespace OAI

/-! # The original coefficient symmetrization with its common regular multiplier -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalSymmetrizedEnergy {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) : ℂ :=
  let F := fun s y x z => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
    (treeLeafMap (List.map y) n small)
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  mixedExternalAverage ν (V n) u v r w center (fun s y x z =>
    (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
      movingExternalDiagonalWeight value outside small (bulkSlotLeaves n m slot)
        greg s φ Jleft Jright diagonal y x z)

theorem movingOriginalSymmetrizedEnergy_bound {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (n m : ℕ) (hm : 1 ≤ m) (small : TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hν : ∀ b a, 0 ≤ ν b a) (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center D E : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hdiag : ‖movingOriginalDiagonalEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n small (bulkSlotLeaves n m slot) greg Jleft Jright diagonal u v r w center‖ ≤ D)
    (hgood : ∀ e : Equiv.Perm (TreeLeafIndex n × Fin m),
      4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex n) →
      ‖movingOriginalMatchedCorrelation q value outside μ ν childBound pivotBound V f g Dq S
        ψ X lo hi φ G n small (movingPatternBulkLeaves n m slot e) greg
        Jleft Jright diagonal u v r w center‖ ≤ E) :
    (movingOriginalSymmetrizedEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg Jleft Jright diagonal u v r w center).re ≤
      (((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
        Real.exp ((2 ^ n : ℝ) * m * (-(3 / 4 : ℝ) * Real.log (2 ^ n : ℕ) + 5 / 4)) * D + E := by
  let F := fun s y x z => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
    (treeLeafMap (List.map y) n small)
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let W := fun s y x z => movingExternalDiagonalWeight value outside small
    (bulkSlotLeaves n m slot) greg s φ Jleft Jright diagonal y x z
  have hW (s y x z) : 0 ≤ (W s y x z).re ∧ ((W s y x z).re : ℂ) = W s y x z := by
    obtain ⟨a, ha, heq⟩ := movingExternalDiagonalWeight_positive value outside small
      (bulkSlotLeaves n m slot) greg s φ hφ Jleft Jright diagonal y x z
    change W s y x z = (a : ℂ) at heq
    rw [heq]
    simpa only [Complex.ofReal_re] using And.intro ha (Eq.refl (a : ℂ))
  have hinv (e s y x z) : (W s (selectedBulkSample slot e y) x z).re = (W s y x z).re :=
    congrArg Complex.re (movingExternalDiagonalWeight_selectedBulkSample value outside n m
      small slot e y hsmall greg s φ Jleft Jright diagonal x z)
  have hd : (mixedExternalAverage ν (V n) u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * (W s y x z).re)).re ≤ D := by
    simp only [(hW _ _ _ _).2]
    exact (Complex.re_le_norm _).trans hdiag
  have hg (e : Equiv.Perm (TreeLeafIndex n × Fin m))
      (he : 4 * Fintype.card (arrangementGraph m e).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex n)) :
      ‖mixedExternalAverage ν (V n) u v r w center
        (fun s y x z => (F s y x z * star (F s (selectedBulkSample slot e y) x z)) *
          (W s y x z).re)‖ ≤ E := by
    simp only [(hW _ _ _ _).2]
    rw [← movingOriginalMatchedCorrelation_bulk_action q value outside μ ν childBound pivotBound V
      f g Dq S ψ X lo hi φ G n m small slot e hsmall greg Jleft Jright diagonal u v r w center]
    exact hgood e he
  have h := mixedBulkSymmetrize_energy_bound n m hm slot ν hν hidentical (V n)
    u v r w center F (fun s y x z => (W s y x z).re) (fun s y x z => (hW s y x z).1)
    hinv D E hD hE hd hg
  simp only [(hW _ _ _ _).2] at h
  exact h

end Ostmann

end OAI
