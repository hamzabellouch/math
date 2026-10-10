import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantPhase
import OAI.NumberTheory.Ostmann.Characters.MixedBoundedPhaseStatistic

namespace OAI

/-! # The original statistic with both giant Fourier phases retained -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingOriginalPhaseStatistic {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) : ℂ :=
  let F := fun s y x z => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
    (treeLeafMap (List.map y) n small)
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  mixedExternalAverage ν (V n) u v r w center (fun s y x z =>
    ((movingGiantPhase value outside small (bulkSlotLeaves n m slot)
      ggiant favorable s y x z * movingExternalRegularFactor value outside small (bulkSlotLeaves n m slot)
      greg s y x z) * F s y x z) *
      giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)

theorem movingOriginalPhaseStatistic_cauchy {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hν : ∀ b a, 0 ≤ ν b a) (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) :
    ‖movingOriginalPhaseStatistic q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg ggiant favorable Jleft Jright diagonal u v r w center‖ ^ 2 ≤
    (mixedExternalAverage ν (V n) u v r w center (fun _ _ x z =>
      giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)).re *
    (movingOriginalSymmetrizedEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg Jleft Jright diagonal u v r w center).re := by
  let F := fun s y x z => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
    (treeLeafMap (List.map y) n small)
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let H := movingExternalRegularFactor value outside small (bulkSlotLeaves n m slot) greg
  let P := movingGiantPhase value outside small (bulkSlotLeaves n m slot) ggiant favorable
  let W := fun (x z : ℝ) => giantOuterWeight φ Jleft Jright diagonal
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  have hW (x z : ℝ) : 0 ≤ (W x z).re ∧ ((W x z).re : ℂ) = W x z := by
    obtain ⟨a, ha, heq⟩ := giantOuterWeight_positive φ hφ Jleft Jright diagonal
      ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    change W x z = (a : ℂ) at heq
    rw [heq]
    simpa only [Complex.ofReal_re] using And.intro ha (Eq.refl (a : ℂ))
  have hH (e s y x z) : H s (selectedBulkSample slot e y) x z = H s y x z := by
    dsimp [H, movingExternalRegularFactor]
    rw [MovingSlotReversal.naturalProduct_selected_bulk value n m small slot e y hsmall]
  have hP (e s y x z) : P s (selectedBulkSample slot e y) x z = P s y x z := by
    exact movingGiantPhase_selectedBulkSample value outside n m small slot e y hsmall
      ggiant favorable s x z
  have hPnorm (s y x z) : ‖P s y x z‖ ≤ 1 :=
    movingGiantPhase_norm_le value outside small (bulkSlotLeaves n m slot) ggiant favorable s y x z
  have hc := mixedBulkSymmetrize_bounded_statistic_cauchy n m slot ν hν hidentical (V n)
    u v r w center F H P hH hP hPnorm (fun x z => (W x z).re) (fun x z => (hW x z).1)
  simp only [(hW _ _).2] at hc
  exact hc

end Ostmann

end OAI
