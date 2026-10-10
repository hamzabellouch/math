import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSymmetrization
import OAI.NumberTheory.Ostmann.Characters.MixedExternalStatistic

namespace OAI

/-! # The original mixed arithmetic statistic and its symmetrized upper bound -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingExternalRegularFactor {σ B : Type*} {n : ℕ}
    (value : σ → ℕ) (outside : List ℕ) (small bulk : TreeLeafTuple (List B) n)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (s : ℤ) (y : B → σ) (x z : ℝ) : ℂ :=
  primeProductTransform greg (outside.prod * ⌊Real.exp x⌋₊ * ⌊Real.exp z⌋₊)
    (MovingSlotReversal.naturalProduct (value ∘ y)
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk)) s

theorem giantOuterWeight_positive (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (Jleft Jright : ℝ) (diagonal : Bool) (L R : ℝ) :
    ∃ a : ℝ, 0 ≤ a ∧ giantOuterWeight φ Jleft Jright diagonal L R = a := by
  have hc (x J : ℝ) : 0 ≤ positiveLogCutoff φ J x := by
    unfold positiveLogCutoff
    split_ifs
    · exact hφ _
    · exact le_rfl
  refine ⟨positiveLogCutoff φ Jleft L * positiveLogCutoff φ Jright R *
    (if diagonal then Real.exp Jright / R else 1), ?_, ?_⟩
  · have hratio : 0 ≤ (if diagonal then Real.exp Jright / R else 1) ∨ R ≤ 0 := by
      by_cases hR : 0 ≤ R
      · left; split_ifs <;> positivity
      · exact Or.inr (le_of_not_ge hR)
    rcases hratio with hratio | hR
    · exact mul_nonneg (mul_nonneg (hc _ _) (hc _ _)) hratio
    · simp only [positiveLogCutoff, not_lt.mpr hR, ite_false, mul_zero, zero_mul]
      exact le_rfl
  · unfold giantOuterWeight
    cases diagonal <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> push_cast <;> rfl

noncomputable def movingOriginalStatistic {σ I B : Type}
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
    (movingExternalRegularFactor value outside small (bulkSlotLeaves n m slot)
      greg s y x z * F s y x z) *
      giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)

theorem movingOriginalStatistic_cauchy {σ I B : Type}
    [Fintype σ] [Fintype B] (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ) (ν : B → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (G : ℕ → ℝ)
    (n m : ℕ) (small : TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (hsmall : ∀ i ∈ flattenMovingSlots n small, i ∉ Set.range slot)
    (hν : ∀ b a, 0 ≤ ν b a) (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v r w center : ℝ) :
    ‖movingOriginalStatistic q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg Jleft Jright diagonal u v r w center‖ ^ 2 ≤
    (mixedExternalAverage ν (V n) u v r w center (fun _ _ x z =>
      giantOuterWeight φ Jleft Jright diagonal ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊)).re *
    (movingOriginalSymmetrizedEnergy q value outside μ ν childBound pivotBound V f g Dq S
      ψ X lo hi φ G n m small slot greg Jleft Jright diagonal u v r w center).re := by
  let F := fun s y x z => movingFrequencyCoefficient value outside μ childBound pivotBound V
    (movingOriginalLeaf value q (fun _ => f) g Dq S ψ X lo hi) φ G n s
    (treeLeafMap (List.map y) n small)
    (treeLeafMap (List.map y) n (bulkSlotLeaves n m slot)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  let H := movingExternalRegularFactor value outside small (bulkSlotLeaves n m slot) greg
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
  have hc := mixedBulkSymmetrize_statistic_cauchy n m slot ν hν hidentical (V n)
    u v r w center F H hH (fun x z => (W x z).re) (fun x z => (hW x z).1)
  simp only [(hW _ _).2] at hc
  exact hc

end Ostmann

end OAI
