import OAI.NumberTheory.Ostmann.Construction.SupportedAlphabetSum
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalWeightRelabel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternTree

namespace OAI

/-! # The original moving sampler on a smaller live alphabet -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingCompensationExtra_map {A B : Type*} (e : B → A) (value : A → ℕ)
    {n : ℕ} (T : MovingSlotData B n) (s v w : ℤ) :
    movingCompensationExtra value (T.map e) s v w =
      movingCompensationExtra (value ∘ e) T s v w := by
  cases T <;> simp only [MovingSlotData.map, movingCompensationExtra,
    MovingSlotReversal.naturalProduct_map]

theorem movingOriginalSampleAverage_alphabet {A B I : Type} [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List B) n)
    (XL XR : ℕ) (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t (treeLeafMap (List.map e) n small) (treeLeafMap (List.map e) n bulk) XL XR =
    movingOriginalSampleAverage q (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound
      (fun T => F (T.map e)) g Dq S ψ X lo hi φ G n t small bulk XL XR := by
  unfold movingOriginalSampleAverage
  rw [movingSamplesPrior_alphabet_sum e μ n _ hμ]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← buildMovingSlotData_map, movingOriginalGiantWeight_map, movingSupportedWeight_map]
  congr 2
  funext d T s v w
  exact movingCompensationExtra_map e value T s v w

theorem movingFrequencyCoefficient_original_alphabet {A B I : Type} [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List B) n)
    (XL XR : ℕ) (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s
      (treeLeafMap (List.map e) n small) (treeLeafMap (List.map e) n bulk) XL XR =
    movingFrequencyCoefficient (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q (fun T => F (T.map e)) g Dq S ψ X lo hi)
      φ G n s small bulk XL XR := by
  simp only [movingFrequencyCoefficient_original]
  apply Finset.sum_congr rfl
  intro t _
  exact movingOriginalSampleAverage_alphabet e q value outside μ childBound pivotBound F g Dq S
    ψ X lo hi φ G n _ small bulk XL XR hμ

theorem movingTemplateCoefficient_original_alphabet {A B I : Type} [Fintype A] [Fintype B]
    (e : B ↪ A) (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (value : A → ℕ) (outside : List ℕ) (μ : ℕ → A → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData A n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n r m : ℕ) (s : ℤ) (y : MovingRegularSlot n r m → B)
    (XL XR : ℕ) (hμ : ∀ j a, j < n → μ j a ≠ 0 → a ∈ Set.range e) :
    movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m s (e ∘ y) XL XR =
    movingTemplateCoefficient (value ∘ e) outside (fun j b => μ j (e b)) childBound pivotBound V
      (movingOriginalLeaf (value ∘ e) q (fun T => F (T.map e)) g Dq S ψ X lo hi)
      φ G n r m s y XL XR := by
  unfold movingTemplateCoefficient
  rw [← treeLeafMap_list_comp, ← treeLeafMap_list_comp]
  exact movingFrequencyCoefficient_original_alphabet e q value outside μ childBound pivotBound V F
    g Dq S ψ X lo hi φ G n s _ _ XL XR hμ

end Ostmann

end OAI
