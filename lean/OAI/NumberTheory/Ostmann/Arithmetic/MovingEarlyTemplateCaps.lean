import OAI.NumberTheory.Ostmann.Arithmetic.MovingEarlyCellCaps
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateIntegerNode

namespace OAI

/-! # The first two product caps on the literal restored templates -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplateCoefficient_initial_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi c E : ℝ) (hX : 0 < X) (hE : 0 ≤ E)
    (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (hμ : ∀ x, μ 0 x ≠ 0 → Real.exp (c - 1) ≤ (value x : ℝ))
    (hwindow : X * hi ≤ Real.exp (G 1 - 1 + 4 * (c - 1) + E))
    (r m : ℕ) (u : TreeLeafIndex 0 × Fin 4 → σ) (hu : (∏ i, μ 0 (u i)) ≠ 0)
    (s : ℤ) (y : MovingRegularSlot 0 r m → σ) (p XR : ℕ)
    (hp : 0 < p) (hpbound : Real.exp (G 1 - 1) ≤ (p : ℝ))
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 0 (4 + r) m s
      (movingRestoreSample 0 r m u y) p XR ≠ 0) :
    XR * (∏ i, value (y i)) ≤ ⌈Real.exp E⌉₊ := by
  let a := (movingTemplateCompensationEquiv σ 0).symm u
  have he : movingTemplateCompensationEquiv σ 0 a = u := Equiv.apply_symm_apply _ _
  have ha : movingCompensationPrior (μ 0) 0 a ≠ 0 := by
    rw [← movingTemplateCompensationEquiv_prior, he]
    exact hu
  rw [← he, movingTemplateCoefficient_restored] at h
  let small : List σ := treeLeafMap (List.map y) 0 (movingTemplateSmall 0 r m)
  let bulk : List σ := treeLeafMap (List.map y) 0 (bulkSlotLeaves 0 m (movingTemplateBulk 0 r m))
  have hc := movingFrequencyCoefficient_initial_cell_cap value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi c E hX hE φ G hμ hwindow a ha s
    small bulk p XR hp hpbound h
  have hid := movingTemplateMapped_product value 0 r m y
  change MovingSlotReversal.naturalProduct value (small ++ bulk) = _ at hid
  rwa [hid] at hc

theorem movingTemplateCoefficient_one_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi c₀ c₁ E : ℝ) (hX : 0 < X) (hE : 0 ≤ E)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμ₀ : ∀ x, μ 0 x ≠ 0 → Real.exp (c₀ - 1) ≤ (value x : ℝ))
    (hμ₁ : ∀ x, μ 1 x ≠ 0 → Real.exp (c₁ - 1) ≤ (value x : ℝ))
    (hwindow : X * hi ≤ Real.exp (G 1 - 1 + 4 * (c₀ - 1) + E))
    (r m : ℕ) (u : TreeLeafIndex 1 × Fin 4 → σ) (hu : (∏ i, μ 1 (u i)) ≠ 0)
    (s : ℤ) (y : MovingRegularSlot 1 r m → σ) (p XR : ℕ)
    (hp : 0 < p) (hpbound : Real.exp (G 2 - 1) ≤ (p : ℝ))
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G 1 (4 + r) m s
      (movingRestoreSample 1 r m u y) p XR ≠ 0) :
    XR * (∏ i, value (y i)) ≤
      ⌈Real.exp (2 * E - (G 2 - 1 + 8 * (c₁ - 1)) + Real.log 4)⌉₊ := by
  let a := (movingTemplateCompensationEquiv σ 1).symm u
  have he : movingTemplateCompensationEquiv σ 1 a = u := Equiv.apply_symm_apply _ _
  have ha : movingCompensationPrior (μ 1) 1 a ≠ 0 := by
    rw [← movingTemplateCompensationEquiv_prior, he]
    exact hu
  rw [← he, movingTemplateCoefficient_restored] at h
  let small : List σ × List σ := treeLeafMap (List.map y) 1 (movingTemplateSmall 1 r m)
  let bulk : List σ × List σ := treeLeafMap (List.map y) 1 (bulkSlotLeaves 1 m (movingTemplateBulk 1 r m))
  have hc := movingFrequencyCoefficient_one_cell_cap value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi c₀ c₁ E hX hE φ G hout hμ₀ hμ₁ hwindow a ha s small bulk p XR hp hpbound h
  have hid := movingTemplateMapped_product value 1 r m y
  change MovingSlotReversal.naturalProduct value ((small.1 ++ small.2) ++ (bulk.1 ++ bulk.2)) = _ at hid
  have hperm : MovingSlotReversal.naturalProduct value ((small.1 ++ bulk.1) ++ (small.2 ++ bulk.2)) =
      MovingSlotReversal.naturalProduct value ((small.1 ++ small.2) ++ (bulk.1 ++ bulk.2)) := by
    simp only [movingNaturalProduct_append]
    ring
  rwa [hperm, hid] at hc

end Ostmann

end OAI
