import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveProductBounds
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateIntegerNode

namespace OAI

/-! # Derived product caps for every restored moving template -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

noncomputable def movingCellPivotExponent (G c : ℕ → ℝ) (n : ℕ) : ℝ :=
  G (n + 1) - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * (c n - 1)

/-- Every compensation prior is the original prior. Only its actual nonzero
support is used in the lower bound; no renormalization is performed. -/
theorem movingFrequencyCoefficient_recursive_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμ : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior (μ n) n a ≠ 0)
    (s : ℤ) (small bulk : TreeLeafTuple (List σ) n) (p XR : ℕ)
    (hpbound : Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n s
      (appendMovingSlotLeaves n (movingCompensationSlots n a) small) bulk p XR ≠ 0) :
    XR * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk) ≤
      ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
        movingCellPivotExponent G c n)⌉₊ := by
  let T := movingCellPivotExponent G c
  have hmin (j : ℕ) (b : TreeLeafTuple (Fin 4 → σ) j)
      (hb : movingCompensationPrior (μ j) j b ≠ 0) (p' : ℕ) (hp' : 0 < p')
      (hφ' : φ (Real.log p' - G (j + 1)) ≠ 0) :=
    movingInsertedPivot_product_lower value (μ j) (c j) (G (j + 1)) φ
      (hμ j) hout j b hb p' hp' hφ'
  have hb := movingFrequencyCoefficient_recursive_product_bound value outside μ
    childBound pivotBound V q F g Dq S ψ X lo hi W hX hwindow φ G T hmin n s
    (appendMovingSlotLeaves n (movingCompensationSlots n a) small) bulk p XR h
  rw [movingNaturalProduct_append_leaves] at hb
  let U := MovingSlotReversal.naturalProduct value
    (flattenMovingSlots n (movingCompensationSlots n a))
  let R := XR * MovingSlotReversal.naturalProduct value
    (flattenMovingSlots n small ++ flattenMovingSlots n bulk)
  have hid : p * XR * (U * MovingSlotReversal.naturalProduct value
      (flattenMovingSlots n small ++ flattenMovingSlots n bulk)) = (p * U) * R := by
    dsimp only [R]; ring
  rw [hid, Nat.cast_mul] at hb
  have hlow := movingCompensation_pivot_lower_of_bound value (μ n) (c n) (G (n + 1))
    (hμ n) n a ha p hpbound
  have hreal : (R : ℝ) ≤ Real.exp (movingProductExponent T W n - T n) := by
    rw [Real.exp_sub]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    have hh := (mul_le_mul_of_nonneg_right hlow (Nat.cast_nonneg R)).trans hb
    simpa only [T, movingCellPivotExponent, mul_comm] using hh
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-- The product bound required by the Cauchy--Schwarz transfer now follows at
any depth from the terminal cutoff and the selected compensation cells. -/
theorem movingTemplateCoefficient_recursive_cell_cap {σ I : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : I → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμ : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
    (s : ℤ) (y : MovingRegularSlot n r m → σ) (p XR : ℕ)
    (hpbound : Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m s
      (movingRestoreSample n r m u y) p XR ≠ 0) :
    XR * (∏ i, value (y i)) ≤
      ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
        movingCellPivotExponent G c n)⌉₊ := by
  let a := (movingTemplateCompensationEquiv σ n).symm u
  have he : movingTemplateCompensationEquiv σ n a = u := Equiv.apply_symm_apply _ _
  have ha : movingCompensationPrior (μ n) n a ≠ 0 := by
    rw [← movingTemplateCompensationEquiv_prior, he]
    exact hu
  rw [← he, movingTemplateCoefficient_restored] at h
  have hc := movingFrequencyCoefficient_recursive_cell_cap value outside μ childBound pivotBound V
    q F g Dq S ψ X lo hi W hX hwindow φ G c hout hμ n a ha s _ _ p XR hpbound h
  rwa [movingTemplateMapped_product] at hc

end Ostmann

end OAI
