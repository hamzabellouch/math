import OAI.NumberTheory.Ostmann.Construction.InitialMovingTemplateProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogDiagonal

namespace OAI

/-! # Removing only the nonnegative diagonal's actual half-cutoff weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem initialHalfBulkWeight_bounds {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (bulk : Fin (b + b) → P) :
    0 ≤ initialHalfBulkWeight value b d cb cd sl sr bulk ∧
      initialHalfBulkWeight value b d cb cd sl sr bulk ≤ 1 := by
  exact initialMovingRealWeight_bounds value b d 0 cb cd sl sr
    (fun j => Sum.elim Fin.elim0 bulk j.2)

theorem initialHalfBulkProduct_bounds {P : Type*} (value : P → ℕ)
    (b d : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (n : ℕ)
    (slot : TreeLeafIndex n × Fin (b + b) → P) :
    0 ≤ initialHalfBulkProduct value b d cb cd sl sr n slot ∧
      initialHalfBulkProduct value b d cb cd sl sr n slot ≤ 1 := by
  induction n with
  | zero => exact initialHalfBulkWeight_bounds value b d cb cd sl sr _
  | succ n ih =>
    obtain ⟨hl, hl1⟩ := ih (fun j => slot (.inl j.1, j.2))
    obtain ⟨hr, hr1⟩ := ih (fun j => slot (.inr j.1, j.2))
    exact ⟨mul_nonneg hl hr, (mul_le_mul hl1 hr1 hr zero_le_one).trans_eq (one_mul 1)⟩

theorem movingTemplateCoefficient_original_initial_norm_le {P J : Type} [Fintype P]
    (value : P → ℕ) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : J → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ) :
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR‖ ≤
    ‖movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (fun _ s => if s = 0 then 0 else 1) g Dq S ψ X lo hi)
        φ G n a (b + b) s y XL XR‖ := by
  unfold movingTemplateCoefficient
  rw [bulkSlotLeaves_map]
  rw [movingFrequencyCoefficient_original_initial_halves value b d r cb cd sl sr fallback
    q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s
    (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
    (y ∘ movingTemplateBulk n a (b + b))
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (initialHalfBulkProduct_bounds value b d cb cd sl sr n _).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (initialHalfBulkProduct_bounds value b d cb cd sl sr n _).2

end Ostmann

end OAI
