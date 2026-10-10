import OAI.NumberTheory.Ostmann.Construction.InitialMovingOriginalFactor
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSymmetrizedProductLower

namespace OAI

/-! # Harmonic product bounds from the literal two-half initial weights -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingLeafLengthEq_map {P Q : Type*} (f : P → Q) (n : ℕ)
    (x : TreeLeafTuple (List P) n) (a : ℕ) (hx : MovingLeafLengthEq n x a) :
    MovingLeafLengthEq n (treeLeafMap (List.map f) n x) a := by
  induction n with
  | zero => simpa only [MovingLeafLengthEq, treeLeafMap, List.length_map] using hx
  | succ n ih => exact ⟨ih x.1 hx.1, ih x.2 hx.2⟩

theorem bulkSlotLeaves_length_eq {P : Type*} (n m : ℕ)
    (slot : TreeLeafIndex n × Fin m → P) :
    MovingLeafLengthEq n (bulkSlotLeaves n m slot) m := by
  induction n with
  | zero => exact List.length_ofFn
  | succ n ih =>
    change MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inl j.1, j.2))) m ∧
      MovingLeafLengthEq n (bulkSlotLeaves n m (fun j => slot (.inr j.1, j.2))) m
    exact ⟨ih _, ih _⟩

theorem movingTemplateCoefficient_original_initial_bulk_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (y : MovingRegularSlot n a (b + b) → P) (hlen : a + 4 * n = r + r) (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s y XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ j : TreeLeafIndex n × Fin (b + b), value (y (j.1, .inr j.2)) : ℕ) : ℝ) := by
  unfold movingTemplateCoefficient at h
  rw [bulkSlotLeaves_map] at h
  exact movingFrequencyCoefficient_original_initial_product_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s _ _
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen XL XR h

theorem movingTemplateCoefficient_original_initial_full_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n a (b + b) → P)
    (hlen : 4 + a + 4 * n = r + r)
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) (XL XR : ℕ)
    (h : movingTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n (4 + a) (b + b) s
          (movingRestoreSample n a (b + b) u y) XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ i, value (y i) : ℕ) : ℝ) := by
  have hb := movingTemplateCoefficient_original_initial_bulk_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n (4 + a) s
    (movingRestoreSample n a (b + b) u y) hlen XL XR h
  have he : (∏ j : TreeLeafIndex n × Fin (b + b),
      value (movingRestoreSample n a (b + b) u y (j.1, .inr j.2))) =
      ∏ j : TreeLeafIndex n × Fin (b + b), value (y (j.1, .inr j.2)) := by
    apply Finset.prod_congr rfl
    intro j _
    change value (movingRestoreSample n a (b + b) u y
      (movingTemplateBulk n (4 + a) (b + b) j)) = _
    rw [movingRestoreSample_bulk]
    rfl
  rw [he] at hb
  have hs := movingTemplate_small_product_lower value n a (b + b) y lower hlower
  rw [Real.exp_add]
  convert mul_le_mul hs hb (Real.exp_nonneg _) (Nat.cast_nonneg _) using 1
  rw [← Nat.cast_mul]
  congr 1
  simp only [MovingRegularSlot, Fintype.prod_prod_type, Fintype.prod_sum_type,
    Finset.prod_mul_distrib]

theorem movingSymmetrizedTemplateCoefficient_original_initial_full_lower {P I : Type} [Fintype P]
    (value : P → ℕ) (hvalue : ∀ p, 0 < value p)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (g : ∀ i, ZMod (q i) → ℂ)
    (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n a : ℕ) (s : ℤ)
    (u : TreeLeafIndex n × Fin 4 → P) (y : MovingRegularSlot n a (b + b) → P)
    (hlen : 4 + a + 4 * n = r + r)
    (lower : TreeLeafIndex n × Fin a → ℝ)
    (hlower : ∀ j, Real.exp (lower j) ≤ (value (y (j.1, .inl j.2)) : ℝ)) (XL XR : ℕ)
    (h : movingSymmetrizedTemplateCoefficient value outside μ childBound pivotBound V
      (movingOriginalLeaf value q (initialMovingDataCutoff value b d r cb cd sl sr fallback)
        g Dq S ψ X lo hi) φ G n a (b + b) s u y XL XR ≠ 0) :
    Real.exp ((∑ j, lower j) + (2 ^ n : ℕ) * (2 * cb - 2)) ≤
      ((∏ i, value (y i) : ℕ) : ℝ) := by
  obtain ⟨e, he⟩ := mixedBulkSymmetrize_ne_zero n (b + b)
    (movingTemplateBulk n a (b + b)) _ 0 y 0 0 h
  have hl (j : TreeLeafIndex n × Fin a) : Real.exp (lower j) ≤
      (value (selectedBulkSample (movingTemplateBulk n a (b + b)) e y (j.1, .inl j.2)) : ℝ) := by
    rw [selectedBulkSample_template_small]
    exact hlower j
  have hp := movingTemplateCoefficient_original_initial_full_lower value hvalue b d r cb cd sl sr
    fallback q g Dq S ψ X lo hi outside μ childBound pivotBound V φ G n a s u
    (selectedBulkSample (movingTemplateBulk n a (b + b)) e y) hlen lower hl XL XR he
  rwa [selectedBulkSample_prod] at hp

end Ostmann

end OAI
