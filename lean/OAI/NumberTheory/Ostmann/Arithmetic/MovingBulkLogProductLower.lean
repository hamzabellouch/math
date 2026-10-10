import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateProducts
import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkOriginalCoefficient

namespace OAI

/-! # Product lower bounds forced by the original terminal weights -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingBulkListLogWeight_product_lower {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ a, 0 < value a) (outside : List ℕ) (cb cd : ℝ) (bulk : List σ)
    (h : movingBulkListLogWeight value outside cb cd bulk ≠ 0) :
    Real.exp (cb - 1) ≤ (MovingSlotReversal.naturalProduct value bulk : ℝ) := by
  have hw : logCellProfile ((bulk.map (fun a => Real.log (value a : ℝ))).sum - cb) ≠ 0 :=
    left_ne_zero_of_mul h
  have habs : |(bulk.map (fun a => Real.log (value a : ℝ))).sum - cb| < 1 := by
    by_contra hn
    exact hw (logCellProfile_zero_outside _ (not_lt.mp hn))
  have hp : 0 < (MovingSlotReversal.naturalProduct value bulk : ℝ) := by
    exact_mod_cast List.prod_pos (fun p hp => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
      exact hvalue a)
  have hl : Real.log (MovingSlotReversal.naturalProduct value bulk : ℝ) =
      (bulk.map (fun a => Real.log (value a : ℝ))).sum := by
    unfold MovingSlotReversal.naturalProduct
    rw [Nat.cast_list_prod, Real.log_list_prod]
    · simp only [List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
      exact_mod_cast (hvalue a).ne'
  have hlog : cb - 1 ≤ Real.log (MovingSlotReversal.naturalProduct value bulk : ℝ) := by
    rw [hl]
    linarith [(abs_lt.mp habs).1]
  exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log hp)

/-- Every original leaf supplies its own product lower bound. Multiplication
therefore gives the full `2^n` exponent, with no distinctness assumption. -/
theorem movingBulkTreeLogWeight_product_lower {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ a, 0 < value a) (outside : List ℕ) (cb cd : ℝ)
    (n m : ℕ) (slot : TreeLeafIndex n × Fin m → σ)
    (h : treeLeafProduct n (treeLeafMap (movingBulkListLogWeight value outside cb cd) n
      (bulkSlotLeaves n m slot)) ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ i, value (slot i) : ℕ) : ℝ) := by
  have hw : (∏ j : TreeLeafIndex n,
      movingBulkListLogWeight value outside cb cd (List.ofFn (fun i => slot (j, i)))) ≠ 0 := by
    have he : treeLeafMap (movingBulkListLogWeight value outside cb cd) n
        (bulkSlotLeaves n m slot) = (treeLeafTupleEquiv ℝ n).symm
          (fun j => movingBulkListLogWeight value outside cb cd (List.ofFn (fun i => slot (j, i)))) := by
      apply (treeLeafTupleEquiv ℝ n).injective
      funext j
      simp only [treeLeafTupleEquiv_map, bulkSlotLeaves, Equiv.apply_symm_apply]
    rwa [he, treeLeafProduct_indexed] at h
  have hleaf (j : TreeLeafIndex n) : Real.exp (cb - 1) ≤
      ((∏ i : Fin m, value (slot (j, i)) : ℕ) : ℝ) := by
    have hh := movingBulkListLogWeight_product_lower value hvalue outside cb cd
      (List.ofFn (fun i => slot (j, i))) (Finset.prod_ne_zero_iff.mp hw j (Finset.mem_univ j))
    simpa only [MovingSlotReversal.naturalProduct, List.map_ofFn, List.prod_ofFn, Function.comp_def] using hh
  have hp := Finset.prod_le_prod₀ (fun j (_ : j ∈ (Finset.univ : Finset (TreeLeafIndex n))) =>
    (Real.exp_nonneg (cb - 1))) (fun j _ => hleaf j)
  simpa only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex, ← Real.exp_nat_mul,
    Fintype.prod_prod_type, Nat.cast_prod, Nat.cast_pow] using hp

/-- The actual weighted Fourier coefficient can be nonzero only above the
product cutoff. This uses the exact coefficient factorization, not an extra
support hypothesis on a surrogate coefficient. -/
theorem movingFrequencyCoefficient_log_product_lower {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (hvalue : ∀ a, 0 < value a) (k : ℕ)
    (outside : List ℕ) (cb cd : ℝ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n m : ℕ) (s : ℤ)
    (small : TreeLeafTuple (List σ) n) (slot : TreeLeafIndex n × Fin m → σ)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n (bulkSlotLeaves n m slot), tier i = k)
    (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n s small (bulkSlotLeaves n m slot) XL XR ≠ 0) :
    Real.exp ((2 ^ n : ℕ) * (cb - 1)) ≤ ((∏ i, value (slot i) : ℕ) : ℝ) := by
  rw [movingFrequencyCoefficient_bulk_log value tier k outside cb cd μ hμ childBound
    pivotBound V F φ G n s small (bulkSlotLeaves n m slot) hn hsmall hbulk XL XR] at h
  apply movingBulkTreeLogWeight_product_lower value hvalue outside cb cd n m slot
  exact_mod_cast left_ne_zero_of_mul h

/-- Pointwise removal is valid for one unsymmetrized coefficient. This is
used only after the harmonic diagonal has reduced to one-branch energy. -/
theorem movingFrequencyCoefficient_bulk_log_norm_le {σ : Type} [Fintype σ]
    (value tier : σ → ℕ) (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → σ → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n)
    (hn : n ≤ k) (hsmall : ∀ i ∈ flattenMovingSlots n small, tier i ≠ k)
    (hbulk : ∀ i ∈ flattenMovingSlots n bulk, tier i = k) (XL XR : ℕ) :
    ‖movingFrequencyCoefficient value outside μ childBound pivotBound V
      (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
      φ G n s small bulk XL XR‖ ≤
    ‖movingFrequencyCoefficient value outside μ childBound pivotBound V F
      φ G n s small bulk XL XR‖ := by
  rw [movingFrequencyCoefficient_bulk_log value tier k outside cb cd μ hμ
    childBound pivotBound V F φ G n s small bulk hn hsmall hbulk XL XR,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (movingBulkLeafProduct_bounds value outside cb cd n bulk).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (movingBulkLeafProduct_bounds value outside cb cd n bulk).2

end Ostmann

end OAI
