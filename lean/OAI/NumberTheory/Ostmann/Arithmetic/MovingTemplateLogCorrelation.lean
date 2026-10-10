import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalLogCoefficientPair
import OAI.NumberTheory.Ostmann.Arithmetic.MovingWeightedMatchedCorrelation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateExternalMultiplier
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalBulkAction
import OAI.NumberTheory.Ostmann.Characters.MixedExternalStatistic

namespace OAI

/-! # The retained log weights in the original masked coefficient correlation -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem mixedExternalAverage_support_const_mul {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v a b center : ℝ) (c : ℂ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (h : ∀ y, (∏ j, ν j (y j)) ≠ 0 → ∀ s x z, F s y x z = c * H s y x z) :
    mixedExternalAverage ν N u v a b center F =
      c * mixedExternalAverage ν N u v a b center H := by
  unfold mixedExternalAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : (∏ j, ν j (y j)) = 0
  · simp only [hy, Complex.ofReal_zero, zero_mul, mul_zero]
  · simp_rw [h y hy, complexIntegerInterval_const_mul, complexPrimeInterval_const_mul]
    ring

theorem movingTemplate_log_correlation_eq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n r m k : ℕ) (hn : n ≤ k)
    (tier : P → ℕ) (outside : List ℕ) (cb cd : ℝ)
    (μ : ℕ → P → ℝ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    (ν : MovingRegularSlot n r m → P → ℝ)
    (hsmall : ∀ y : MovingRegularSlot n r m → P, (∏ j, ν j (y j)) ≠ 0 → ∀ j : TreeLeafIndex n × Fin r,
      tier (y (j.1, .inl j.2)) ≠ k)
    (hbulk : ∀ y : MovingRegularSlot n r m → P, (∏ j, ν j (y j)) ≠ 0 → ∀ j : TreeLeafIndex n × Fin m,
      tier (y (j.1, .inr j.2)) = k)
    (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
    (g : ∀ i, ZMod (p i) → ℂ) (Dq : ∀ i, (ZMod (p i))ˣ)
    (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (active : MovingRegularSlot n r m → Bool) (greg : ∀ q : ℕ, ZMod q → ℂ)
    (Jleft Jright : ℝ) (diagonal : Bool) (u v a b center : ℝ)
    (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) :
    let slot := movingTemplateBulk n r m
    let bulk := movingPatternBulkLeaves n m slot perm
    let leaf := movingOriginalLeaf Subtype.val p
      (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
      g Dq Finset.univ ψ X lo hi
    let coeff := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      leaf φ G n r m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    let W := fun s => movingTemplateExternalMultiplier P hP n r m active outside greg s φ Jleft Jright diagonal
    let wgt := fun y => ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb
      (movingBulkPairedCutoffSlots n bulk j) : ℝ) : ℂ)
    mixedExternalAverage ν (V n) u v a b center (fun s y x z =>
      (coeff s y x z * star (coeff s (selectedBulkSample slot perm y) x z)) * W s y x z) =
    (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ (2 ^ n + 2 ^ n) : ℝ) *
      movingWeightedMatchedCorrelation p Subtype.val outside μ ν childBound pivotBound V f g Dq Finset.univ
        ψ X lo hi φ G n (movingTemplateSmall n r m) bulk
        (fun s y x z => wgt y * W s y x z) u v a b center := by
  intro slot bulk leaf coeff W wgt
  let plain := fun side (s : ℤ) (y : MovingRegularSlot n r m → P) (x z : ℝ) =>
    movingFrequencyCoefficient Subtype.val outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val p (fun _ => f) g Dq Finset.univ ψ X lo hi) φ G n s
      (treeLeafMap (List.map y) n (movingTemplateSmall n r m))
      (treeLeafMap (List.map y) n (bulk side)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  change mixedExternalAverage ν (V n) u v a b center
    (fun s y x z => (coeff s y x z * star (coeff s (selectedBulkSample slot perm y) x z)) * W s y x z) =
    (logCellProfile ((outside.map (fun p => Real.log (p : ℝ))).sum - cd) ^ (2 ^ n + 2 ^ n) : ℝ) *
      mixedExternalAverage ν (V n) u v a b center
        (fun s y x z => (plain false s y x z * star (plain true s y x z)) * (wgt y * W s y x z))
  apply mixedExternalAverage_support_const_mul
  intro y hy s x z
  have hs : ∀ i ∈ flattenMovingSlots n
      (treeLeafMap (List.map y) n (movingTemplateSmall n r m)), tier i ≠ k := by
    intro i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n r _ j).mp hj
    exact hsmall y hy j
  have hb : ∀ side i, i ∈ flattenMovingSlots n
      (treeLeafMap (List.map y) n (movingPatternBulkLeaves n m (movingTemplateBulk n r m) perm side)) → tier i = k := by
    intro side i hi
    rw [flattenMovingSlots_map] at hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    cases side
    · obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m _ j).mp hj
      exact hbulk y hy j
    · obtain ⟨j, rfl⟩ := (mem_flatten_bulkSlotLeaves n m _ j).mp hj
      exact hbulk y hy (perm.symm j)
  have hp := movingOriginalCoefficientPair_bulk_log Subtype.val tier
    (fun q : P => (hP _ q.property).pos) k outside cb cd μ hμ p (fun _ => f) g Dq Finset.univ
    ψ X lo hi childBound pivotBound V φ G n s
    (treeLeafMap (List.map y) n (movingTemplateSmall n r m))
    (fun side => treeLeafMap (List.map y) n (movingPatternBulkLeaves n m (movingTemplateBulk n r m) perm side))
    hn hs hb ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  dsimp only [coeff, leaf, plain, W, wgt, slot, bulk]
  unfold movingTemplateCoefficient
  rw [movingFrequencyCoefficient_bulk_action Subtype.val outside μ childBound pivotBound V _ φ G
    n m s (movingTemplateSmall n r m) (movingTemplateBulk n r m) perm y
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ (movingTemplateSmall_not_bulk n r m)]
  dsimp only at hp
  have hfalse : movingPatternBulkLeaves n m (movingTemplateBulk n r m) perm false =
      bulkSlotLeaves n m (movingTemplateBulk n r m) := rfl
  have htrue : movingPatternBulkLeaves n m (movingTemplateBulk n r m) perm true =
      bulkSlotLeaves n m (movingTemplateBulk n r m ∘ perm.symm) := rfl
  rw [hfalse, htrue] at hp ⊢
  rw [hp]
  simp only [movingBulkPairedCutoffSlots_map, bulkLogCutoffWeight_map, Function.comp_def]
  ring

end Ostmann

end OAI
