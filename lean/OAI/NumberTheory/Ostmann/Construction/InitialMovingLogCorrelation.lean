import OAI.NumberTheory.Ostmann.Construction.InitialMovingCoefficientPair
import OAI.NumberTheory.Ostmann.Construction.InitialMovingTemplateProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogCorrelation

namespace OAI

/-! # The literal half-cutoff correlation under the original regular law -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingTemplate_initial_log_correlation_eq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n a b d r : ℕ)
    (hlen : a + 4 * n = r + r) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (outside : List ℕ) (μ : ℕ → P → ℝ) (ν : MovingRegularSlot n a (b + b) → P → ℝ)
    (q : Fin (b + b) → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ)
    (childBound pivotBound V : ℕ → ℕ) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (active : MovingRegularSlot n a (b + b) → Bool)
    (greg : ∀ p : ℕ, ZMod p → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (u v w z center : ℝ) (perm : Equiv.Perm (TreeLeafIndex n × Fin (b + b))) :
    let slot := movingTemplateBulk n a (b + b)
    let bulk := movingPatternBulkLeaves n (b + b) slot perm
    let slots := fun side => if side then slot ∘ perm.symm else (slot : _ → _)
    let logSlots := initialPairedHalfLogSlots n b slots
    let leaf := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback) g Dq Finset.univ ψ X lo hi
    let coeff := fun s y x z => movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
      leaf φ G n a (b + b) s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
    let W := fun s => movingTemplateExternalMultiplier P hP n a (b + b) active outside greg s φ
      Jleft Jright diagonal
    let wgt := fun (y : MovingRegularSlot n a (b + b) → P) =>
      ((∏ j, bulkLogCutoffWeight (fun i => ((y i : ℕ) : ℝ)) cb (logSlots j) : ℝ) : ℂ)
    mixedExternalAverage ν (V n) u v w z center (fun s y x z =>
      (coeff s y x z * star (coeff s (selectedBulkSample slot perm y) x z)) * W s y x z) =
    ((initialLogSumWeight Subtype.val cd sl * initialLogSumWeight Subtype.val cd sr) ^
      (2 ^ n + 2 ^ n) : ℝ) *
      movingWeightedMatchedCorrelation q Subtype.val outside μ ν childBound pivotBound V
        (fun s => if s = 0 then 0 else 1) g Dq Finset.univ ψ X lo hi φ G n
        (movingTemplateSmall n a (b + b)) bulk (fun s y x z => wgt y * W s y x z) u v w z center := by
  intro slot bulk slots logSlots leaf coeff W wgt
  let plain := fun side (s : ℤ) (y : MovingRegularSlot n a (b + b) → P) (x z : ℝ) =>
    movingFrequencyCoefficient Subtype.val outside μ childBound pivotBound V
      (movingOriginalLeaf Subtype.val q (fun _ s => if s = 0 then 0 else 1)
        g Dq Finset.univ ψ X lo hi) φ G n s
      (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
      (treeLeafMap (List.map y) n (bulk side)) ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  change mixedExternalAverage ν (V n) u v w z center _ = _ *
    mixedExternalAverage ν (V n) u v w z center
      (fun s y x z => (plain false s y x z * star (plain true s y x z)) * (wgt y * W s y x z))
  apply mixedExternalAverage_support_const_mul
  intro y _ s x z
  have hp := movingOriginalCoefficientPair_initial_halves Subtype.val
    (fun p : P => (hP _ p.property).pos) b d r cb cd sl sr fallback q g Dq Finset.univ
    ψ X lo hi outside μ childBound pivotBound V φ G n a s
    (treeLeafMap (List.map y) n (movingTemplateSmall n a (b + b)))
    (fun side => y ∘ slots side)
    (movingLeafLengthEq_map y n _ a (bulkSlotLeaves_length_eq n a _)) hlen
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊
  dsimp only [coeff, leaf, plain, W, wgt, slot, bulk]
  unfold movingTemplateCoefficient
  rw [movingFrequencyCoefficient_bulk_action Subtype.val outside μ childBound pivotBound V _ φ G
    n (b + b) s (movingTemplateSmall n a (b + b)) (movingTemplateBulk n a (b + b)) perm y
    ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊ (movingTemplateSmall_not_bulk n a (b + b))]
  simp only [movingPatternBulkLeaves, Bool.false_eq_true, ite_false, ite_true, bulkSlotLeaves_map]
  have hlogs (j) : initialPairedHalfLogSlots n b (fun side => y ∘ slots side) j =
      (logSlots j).map y := initialPairedHalfLogSlots_map y n b slots j
  dsimp only [slots, slot] at hp hlogs
  simp only [Bool.false_eq_true, ite_false, ite_true] at hp
  rw [hp]
  simp_rw [hlogs]
  simp only [bulkLogCutoffWeight_map, Function.comp_def]
  ring

end Ostmann

end OAI
