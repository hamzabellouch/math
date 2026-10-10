import OAI.NumberTheory.TwoPoint.Bounds.ActualCodeAssignments

namespace OAI

/-! A single finite universe covers all numerical words with bounded prime slots. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

/-- Slot count, complete equality-pattern code, and separate prime-pool assignments. -/
abbrev PrimeWordEncoding (R T : ℕ) (P Q : Finset ℕ) :=
  (n : Fin (T + 1)) × (c : CrudeWordCode R n.val R) ×
    (c.tupleClasses → P) × ({z : c.usedClasses // z ∉ c.tupleClasses} → Q)

namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}

def decode (e : PrimeWordEncoding R T P Q) : List SignedStep :=
  e.2.1.numericalWord (joinCoordinates e.2.1.tupleClasses
    (fun z => (e.2.2.1 z).val) (fun z => (e.2.2.2 z).val))

noncomputable def weight (e : PrimeWordEncoding R T P Q) : ℝ :=
  ∏ z : e.2.1.usedClasses, ((joinCoordinates e.2.1.tupleClasses
    (fun z => (e.2.2.1 z).val) (fun z => (e.2.2.2 z).val) z : ℕ) : ℝ)⁻¹

lemma weight_nonneg (e : PrimeWordEncoding R T P Q) : 0 ≤ e.weight := by
  unfold weight
  exact prod_nonneg (fun _ _ => by positivity)

/-- No loss in the reciprocal weight occurs on encoding an actual word. -/
theorem covers (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    ∃ e : PrimeWordEncoding R T P Q, e.decode = List.ofFn w ∧
      e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
      Function.Injective (fun z => (e.2.2.1 z).val) ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  obtain ⟨a, b, hab⟩ := actual_code_pool_assignments w P Q hP hQ
  let c := (actualPrimeSlotData w).code
  let e : PrimeWordEncoding R T P Q :=
    ⟨⟨Fintype.card (ActualPrimeSlot w), by omega⟩, c, a, b⟩
  refine ⟨e, ?_, actualPrimeSlotData_code_kindConsistent w hd,
    actualPrimeSlotData_code_rowInjective w, ?_, ?_⟩
  · change c.numericalWord (joinCoordinates c.tupleClasses
      (fun z => (a z).val) (fun z => (b z).val)) = _
    rw [hab, CrudeWordCode.numericalWord_encode]
    exact actualPrimeSlotData_word w ht hq
  · have ha (z : c.tupleClasses) : (a z).val = (actualPrimeSlotData w).prime z.val.val := by
      have hz := congrFun hab z.val
      simpa only [joinCoordinates_mem] using hz
    intro u v huv
    apply Subtype.ext
    apply (actualPrimeSlotData w).code_value_injective
    change (actualPrimeSlotData w).prime u.val.val = (actualPrimeSlotData w).prime v.val.val
    exact (ha u).symm.trans (huv.trans (ha v))
  · change (∏ z : c.usedClasses, ((joinCoordinates c.tupleClasses
      (fun z => (a z).val) (fun z => (b z).val) z : ℕ) : ℝ)⁻¹) = _
    rw [hab]
    exact actual_code_reciprocal_weight w (fun i => (ht i).ne_zero) (fun i => (hq i).ne_zero)

end PrimeWordEncoding

/-- A finite decoding cover also covers every nonnegative weighted sum.
The chosen representatives are injective because decoding recovers the word. -/
theorem finite_decoding_weight_bound {W C : Type*} [DecidableEq W] [Fintype C]
    (F : Finset W) (decode : C → W) (weight : W → ℝ) (cost : C → ℝ)
    (hcost : ∀ c, 0 ≤ cost c)
    (hcover : ∀ w ∈ F, ∃ c, decode c = w ∧ weight w ≤ cost c) :
    (∑ w ∈ F, weight w) ≤ ∑ c, cost c := by
  let choose (w : F) : C := Classical.choose (hcover w.val w.property)
  have hchoose (w : F) : decode (choose w) = w.val ∧ weight w.val ≤ cost (choose w) :=
    Classical.choose_spec (hcover w.val w.property)
  have hinj : Function.Injective choose := by
    intro u v h
    apply Subtype.ext
    exact (hchoose u).1.symm.trans ((congrArg decode h).trans (hchoose v).1)
  calc
    _ = ∑ w : F, weight w.val := (Finset.sum_coe_sort F weight).symm
    _ ≤ ∑ c, cost c := sum_le_sum_of_injOn choose
      (fun u _ v _ h => hinj h) (subset_univ _)
      (fun w _ => (hchoose w).2) (fun c _ _ => hcost c)

end TwoPointCorrelations

end OAI
