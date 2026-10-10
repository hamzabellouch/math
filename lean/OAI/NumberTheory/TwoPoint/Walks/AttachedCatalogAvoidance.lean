import OAI.NumberTheory.TwoPoint.Walks.ProhibitedFamilyWitnesses
import OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference

namespace OAI

/-! The attached minimal-word catalog is the actual vertex-deletion indicator. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma attachedResiduePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h B : ℕ)
    (w : List SignedStep) (a n : ℤ) (x : ι → Fin B)
    (hn : ∀ i, (n : ZMod (p i)) = ((x i).val : ZMod (p i)))
    (hsq : ∀ t ∈ w, Squarefree (t.padding * t.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    AttachedResiduePositiveWord p h w a B x ↔ PositiveWord h (n + a) w := by
  let r (i : ι) : ZMod (p i) := ((x i).val : ZMod (p i)) + (a : ZMod (p i))
  have hr : ∀ i, ((n + a : ℤ) : ZMod (p i)) = r i := by
    intro i
    simp only [Int.cast_add, hn, r]
  rw [← residuePositiveWord_iff p h w r (n + a) hr hsq hcover]
  constructor
  · intro ht k i hi
    change ((x i).val : ZMod (p i)) + (a : ZMod (p i)) = _
    rw [ht k i hi, Int.cast_add]
    ring
  · intro ht k i hi
    have he := ht k i hi
    change ((x i).val : ZMod (p i)) + (a : ZMod (p i)) = _ at he
    change ((x i).val : ZMod (p i)) = _
    rw [Int.cast_add]
    calc
      _ = (((x i).val : ZMod (p i)) + (a : ZMod (p i))) - a := by ring
      _ = _ := by rw [he]; ring

noncomputable def attachedCatalogAvoidance {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (x : ↥(F.P ∪ F.Q) → Fin B) : ℝ :=
  witnessAvoidance
    (fun a : Fin (D + 1) × ProhibitedCatalog F.pairs h s => fun z => decide
      (AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
        (decodeStepWord a.2.val) (wordDisplacement h (main.take (min a.1.val main.length))) B z)) x

theorem attachedCatalogAvoidance_ne_zero_iff {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x ≠ 0 ↔
      ∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v)) := by
  have htest (a : Fin (D + 1) × ProhibitedCatalog F.pairs h s) :
      AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
        (decodeStepWord a.2.val) (wordDisplacement h (main.take (min a.1.val main.length))) B x ↔
      PositiveWord h (n + wordDisplacement h (main.take (min a.1.val main.length)))
        (decodeStepWord a.2.val) := by
    apply attachedResiduePositiveWord_iff _ h B _ _ n x hn
    · exact F.catalog_whole_squarefree s a.2
    · intro q hq
      exact ⟨⟨q, F.support_subset s a.2 hq⟩, rfl⟩
  have hne : attachedCatalogAvoidance F s B D main x ≠ 0 ↔
      ∀ a : Fin (D + 1) × ProhibitedCatalog F.pairs h s,
        ¬PositiveWord h (n + wordDisplacement h (main.take (min a.1.val main.length)))
          (decodeStepWord a.2.val) := by
    unfold attachedCatalogAvoidance witnessAvoidance
    rw [prod_ne_zero_iff]
    constructor
    · intro hx a ha
      have hz := hx a (mem_univ a)
      have ht := (htest a).mpr ha
      simp [ht] at hz
    · intro hx a _
      have ht : ¬AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
          (decodeStepWord a.2.val)
          (wordDisplacement h (main.take (min a.1.val main.length))) B x :=
        fun hp => hx a ((htest a).mp hp)
      simp [ht]
  rw [hne]
  constructor
  · intro ha v hv ⟨w, hw, hm⟩
    obtain ⟨c, hc⟩ := stepWord_covered F.pairs s w hm.1.2.1 hm.1.2.2.1
    have hcm : MinimalWord (ForwardProhibited h s (fun d q => (d, q) ∈ F.pairs))
        (decodeStepWord c) := by rw [hc]; exact hm
    have hh := ha (⟨v, by omega⟩, ⟨c, hcm⟩)
    rw [min_eq_left hv, hc] at hh
    exact hh hw
  · intro ha a hw
    exact ha (min a.1.val main.length) (Nat.min_le_right _ _)
      ⟨decodeStepWord a.2.val, hw, a.2.property⟩

end TwoPointCorrelations

end OAI
