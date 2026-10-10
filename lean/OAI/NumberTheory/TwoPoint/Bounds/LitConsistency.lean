import OAI.NumberTheory.TwoPoint.Bounds.PartialCentering
import OAI.NumberTheory.TwoPoint.Bounds.OccurrenceCounts

namespace OAI

/-! Compress all lit tests for one prime into one forced residue, or zero. -/

namespace TwoPointCorrelations

open Finset

variable {ι τ A : Type*} [DecidableEq ι] [DecidableEq A]

def LitConsistent (L : Finset τ) (label : τ → ι) (target : τ → A) : Prop :=
  ∀ t ∈ L, ∀ u ∈ L, label t = label u → target t = target u

noncomputable def litForcedTarget (L : Finset τ) (label : τ → ι) (target : τ → A)
    (base : ι → A) (i : ι) : A := by
  classical
  exact if hi : ∃ t ∈ L, label t = i then target (Classical.choose hi) else base i

omit [DecidableEq A] in
lemma litForcedTarget_at (L : Finset τ) (label : τ → ι) (target : τ → A)
    (base : ι → A) (hL : LitConsistent L label target) (t : τ) (ht : t ∈ L) :
    litForcedTarget L label target base (label t) = target t := by
  classical
  have hex : ∃ u ∈ L, label u = label t := ⟨t, ht, rfl⟩
  simp only [litForcedTarget, dite_eq_left hex]
  exact hL _ (Classical.choose_spec hex).1 t ht (Classical.choose_spec hex).2

/-- Repetitions of the same lit residue test contribute just one indicator. -/
lemma lit_indicator_product (L : Finset τ) (label : τ → ι) (target : τ → A)
    (base : ι → A) (hL : LitConsistent L label target) (x : ι → A) :
    (∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) =
      ∏ i ∈ L.image label, if x i = litForcedTarget L label target base i then (1 : ℝ) else 0 := by
  classical
  have hall : (∀ t ∈ L, x (label t) = target t) ↔
      ∀ i ∈ L.image label, x i = litForcedTarget L label target base i := by
    constructor
    · intro hx i hi
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hi
      rw [litForcedTarget_at L label target base hL t ht]
      exact hx t ht
    · intro hx t ht
      have hi := hx (label t) (mem_image.mpr ⟨t, ht, rfl⟩)
      rwa [litForcedTarget_at L label target base hL t ht] at hi
  simp only [Finset.prod_boole, hall]

omit [DecidableEq ι] in
/-- Incompatible lit offsets give exactly zero before any estimate. -/
lemma lit_indicator_product_eq_zero (L : Finset τ) (label : τ → ι) (target : τ → A)
    (hL : ¬LitConsistent L label target) (x : ι → A) :
    (∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) = 0 := by
  classical
  have hno : ¬∀ t ∈ L, x (label t) = target t := by
    intro hx
    apply hL
    intro t ht u hu htu
    exact (hx t ht).symm.trans (htu ▸ hx u hu)
  rw [Finset.prod_boole, ite_eq_right hno]

end TwoPointCorrelations

end OAI
