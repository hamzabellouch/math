import OAI.NumberTheory.TwoPoint.Bounds.ObservedDesignationWeights
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
import OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyWeights
import OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum

namespace OAI

/-! Exact passage from divisibility centers to the common-carrier singleton formula. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma FiniteLaw.average_congr_on_support {A : Type*} [Fintype A]
    (μ : FiniteLaw A) {f g : A → ℝ} (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.average f = μ.average g := by
  apply sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

noncomputable def forcedResidue (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (offset : ℤ) : Fin B :=
  letI : NeZero p := ⟨hp.ne'⟩
  ⟨(- (offset : ZMod p)).val, (ZMod.val_lt _).trans_le hpB⟩

lemma forcedResidue_lt (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (offset : ℤ) :
    (forcedResidue B p hp hpB offset).val < p := by
  let : NeZero p := ⟨hp.ne'⟩
  exact ZMod.val_lt _

lemma divisor_test_iff_forcedResidue (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (offset : ℤ) (z : Fin B) (hz : z.val < p) :
    (p : ℤ) ∣ (z.val : ℤ) + offset ↔ z = forcedResidue B p hp hpB offset := by
  let : NeZero p := ⟨hp.ne'⟩
  have he : (p : ℤ) ∣ (z.val : ℤ) + offset ↔
      (z.val : ZMod p) = -(offset : ZMod p) :=
    residue_offset_divisibility (z.val : ZMod p) (z.val : ℤ) offset (by simp)
  rw [he]
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hz, forcedResidue] using hv
  · intro h
    subst z
    exact ZMod.natCast_zmod_val _

/-- The equality is needed only on the support of the product law. Values
in the common carrier above a coordinate's modulus have zero mass. -/
theorem uniform_divisor_word_average {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (offset : τ → ℤ) (R : ℝ) (G : (ι → Fin B) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R * (∏ t,
        ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
          (p (label t) : ℝ)⁻¹)) * G z) =
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R * (∏ t,
        ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
          then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G z) := by
  apply FiniteLaw.average_congr_on_support
  intro z hz
  have hs := (uniformResidueLaw_independent_support B p hp hpB z).mp hz
  have he (t : τ) := divisor_test_iff_forcedResidue B (p (label t)) (hp _) (hpB _)
    (offset t) (z (label t)) (hs (label t))
  simp only [he]

abbrev ColumnPrimeCoordinate {J : ℕ} (P : Fin J → Finset ℕ) := Σ j, P j

def tupleSlotLabel {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (t : Fin R × Fin J) : ColumnPrimeCoordinate P :=
  ⟨t.2, w t.2 t.1⟩

/-- Flatten the actual product of family centers without changing either
the numerical prime labels or their repeated residue coordinates. -/
lemma familyCenter_word_product {J R B : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (offset : Fin R → ℤ)
    (z : ColumnPrimeCoordinate P → Fin B) :
    (∏ i, familyCenter (fun _ p => p.val)
      (fun j p => ((z ⟨j, p⟩).val : ℤ)) (fun j => w j i) (offset i)) =
      ∏ t : Fin R × Fin J,
        ((if ((tupleSlotLabel w t).2.val : ℤ) ∣
          ((z (tupleSlotLabel w t)).val : ℤ) + offset t.1 then (1 : ℝ) else 0) -
            ((tupleSlotLabel w t).2.val : ℝ)⁻¹) := by
  rw [Fintype.prod_prod_type]
  rfl

end TwoPointCorrelations

end OAI
