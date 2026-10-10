import OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
import OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift

namespace OAI

/-! Evaluate the actual padding-periodic weights at one common integer lift of the product-law sample. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open Finset
open scoped Classical

theorem exists_residue_origin {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    ∃ n : ℤ, ∀ p : ↥(data.P ∪ data.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val) := by
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  apply exists_common_integer_residue (fun p : ↥(data.P ∪ data.Q) => p.val)
  intro p q hpq
  exact (Nat.coprime_primes (data.prime p) (data.prime q)).mpr
    (fun he => hpq (Subtype.ext he))

noncomputable def residueOrigin {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) : ℤ :=
  (data.exists_residue_origin x).choose

lemma residueOrigin_spec {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) :
    (data.residueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_residue_origin x).choose_spec p

lemma residueOrigin_divisibility {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) (offset : ℤ) :
    (p.val : ℤ) ∣ data.residueOrigin x + offset ↔
      (p.val : ℤ) ∣ (x p).val + offset := by
  exact (residue_offset_divisibility _ _ _ (data.residueOrigin_spec x p)).trans
    (residue_offset_divisibility ((x p).val : ZMod p.val) ((x p).val : ℤ) offset
      (by simp)).symm

noncomputable def residueValue {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (f : ℤ → ℝ) (x : ↥(data.P ∪ data.Q) → Fin B) : ℝ := f (data.residueOrigin x)

theorem residueValue_eq_of_lift {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (f : ℤ → ℝ)
    (hf : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → f n = f m)
    (x : ↥(data.P ∪ data.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(data.P ∪ data.Q), p.val ∈ data.Q →
      (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    data.residueValue f x = f n := by
  apply hf
  intro q hq
  let p : ↥(data.P ∪ data.Q) := ⟨q, mem_union_right _ hq⟩
  exact (data.residueOrigin_spec x p).trans (hn p hq).symm

theorem residueValue_independent_tuple {h J M B : ℕ} {τ : Type*} [Fintype τ]
    (data : ProhibitedPrimeFamily h J M) (label : τ → ↥(data.P ∪ data.Q))
    (hlabel : ∀ p ∈ univ.image label, p.val ∈ data.P)
    (f : ℤ → ℝ)
    (hf : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → f n = f m)
    (x y : ↥(data.P ∪ data.Q) → Fin B)
    (hxy : ∀ p, p ∉ univ.image label → x p = y p) :
    data.residueValue f x = data.residueValue f y := by
  apply hf
  intro q hq
  let p : ↥(data.P ∪ data.Q) := ⟨q, mem_union_right _ hq⟩
  have hp : p ∉ univ.image label := by
    intro hp
    exact disjoint_left.mp data.disjoint (hlabel p hp) hq
  rw [data.residueOrigin_spec x p, data.residueOrigin_spec y p, hxy p hp]

end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI
