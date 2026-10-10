import OAI.NumberTheory.TwoPoint.Bounds.CRTComparison
import Mathlib.RingTheory.Coprime.Lemmas

namespace OAI

/-! One integer realizes all coordinates of a common residue configuration. -/

namespace TwoPointCorrelations

open Finset

/-- This is a simultaneous lift of the entire configuration. It is used
after forming a hybrid, so different witness sites keep the same origin. -/
theorem exists_common_integer_residue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ∀ i, ZMod (p i)) :
    ∃ n : ℤ, ∀ i, (n : ZMod (p i)) = r i := by
  let y : ZMod (∏ i, p i) := (ZMod.prodEquivPi p hcop).symm r
  refine ⟨(y.val : ℤ), ?_⟩
  intro i
  calc
    ((y.val : ℤ) : ZMod (p i)) =
        ZMod.prodEquivPi p hcop ((y.val : ℕ) : ZMod (∏ i, p i)) i := by
      simp only [Int.cast_natCast, ZMod.prodEquivPi_apply, map_natCast]
    _ = ZMod.prodEquivPi p hcop y i := by rw [ZMod.natCast_zmod_val]
    _ = r i := congrFun ((ZMod.prodEquivPi p hcop).apply_symm_apply r) i

/-- Prime divisibility at any offset is read from that same lifted origin. -/
lemma residue_offset_divisibility {p : ℕ} (r : ZMod p) (n offset : ℤ)
    (hn : (n : ZMod p) = r) :
    (p : ℤ) ∣ n + offset ↔ r = -(offset : ZMod p) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, hn, add_eq_zero_iff_eq_neg]

/-- The conjunction of all prime-power coordinate tests is exactly
divisibility by their product. No independence across sites is required. -/
lemma residue_product_divisibility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ∀ i, ZMod (p i)) (n offset : ℤ) (hn : ∀ i, (n : ZMod (p i)) = r i)
    (S : Finset ι) :
    ((∏ i ∈ S, p i : ℕ) : ℤ) ∣ n + offset ↔
      ∀ i ∈ S, r i = -(offset : ZMod (p i)) := by
  rw [Nat.cast_prod]
  constructor
  · intro hd i hi
    apply (residue_offset_divisibility (r i) n offset (hn i)).mp
    exact (dvd_prod_of_mem (fun j => (p j : ℤ)) hi).trans hd
  · intro ht
    apply prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (hcop hij).cast (R := ℤ)
    · intro i hi
      exact (residue_offset_divisibility (r i) n offset (hn i)).mpr (ht i hi)

end TwoPointCorrelations

end OAI
