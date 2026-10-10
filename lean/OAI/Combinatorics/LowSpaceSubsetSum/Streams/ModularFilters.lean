import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace OAI

/-!
# Nested filters and enumeration of parent residue classes

The congruence and finite-loop facts used by both trials. No coprimality of
the low modulus and the additional prime is required.
-/

namespace LowSpaceSubsetSum

/-- A passing parent and first child force the second child's low filter. -/
theorem nested_second_child_filter {p p0 x1 x2 w rho : ℤ}
    (hdiv : p ∣ p0) (hparent : x1 + x2 ≡ w [ZMOD p0])
    (hchild : x1 ≡ rho [ZMOD p]) : x2 ≡ w - rho [ZMOD p] := by
  have h := (hparent.of_dvd hdiv).sub hchild
  convert h using 1
  ring

/-- Every lifted class has the prescribed low residue. -/
theorem lift_low_residue {p rho z : ℕ} (hrho : rho < p) :
    (rho + p * z) % p = rho := by
  simp [Nat.add_mod, Nat.mod_eq_of_lt hrho]

/-- The program's lift lies within the product modulus. -/
theorem lift_lt_product {p q rho z : ℕ} (hrho : rho < p) (hz : z < q) :
    rho + p * z < p * q := by
  have hz' : z + 1 ≤ q := by omega
  have hp := Nat.mul_le_mul_left p hz'
  nlinarith

/-- All product-modulus residues with a given low base occur exactly once in
the loop over `z < q`, including when `q` and `p` have a common factor. -/
theorem lift_residue_exists_unique {p q rho r : ℕ}
    (hp : 0 < p) (hr : r < p * q) (hbase : r % p = rho) :
    ∃! z : ℕ, z < q ∧ r = rho + p * z := by
  have hz : r / p < q := (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using hr)
  have heq : r = rho + p * (r / p) := by
    have h := Nat.mod_add_div r p
    omega
  refine ⟨r / p, ⟨hz, heq⟩, ?_⟩
  intro z hz'
  have hprod : p * z = p * (r / p) := by omega
  exact Nat.eq_of_mul_eq_mul_left hp hprod

/-- Complementing the target gives a bijection of the product residue ring. -/
theorem complementary_residue_injective {P t : ℤ} {x y : ℤ}
    (hx : 0 ≤ x ∧ x < P) (hy : 0 ≤ y ∧ y < P)
    (h : (t - x) % P = (t - y) % P) : x = y := by
  have hm : t - x ≡ t - y [ZMOD P] := h
  have hxym := hm.neg.add_left t
  have hxy : x % P = y % P := by
    change x ≡ y [ZMOD P]
    convert hxym using 1 <;> ring
  rwa [Int.emod_eq_of_lt hx.1 hx.2, Int.emod_eq_of_lt hy.1 hy.2] at hxy

end LowSpaceSubsetSum

end OAI
