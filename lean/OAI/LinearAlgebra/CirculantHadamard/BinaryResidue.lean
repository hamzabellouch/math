import OAI.LinearAlgebra.CirculantHadamard.FirstOrderResidue
import OAI.LinearAlgebra.CirculantHadamard.ResidueTorsion
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Ring

namespace OAI

universe uO uk uIota

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

/-- The coefficient of the ratio `d / c` along `2`. Division by `c` means
multiplication by the inverse of the supplied unit. -/
def binaryLr (c : Oˣ) (b : O) : O :=
  -b * (↑(c⁻¹) : O)

/-- The coefficient of the ratio `g / c` along `1 + i`. -/
def binaryLw (c : Oˣ) (i b J U : O) : O :=
  i * b * (↑(c⁻¹) : O) - J * (↑(c⁻¹) : O) -
    (1 - i) * U * (↑(c⁻¹) : O)

theorem binary_ratio_r (c d : Oˣ) (a b : O)
    (hc : (c : O) = a + b) (hd : (d : O) = a - b) :
    ((d * c⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr c b := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  calc
    ((d * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + 2 * (-b * (↑(c⁻¹) : O)) := by
      change (d : O) * (↑(c⁻¹) : O) = _
      rw [hd]
      ring
    _ = 1 + (2 : O) * binaryLr c b := by rw [hc']; rfl

theorem binary_ratio_w (c g : Oˣ) (a b J U i : O)
    (hc : (c : O) = a + b)
    (hg : (g : O) = a + i * b - ((1 + i) * J + 2 * U))
    (hi : i ^ 2 = -1) :
    ((g * c⁻¹ : Oˣ) : O) = 1 + (1 + i) * binaryLw c i b J U := by
  have hc' : (a + b) * (↑(c⁻¹) : O) = 1 := by
    rw [← hc]
    exact c.mul_inv
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  calc
    ((g * c⁻¹ : Oˣ) : O) =
        (a + b) * (↑(c⁻¹) : O) + (1 + i) * binaryLw c i b J U -
          (i * i + 1) * (b + U) * (↑(c⁻¹) : O) := by
      change (g : O) * (↑(c⁻¹) : O) = _
      rw [hg]
      unfold binaryLw
      ring
    _ = 1 + (1 + i) * binaryLw c i b J U := by rw [hc', hi']; ring

/-- This identity is exact before applying the residue map. -/
theorem binaryLr_add_binaryLw (c : Oˣ) (i b J U : O) :
    binaryLr c b + binaryLw c i b J U =
      -J * (↑(c⁻¹) : O) - (1 - i) * (b + U) * (↑(c⁻¹) : O) := by
  unfold binaryLr binaryLw
  ring

/-- Nonvanishing of `2` also makes the second first-order parameter nonzero. -/
theorem binary_one_add_i_ne_zero (i : O) (hi : i ^ 2 = -1)
    (h2 : (2 : O) ≠ 0) : 1 + i ≠ 0 := by
  have hi' : i * i = -1 := by simpa only [pow_two] using hi
  have hfactor : (1 + i) * (1 - i) = (2 : O) := by
    calc
      (1 + i) * (1 - i) = 1 - i * i := by ring
      _ = 2 := by rw [hi']; ring
  intro hzero
  apply h2
  rw [← hfactor, hzero, zero_mul]

section Domain

variable [IsDomain O]

/-- The displayed coefficient is the unique coefficient along `2`. -/
theorem binaryLr_unique (c d : Oˣ) (a b L : O)
    (hc : (c : O) = a + b) (hd : (d : O) = a - b)
    (h2 : (2 : O) ≠ 0)
    (hL : ((d * c⁻¹ : Oˣ) : O) = 1 + (2 : O) * L) :
    L = binaryLr c b := by
  apply mul_left_cancel₀ h2
  exact add_left_cancel (hL.symm.trans (binary_ratio_r c d a b hc hd))

/-- The displayed coefficient is the unique coefficient along `1 + i`. -/
theorem binaryLw_unique (c g : Oˣ) (a b J U i L : O)
    (hc : (c : O) = a + b)
    (hg : (g : O) = a + i * b - ((1 + i) * J + 2 * U))
    (hi : i ^ 2 = -1) (h2 : (2 : O) ≠ 0)
    (hL : ((g * c⁻¹ : Oˣ) : O) = 1 + (1 + i) * L) :
    L = binaryLw c i b J U := by
  apply mul_left_cancel₀ (binary_one_add_i_ne_zero i hi h2)
  exact add_left_cancel (hL.symm.trans (binary_ratio_w c g a b J U i hc hg hi))

end Domain

section Residue

variable {k : Type uk} [Field k] [charTwo : CharP k 2]

/-- The two coefficients have residues summing to the residue of `J / c`. -/
theorem binary_residue_sum (φ : O →+* k) (c : Oˣ) (i b J U : O)
    (hi : φ i = 1) :
    φ (binaryLr c b) + φ (binaryLw c i b J U) =
      φ (J * (↑(c⁻¹) : O)) := by
  rw [← map_add, binaryLr_add_binaryLw]
  simp [hi, CharTwo.neg_eq]

omit charTwo in
/-- A signed product of units with residue one again has residue one.
The powers are formed in the unit group, including for negative exponents. -/
theorem binary_signed_product_residue_one [CharP k 2] {ι : Type uIota}
    (φ : O →+* k) (s : Finset ι) (u : ι → Oˣ) (ε : ι → ℤ)
    (hu : ∀ j ∈ s, φ (u j : O) = 1) :
    φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 := by
  let f : Oˣ →* kˣ := Units.map φ.toMonoidHom
  have hf (j : ι) (hj : j ∈ s) : f (u j) = 1 := by
    apply Units.ext
    change φ (u j : O) = 1
    exact hu j hj
  have hp : f (∏ j ∈ s, (u j) ^ (ε j)) = 1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro j hj
    rw [map_zpow, hf j hj, one_zpow]
  have hval := congrArg (fun z : kˣ => (z : k)) hp
  change φ ((∏ j ∈ s, (u j) ^ (ε j) : Oˣ) : O) = 1 at hval
  exact hval

variable [IsDomain O]

/-- The same-residue-field contradiction for a finite signed family of
binary decompositions. All arithmetic input to the concrete application is
explicit: unit decompositions, a square root of `-1`, odd torsion of both
signed products, and a nonzero signed `J / c` residue sum. -/
theorem binary_residue_contradiction {ι : Type uIota}
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) (hφi : φ i = 1)
    (h2 : (2 : O) ≠ 0) (s : Finset ι) (ε : ι → ℤ)
    (c d g : ι → Oˣ) (a b J U : ι → O)
    (hc : ∀ j ∈ s, (c j : O) = a j + b j)
    (hd : ∀ j ∈ s, (d j : O) = a j - b j)
    (hg : ∀ j ∈ s,
      (g j : O) = a j + i * b j - ((1 + i) * J j + 2 * U j))
    (hrOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hwOdd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) ^ m = 1)
    (hnonzero : (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) ≠ 0) :
    False := by
  have hφ2 : φ (2 : O) = 0 := by
    calc
      φ (2 : O) = φ (1 + 1) := by congr 1; ring
      _ = (1 : k) + 1 := by simp only [map_add, map_one]
      _ = 0 := CharTwo.add_self_eq_zero 1
  have hφpi : φ (1 + i) = 0 := by
    rw [map_add, map_one, hφi]
    exact CharTwo.add_self_eq_zero 1
  have hr (j : ι) (hj : j ∈ s) :
      ((d j * (c j)⁻¹ : Oˣ) : O) = 1 + (2 : O) * binaryLr (c j) (b j) :=
    binary_ratio_r (c j) (d j) (a j) (b j) (hc j hj) (hd j hj)
  have hw (j : ι) (hj : j ∈ s) :
      ((g j * (c j)⁻¹ : Oˣ) : O) =
        1 + (1 + i) * binaryLw (c j) i (b j) (J j) (U j) :=
    binary_ratio_w (c j) (g j) (a j) (b j) (J j) (U j) i (hc j hj) (hg j hj) hi
  have hrMap (j : ι) (hj : j ∈ s) : φ ((d j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hr j hj, map_add, map_one, map_mul, hφ2, zero_mul, add_zero]
  have hwMap (j : ι) (hj : j ∈ s) : φ ((g j * (c j)⁻¹ : Oˣ) : O) = 1 := by
    rw [hw j hj, map_add, map_one, map_mul, hφpi, zero_mul, add_zero]
  have hrOne : (∏ j ∈ s, (d j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => d j * (c j)⁻¹) ε hrMap) hrOdd
  have hwOne : (∏ j ∈ s, (g j * (c j)⁻¹) ^ (ε j)) = 1 :=
    units_eq_one_of_residue_one_of_odd φ _
      (binary_signed_product_residue_one φ s (fun j => g j * (c j)⁻¹) ε hwMap) hwOdd
  have hrSum := first_order_sum_eq_zero_of_prod_eq_one φ (2 : O) h2 hφ2 s
    (fun j => d j * (c j)⁻¹) (fun j => binaryLr (c j) (b j)) ε hr hrOne
  have hwSum := first_order_sum_eq_zero_of_prod_eq_one φ (1 + i)
    (binary_one_add_i_ne_zero i hi h2) hφpi s
    (fun j => g j * (c j)⁻¹) (fun j => binaryLw (c j) i (b j) (J j) (U j)) ε hw hwOne
  apply hnonzero
  calc
    (∑ j ∈ s, (ε j : k) * φ (J j * (↑((c j)⁻¹) : O))) =
        ∑ j ∈ s, ((ε j : k) * φ (binaryLr (c j) (b j)) +
          (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_add, binary_residue_sum φ (c j) i (b j) (J j) (U j) hφi]
    _ = (∑ j ∈ s, (ε j : k) * φ (binaryLr (c j) (b j))) +
        ∑ j ∈ s, (ε j : k) * φ (binaryLw (c j) i (b j) (J j) (U j)) :=
      Finset.sum_add_distrib
    _ = 0 := by rw [hrSum, hwSum, add_zero]

end Residue

end CirculantHadamard

end OAI
