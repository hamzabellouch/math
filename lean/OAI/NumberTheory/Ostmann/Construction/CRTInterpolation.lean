import Mathlib
import OAI.NumberTheory.Ostmann.Supply.CRTPrimitiveEnergy

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def otherProduct (p : ι → ℕ) (i : ι) : ℕ := ∏ j∈Finset.univ.erase i, p j

theorem mul_otherProduct (p : ι → ℕ) (i : ι) : p i*otherProduct p i=∏ j, p j :=
  Finset.mul_prod_erase Finset.univ p (Finset.mem_univ i)

theorem otherProduct_coprime (p : ι → ℕ)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (i : ι) :
    (otherProduct p i).Coprime (p i) := by
  apply Nat.Coprime.prod_left
  intro j hj
  exact hcop (Finset.mem_erase.mp hj).1

theorem otherProduct_cast_zero (p : ι → ℕ) {i j : ι} (hij : i≠j) :
    (otherProduct p i : ZMod (p j))=0 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  exact Finset.dvd_prod_of_mem p (Finset.mem_erase.mpr ⟨Ne.symm hij,Finset.mem_univ j⟩)

def interpolationCoordinate (p : ι → ℕ) (x : ∀ i, ZMod (p i)) (i : ι) : ZMod (p i) :=
  x i*(otherProduct p i : ZMod (p i))⁻¹

def crtReconstruct (p : ι → ℕ) (x : ∀ i, ZMod (p i)) : ZMod (∏ i, p i) :=
  ∑ i, (otherProduct p i : ZMod (∏ i, p i))*((interpolationCoordinate p x i).val : ZMod (∏ i, p i))

theorem crtReconstruct_coordinates (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (x : ∀ i, ZMod (p i)) :
    ZMod.prodEquivPi p hcop (crtReconstruct p x)=x := by
  funext j
  simp only [crtReconstruct,map_sum,map_mul,map_natCast,Finset.sum_apply,Pi.mul_apply,Pi.natCast_apply]
  rw [Finset.sum_eq_single j]
  · rw [ZMod.natCast_zmod_val]
    unfold interpolationCoordinate
    calc
      _ = x j*((otherProduct p j : ZMod (p j))*(otherProduct p j : ZMod (p j))⁻¹) := by ring
      _ = x j := by rw [ZMod.coe_mul_inv_eq_one _ (otherProduct_coprime p hcop j),mul_one]
  · intro i hi hij
    rw [otherProduct_cast_zero p hij,zero_mul]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem crtReconstruct_eq (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (z : ZMod (∏ i, p i)) :
    crtReconstruct p (ZMod.prodEquivPi p hcop z)=z := by
  apply (ZMod.prodEquivPi p hcop).injective
  exact crtReconstruct_coordinates p hcop _

end Ostmann.Construction

end

end OAI
