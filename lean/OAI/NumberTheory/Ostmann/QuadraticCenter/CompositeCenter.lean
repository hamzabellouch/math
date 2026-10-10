import OAI.NumberTheory.Ostmann.QuadraticCenter.Amplifier
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedPoisson

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def compositeCenter {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (t : ι → ℤ) : ℕ :=
  ((ZMod.prodEquivPi p hcop).symm (fun i => (t i : ZMod (p i)))).val

theorem compositeCenter_lt {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (t : ι → ℤ) :
    compositeCenter p hcop t < ∏ i, p i := ZMod.val_lt _

theorem compositeCenter_cast {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (t : ι → ℤ) (i : ι) :
    ((compositeCenter p hcop t : ℕ) : ZMod (p i)) = (t i : ZMod (p i)) := by
  have hc : ZMod.prodEquivPi p hcop
      ((compositeCenter p hcop t : ℕ) : ZMod (∏ i, p i)) =
      (fun i => (t i : ZMod (p i))) := by
    unfold compositeCenter
    rw [ZMod.natCast_zmod_val]
    exact (ZMod.prodEquivPi p hcop).apply_symm_apply _
  have hi := congrFun hc i
  simpa only [map_natCast, Pi.natCast_apply] using hi

theorem compositeCenter_dvd {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (t : ι → ℤ) (i : ι) :
    (p i : ℤ) ∣ (compositeCenter p hcop t : ℤ) - t i := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub, Int.cast_natCast, compositeCenter_cast, sub_self]

theorem jacobi_finset_prod_right {ι : Type*} (I : Finset ι) (p : ι → ℕ)
    (hp : ∀ i ∈ I, p i ≠ 0) (n : ℤ) :
    jacobiSym n (∏ i ∈ I, p i) = ∏ i ∈ I, jacobiSym n (p i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hi0 := hp i (Finset.mem_insert_self _ _)
    have hI0 : ∀ j ∈ I, p j ≠ 0 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      jacobiSym.mul_right' n hi0 (Finset.prod_ne_zero_iff.mpr hI0), ih hI0]

theorem translated_jacobi_prod_eq_composite {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (t : ι → ℤ) (n : ℤ) :
    (∏ i, jacobiSym (n - t i) (p i)) =
      jacobiSym (n - compositeCenter p hcop t) (∏ i, p i) := by
  classical
  rw [jacobi_finset_prod_right Finset.univ p (fun i _ => NeZero.ne (p i))]
  apply Finset.prod_congr rfl
  intro i hi
  apply jacobiSym.mod_left'
  apply (ZMod.intCast_eq_intCast_iff' _ _ (p i)).mp
  simp only [Int.cast_sub, Int.cast_natCast, compositeCenter_cast]

end Ostmann.QuadraticCenter

end

end OAI
