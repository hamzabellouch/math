import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Basic.Complex.Basic

namespace OAI

/-!
# Algebraic resolvent transfer for a nonbacktracking operator

This is the kernel argument in manuscript Lemma `q:noncommuting`. Each
edge operator has its own resolvent; distinct edge operators are never
commuted. The positivity and norm steps are separate from this algebraic
transfer.
-/

open scoped BigOperators

namespace TwoPointCorrelations

section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup E] [Module ℂ E]

/-- The copy indexed by `i` receives all transitions except the one with
the same index. -/
def nonbacktracking (B : ι → E →ₗ[ℂ] E) : (ι → E) →ₗ[ℂ] (ι → E) where
  toFun z i := ∑ j ∈ Finset.univ.erase i, B j (z j)
  map_add' x y := by
    funext i
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    simp [Finset.smul_sum, smul_sub]

/-- `R i` is the inverse of `1 + u B i`. These are the only inverse
identities needed to transfer injectivity. -/
theorem resolvent_transfer_injective (B : ι → E →ₗ[ℂ] E) (u : ℂ)
    (R : ι → E →ₗ[ℂ] E)
    (hR : ∀ i v, R i v + u • B i (R i v) = v)
    (hinj : Function.Injective (fun z : ι → E => z - u • nonbacktracking B z)) :
    Function.Injective (fun v : E => v - ∑ i, u • B i (R i v)) := by
  intro v w hvw
  let z : ι → E := fun i => R i (v - w)
  have hsum : ∑ i, u • B i (z i) = v - w := by
    have hs : (∑ i, u • B i (R i v)) - (∑ i, u • B i (R i w)) = v - w := by
      exact (sub_eq_sub_iff_sub_eq_sub.mp hvw).symm
    simpa only [z, map_sub, smul_sub, Finset.sum_sub_distrib] using hs
  have hkernel : z - u • nonbacktracking B z = 0 := by
    funext i
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun j => u • B j (z j)) (Finset.mem_univ i)
    have hri := hR i (v - w)
    change z i - u • (∑ j ∈ Finset.univ.erase i, B j (z j)) = 0
    rw [Finset.smul_sum]
    change z i - (∑ j ∈ Finset.univ.erase i, u • B j (z j)) = 0
    change z i + u • B i (z i) = v - w at hri
    rw [hsum] at hsplit
    exact sub_eq_zero.mpr (add_right_cancel (hri.trans hsplit.symm))
  have hz : z = 0 := hinj (by simpa using hkernel)
  by_cases hι : Nonempty ι
  · obtain ⟨i⟩ := hι
    have hzi : R i (v - w) = 0 := by
      simpa [z] using congrFun hz i
    have hvwzero := hR i (v - w)
    rw [hzi, map_zero, smul_zero, add_zero] at hvwzero
    exact sub_eq_zero.mp hvwzero.symm
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    simpa using hvw

end

end TwoPointCorrelations

end OAI
