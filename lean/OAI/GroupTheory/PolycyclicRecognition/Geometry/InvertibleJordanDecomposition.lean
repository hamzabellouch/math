import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.RingTheory.Nilpotent.Basic

namespace OAI

/-! # The multiplicative decomposition needed for a real matrix logarithm

The additive Jordan decomposition of an invertible operator gives a commuting
semisimple unit and a unipotent factor. Both factors are constructed here.
-/

noncomputable section
namespace PolycyclicRecognition
variable {K V : Type*} [Field K] [PerfectField K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem invertible_jordan_decomposition_centralizer (A : Module.End K V) (hA : IsUnit A) :
    ∃ (S : (Module.End K V)ˣ) (U : Module.End K V),
      Module.End.IsSemisimple (S : Module.End K V) ∧ IsNilpotent (U - 1) ∧
      Commute (S : Module.End K V) U ∧ A = (S : Module.End K V) * U ∧ IsUnit U ∧
      ∀ T : Module.End K V, Commute A T → Commute (S : Module.End K V) T ∧ Commute U T := by
  obtain ⟨n, hn, s, hs, hnil, hsem, hsum⟩ := A.exists_isNilpotent_isSemisimple
  have hnA : Commute n A := (Algebra.commute_of_mem_adjoin_self hn).symm
  have hns : Commute n s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs hnA
  have hsu : IsUnit s := by
    have hu := hnil.neg.isUnit_add_left_of_commute hA hnA.neg_left
    have he : A + -n = s := by rw [hsum]; abel
    rwa [he] at hu
  obtain ⟨S, hS⟩ := hsu
  have hnS : Commute n (S : Module.End K V) := hS.symm ▸ hns
  let q : Module.End K V := (S⁻¹ : (Module.End K V)ˣ) * n
  have hq : IsNilpotent q := by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    change ((S⁻¹ : (Module.End K V)ˣ) * n) ^ k = 0
    rw [(hnS.units_inv_right).symm.mul_pow, hk, mul_zero]
  have hSq : Commute (S : Module.End K V) q := by
    change (S : Module.End K V) * ((S⁻¹ : (Module.End K V)ˣ) * n) =
      ((S⁻¹ : (Module.End K V)ˣ) * n) * (S : Module.End K V)
    calc
      _ = n := by simp [← mul_assoc]
      _ = (S⁻¹ : (Module.End K V)ˣ) * ((S : Module.End K V) * n) := by
        simp [← mul_assoc]
      _ = _ := by rw [← hnS.eq, mul_assoc]
  refine ⟨S, 1 + q, hS.symm ▸ hsem, ?_, (Commute.one_right _).add_right hSq, ?_,
    hq.isUnit_one_add, ?_⟩
  · simpa only [add_sub_cancel_left] using hq
  · have he : (S : Module.End K V) * q = n := by simp [q, ← mul_assoc]
    rw [mul_add, mul_one, he, hS, add_comm]
    exact hsum
  · intro T hT
    have hsT : Commute (S : Module.End K V) T := by
      rw [hS]
      exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hs hT.symm).symm
    have hnT : Commute n T :=
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hn hT.symm).symm
    exact ⟨hsT, (Commute.one_left T).add_left (hsT.units_inv_left.mul_left hnT)⟩

theorem invertible_jordan_decomposition (A : Module.End K V) (hA : IsUnit A) :
    ∃ (S : (Module.End K V)ˣ) (U : Module.End K V),
      Module.End.IsSemisimple (S : Module.End K V) ∧ IsNilpotent (U - 1) ∧
      Commute (S : Module.End K V) U ∧ A = (S : Module.End K V) * U ∧ IsUnit U := by
  obtain ⟨S, U, hS, hU, hc, he, hu, _⟩ := invertible_jordan_decomposition_centralizer A hA
  exact ⟨S, U, hS, hU, hc, he, hu⟩

end PolycyclicRecognition

end

end OAI
