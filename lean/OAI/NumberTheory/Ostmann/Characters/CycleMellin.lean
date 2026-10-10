import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Characters.CycleAction
import OAI.NumberTheory.Ostmann.Characters.MellinParseval

namespace OAI

/-!
# The Mellin constraint retained by cycle averaging

Reciprocal multiplication retains exactly the character tuples whose
signed product is principal. This is the relation used in the final
cycle-coefficient estimate.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance cycleMellinFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance cycleMellinDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

private theorem mulChar_product_apply {p : ℕ} [Fact p.Prime]
    {I : Type*} (s : Finset I) (χ : I → MulChar (ZMod p) ℂ) (z : (ZMod p)ˣ) :
    (∏ i ∈ s, χ i) z = ∏ i ∈ s, χ i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, MulChar.one_apply_coe]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, MulChar.coeToFun_mul, Pi.mul_apply, ih]

theorem cycleAverage_product_mellin {p : ℕ} [Fact p.Prime]
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → (ZMod p)ˣ → ℂ) (sign : I → ℤ) (m : I → (ZMod p)ˣ) :
    cycleAverage sign (fun m => ∏ i : I, f i (m i)) m =
      ∑ ρ : I → MulChar (ZMod p) ℂ,
        if (∏ i : I, (ρ i) ^ sign i) = 1 then
          ∏ i : I, mellinCoefficient (f i) (ρ i) * ρ i (m i) else 0 := by
  classical
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (z : (ZMod p)ˣ) :
      (∏ i : I, f i (cycleMultiply sign z m i)) =
        ∑ ρ : I → MulChar (ZMod p) ℂ,
          (∏ i : I, mellinCoefficient (f i) (ρ i) * ρ i (m i)) *
            (∏ i : I, (ρ i) ^ sign i) z := by
    have hf (i : I) : f i (cycleMultiply sign z m i) =
        ∑ χ : MulChar (ZMod p) ℂ,
          mellinCoefficient (f i) χ * χ ((cycleMultiply sign z m i : (ZMod p)ˣ) : ZMod p) :=
      (mellin_inversion (f i) _).symm
    simp_rw [hf]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [mulChar_product_apply]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [cycleMultiply, Units.val_mul, map_mul, MulChar.zpow_apply_coe]
    ring
  unfold cycleAverage
  simp_rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [← Finset.mul_sum, sum_mulChar_units_eq_ite]
  split_ifs
  · field_simp
  · simp

end Ostmann

end OAI
