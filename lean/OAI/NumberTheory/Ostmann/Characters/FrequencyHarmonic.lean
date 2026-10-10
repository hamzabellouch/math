import Mathlib.NumberTheory.Harmonic.Bounds
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyMultiplicity

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Arithmetic.FrequencyMultiplicity

theorem reducedModulus_mem_Icc (v w s : ℤ) (hs:s≠0) (V:ℕ) (hV:s.natAbs≤V) :
    reducedModulus v w s ∈ Finset.Icc 1 V := by
  have hn : 0<s.natAbs := Int.natAbs_pos.mpr hs
  have hg : 0<(v.natAbs.gcd w.natAbs).gcd s.natAbs := Nat.gcd_pos_of_pos_right _ hn
  exact Finset.mem_Icc.mpr ⟨(Nat.one_le_div_iff hg).mpr
    (Nat.gcd_le_right _ hn), (Nat.div_le_self _ _).trans hV⟩

theorem reciprocal_reduced_sum_le_log (v w : ℤ) (hv:v≠0) (S:Finset ℤ) (V:ℕ)
    (hS:∀s∈S,s≠0 ∧ s.natAbs≤V) :
    ∑s∈S,(reducedModulus v w s:ℝ)⁻¹ ≤
      2*((v.natAbs.gcd w.natAbs).divisors.card:ℝ)*(1+Real.log V) := by
  have hmap : ∀s∈S,reducedModulus v w s∈Finset.Icc 1 V :=
    fun s hs => reducedModulus_mem_Icc v w s (hS s hs).1 V (hS s hs).2
  calc
    _ = ∑a∈Finset.Icc 1 V, ∑s∈S with reducedModulus v w s=a,(a:ℝ)⁻¹ :=
      (Finset.sum_fiberwise_of_maps_to' hmap (fun a:ℕ => (a:ℝ)⁻¹)).symm
    _ ≤ ∑a∈Finset.Icc 1 V, (2*((v.natAbs.gcd w.natAbs).divisors.card:ℝ))*(a:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast reduced_fiber_card v w hv S a
    _ = (2*((v.natAbs.gcd w.natAbs).divisors.card:ℝ))*
        (∑a∈Finset.Icc 1 V,(a:ℝ)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log V

theorem gcd_div_eq_inv_reduced (v w s:ℤ) (hs:s≠0) :
    (((v.natAbs.gcd w.natAbs).gcd s.natAbs:ℕ):ℝ)/(s.natAbs:ℝ)=
      (reducedModulus v w s:ℝ)⁻¹ := by
  let d := (v.natAbs.gcd w.natAbs).gcd s.natAbs
  have hd : (d:ℝ)≠0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right (v.natAbs.gcd w.natAbs)
      (Int.natAbs_pos.mpr hs)).ne'
  have he : (reducedModulus v w s:ℝ)*(d:ℝ)=(s.natAbs:ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right (v.natAbs.gcd w.natAbs) s.natAbs)
  change (d:ℝ)/(s.natAbs:ℝ)=_
  rw [← he]
  simp [div_eq_mul_inv, mul_inv_rev, hd]

theorem gcd_frequency_sum_le_log (v w:ℤ) (hv:v≠0) (S:Finset ℤ) (V:ℕ)
    (hS:∀s∈S,s≠0 ∧ s.natAbs≤V) :
    ∑s∈S, (((v.natAbs.gcd w.natAbs).gcd s.natAbs:ℕ):ℝ)/(s.natAbs:ℝ) ≤
      2*((v.natAbs.gcd w.natAbs).divisors.card:ℝ)*(1+Real.log V) := by
  calc
    _ = ∑s∈S,(reducedModulus v w s:ℝ)⁻¹ :=
      Finset.sum_congr rfl (fun s hs => gcd_div_eq_inv_reduced v w s (hS s hs).1)
    _ ≤ _ := reciprocal_reduced_sum_le_log v w hv S V hS

end Ostmann.Characters

end

end OAI
