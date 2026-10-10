import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBandSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

def primeLogMass (P : Finset ℕ) : ℝ := ∑p∈P,Real.log p/(p:ℝ)

lemma primeLogMass_mono {P R : Finset ℕ} (hPR : P⊆R) : primeLogMass P≤primeLogMass R := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hPR
  intro p hp _
  exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem primeLogMass_block_le (P : Finset ℕ) (G h : ℝ) (hG : 1≤G) (hh : 0≤h)
    (hP : ∀p∈P,p.Prime ∧ G≤Real.log p ∧ Real.log p≤G+h) :
    primeLogMass P≤h+1+2*(Real.log 4+4) := by
  let U := primePrefix (Real.exp (G+h))
  let D := primePrefix (Real.exp (G-1))
  have hD : D⊆U := primePrefix_mono (Real.exp_le_exp.mpr (by linarith))
  have hsub : P⊆U\D := by
    intro p hp
    obtain ⟨hprime,hlo,hhi⟩ := hP p hp
    have hp0 : (0:ℝ)<p := by exact_mod_cast hprime.pos
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ioc.mpr ⟨hprime.pos,?_⟩,hprime⟩
      apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
      have he := Real.exp_le_exp.mpr hhi
      rwa [Real.exp_log hp0] at he
    · intro hd
      have hd' := (Nat.le_floor_iff (Real.exp_pos _).le).mp
        (Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1).2
      have hl := Real.log_le_log hp0 hd'
      rw [Real.log_exp] at hl
      linarith
  have he := Finset.sum_sdiff (f := fun p : ℕ => Real.log p/(p:ℝ)) hD
  have hmono := primeLogMass_mono hsub
  have hge : 1≤Real.exp (G+h) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : (0:ℝ)≤G+h)
  have hde : 1≤Real.exp (G-1) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by linarith : (0:ℝ)≤G-1)
  have hupper := Erdos970.Mertens.sum_log_prime_div_eq_log hge
  have hlower := Erdos970.Mertens.sum_log_prime_div_eq_log hde
  simp only [Real.log_exp] at hupper hlower
  change |primeLogMass U-(G+h)|≤Real.log 4+4 at hupper
  change |primeLogMass D-(G-1)|≤Real.log 4+4 at hlower
  change primeLogMass (U\D)+primeLogMass D=primeLogMass U at he
  have hu := (abs_le.mp hupper).2
  have hl := (abs_le.mp hlower).1
  linarith

end Ostmann.Construction

end

end OAI
