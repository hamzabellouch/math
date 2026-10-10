import Mathlib

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosInversePrimeBin

noncomputable def primeBin (R xi : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊(1+xi)*R⌋₊ \ Nat.primesLE ⌊R⌋₊

theorem mem_primeBin {R xi : ℝ} (hR : 0 ≤ R) (hxi : 0 ≤ xi) (p : ℕ) :
    p ∈ primeBin R xi ↔ p.Prime ∧ R < (p : ℝ) ∧ (p : ℝ) ≤ (1+xi)*R := by
  have hb : 0 ≤ (1+xi)*R := by positivity
  constructor
  · intro hp
    obtain ⟨hpB,hpR⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hup,hprime⟩ := Nat.mem_primesLE.mp hpB
    refine ⟨hprime,?_,(Nat.le_floor_iff hb).mp hup⟩
    by_contra! hlow
    exact hpR (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hR).mpr hlow,hprime⟩)
  · rintro ⟨hprime,hlo,hhi⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hb).mpr hhi,hprime⟩,?_⟩
    intro hpR
    exact (not_le_of_gt hlo) ((Nat.le_floor_iff hR).mp (Nat.mem_primesLE.mp hpR).1)

theorem primeBin_log_sum {R xi : ℝ} (hR : 0 ≤ R) (hxi : 0 ≤ xi) :
    (∑ p ∈ primeBin R xi,Real.log p) = Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R := by
  have hsub : Nat.primesLE ⌊R⌋₊ ⊆ Nat.primesLE ⌊(1+xi)*R⌋₊ := by
    intro p hp
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_mono (by nlinarith)),hprime⟩
  rw [Chebyshev.theta_eq_sum_primesLE,Chebyshev.theta_eq_sum_primesLE]
  simpa only [primeBin] using (Finset.sum_sdiff_eq_sub (f := fun p : ℕ => Real.log p) hsub)

theorem primeBin_log_sum_upper {R xi : ℝ} (hR : 2 ≤ R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) :
    (∑ p ∈ primeBin R xi,Real.log p) ≤ (primeBin R xi).card*(2*Real.log R) := by
  have hR0 : 0 < R := by linarith
  have hupper : (1+xi)*R ≤ R^2 := by nlinarith
  have hb0 : 0 < (1+xi)*R := by positivity
  have hlog : Real.log ((1+xi)*R) ≤ 2*Real.log R := by
    have h := Real.log_le_log hb0 hupper
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  calc
    _ ≤ ∑ _p ∈ primeBin R xi,2*Real.log R := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hprime,_,hhi⟩ := (mem_primeBin hR0.le hxi p).mp hp
      exact (Real.log_le_log (by exact_mod_cast hprime.pos) hhi).trans hlog
    _ = _ := by simp

end ErdosInversePrimeBin

end

end Erdos970

end OAI
