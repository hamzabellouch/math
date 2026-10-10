import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveTransfer

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz

lemma modulusHeight_mono {m q : ℕ} [NeZero m] [NeZero q] (hmq : m ≤ q) (t : ℝ) :
    modulusHeight m t ≤ modulusHeight q t := by
  have h : Real.log (m:ℝ) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (by exact_mod_cast NeZero.pos m) (by exact_mod_cast hmq)
  unfold modulusHeight
  linarith

theorem exists_nonprincipal_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ s : ℂ, 1-c/(modulusHeight q s.im)^2 ≤ s.re →
        DirichletCharacter.LFunction chi s ≠ 0 := by
  obtain ⟨cp,hcp,hprimitive⟩ := exists_primitive_zero_free_region
  let c : ℝ := min cp (1/4)
  have hc : 0 < c := lt_min hcp (by norm_num)
  have hcc : c ≤ cp := min_le_left _ _
  have hc4 : c ≤ 1/4 := min_le_right _ _
  refine ⟨c,hc,?_⟩
  intro q _ chi hchi s hs
  let _ : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hH := modulusHeight_ge_one q s.im
  have hHsq : 1 ≤ (modulusHeight q s.im)^2 := by nlinarith
  have hfrac : c/(modulusHeight q s.im)^2 ≤ c := by
    apply (div_le_iff₀ (by positivity : 0 < (modulusHeight q s.im)^2)).mpr
    nlinarith
  have hrep : 0 < s.re := by linarith
  apply (LFunction_primitive_ne_zero_iff chi hchi hrep).mpr
  have hcond : chi.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hHm := modulusHeight_ge_one chi.conductor s.im
  have hmono := modulusHeight_mono hcond s.im
  have hpow : (modulusHeight chi.conductor s.im)^2 ≤ (modulusHeight q s.im)^2 := by nlinarith
  have hfrac' : c/(modulusHeight q s.im)^2 ≤ cp/(modulusHeight chi.conductor s.im)^2 := by
    calc
      _ ≤ cp/(modulusHeight q s.im)^2 := div_le_div_of_nonneg_right hcc (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hcp.le (by positivity) hpow
  apply hprimitive chi.conductor (conductor_ge_three chi hchi) chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive (primitiveCharacter_ne_one chi hchi) s
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
