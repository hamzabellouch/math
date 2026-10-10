import OAI.NumberTheory.Ostmann.Construction.PrimeLogGrid

namespace OAI

/-! # The grid covers exactly the original prime interval -/

namespace Ostmann

open scoped Classical

theorem mem_gridPrimeSupport_iff (N q : ℕ) [NeZero q] (s h : ℝ) (hh : 0 ≤ h) (p : ℕ) :
    p ∈ primeCellSupport q (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h) ↔
      p.Prime ∧ p.Coprime q ∧ Real.log (p : ℝ) ∈ Set.Ioc s (s + N * h) := by
  constructor
  · intro hp
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hres, hlo, hhi⟩ := mem_primeLogCellSet_iff.mp hc
    have heq := (ZMod.natCast_eq_natCast_iff p (gridResidue c) q).mpr hres
    simp only [gridResidue, ZMod.natCast_zmod_val] at heq
    have hcop : p.Coprime q := (ZMod.isUnit_iff_coprime p q).mp (by
      rw [heq]
      exact c.2.isUnit)
    have hj : (c.1 : ℝ) + 1 ≤ N := by
      exact_mod_cast (show c.1.val + 1 ≤ N from c.1.isLt)
    have hj0 : (0 : ℝ) ≤ c.1 := by positivity
    dsimp [gridLower, gridUpper] at hlo hhi
    exact ⟨hprime, hcop, by nlinarith, by nlinarith⟩
  · rintro ⟨hprime, hcop, hlog⟩
    have hmem : Real.log (p : ℝ) ∈
        Set.Ioc ((fun j : ℕ => s + j * h) 0) ((fun j : ℕ => s + j * h) N) := by
      simpa using hlog
    have hu := Ioc_subset_biUnion_Ioc N (fun j : ℕ => s + j * h) hmem
    simp only [Set.mem_iUnion] at hu
    obtain ⟨j, hj, hbound⟩ := hu
    let c : Fin N × (ZMod q)ˣ := (⟨j, Finset.mem_range.mp hj⟩, ZMod.unitOfCoprime p hcop)
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ c, mem_primeLogCellSet_iff.mpr ⟨hprime, ?_, ?_⟩⟩
    · apply (ZMod.natCast_eq_natCast_iff p (gridResidue c) q).mp
      simp [c, gridResidue]
    · simpa only [c, gridLower, gridUpper, Nat.cast_add, Nat.cast_one] using hbound

/-- At these scales the modulus is below every sampled prime, so every
prime in the log interval appears in the unit-residue grid. -/
theorem mem_gridPrimeSupport_iff_prime (N q : ℕ) [NeZero q] (s h : ℝ)
    (hh : 0 ≤ h) (hq : (q : ℝ) ≤ Real.exp s) (p : ℕ) :
    p ∈ primeCellSupport q (gridResidue (N := N) (q := q)) (gridLower s h) (gridUpper s h) ↔
      p.Prime ∧ Real.log (p : ℝ) ∈ Set.Ioc s (s + N * h) := by
  rw [mem_gridPrimeSupport_iff N q s h hh p]
  constructor
  · exact fun hp => ⟨hp.1, hp.2.2⟩
  · rintro ⟨hp, hlog⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hqp : q < p := by
      exact_mod_cast hq.trans_lt ((Real.lt_log_iff_exp_lt hp0).mp hlog.1)
    have hcop := hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (NeZero.pos q) hqp)
    exact ⟨hp, hcop, hlog⟩

end Ostmann

end OAI
