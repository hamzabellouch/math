import OAI.NumberTheory.Ostmann.Arithmetic.PrimeProgression

namespace OAI

namespace Ostmann.Arithmetic.PrimeProgression

theorem logPrimeSupport_cutoff_eq (N : ℕ) (lo hi : ℝ) (hN : ⌊Real.exp hi⌋₊ ≤ N) :
    logPrimeSupport N lo hi = logPrimeSupport ⌊Real.exp hi⌋₊ lo hi := by
  ext p
  simp only [mem_logPrimeSupport]
  constructor
  · rintro ⟨hpN, hp, hlo, hhi⟩
    refine ⟨?_, hp, hlo, hhi⟩
    apply (Nat.le_floor_iff (Real.exp_pos hi).le).mpr
    exact (Real.log_le_iff_le_exp (by exact_mod_cast hp.pos)).mp hhi
  · rintro ⟨hpN, hp, hlo, hhi⟩
    exact ⟨hpN.trans hN, hp, hlo, hhi⟩

theorem harmonicProgression_cutoff_eq (N M : ℕ) (a : ZMod M) (lo hi : ℝ)
    (hN : ⌊Real.exp hi⌋₊ ≤ N) :
    harmonicProgression N M a lo hi = harmonicProgression ⌊Real.exp hi⌋₊ M a lo hi := by
  unfold harmonicProgression
  rw [logPrimeSupport_cutoff_eq N lo hi hN]

end Ostmann.Arithmetic.PrimeProgression

end OAI
