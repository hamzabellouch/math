import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.FieldSimp
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootResidueSeparation

namespace OAI

/-! # Constructing the actual rescaling at a split prime -/

namespace Ostmann

theorem exists_quadratic_split_root (u v : ℤ) {p : ℕ} (hp : p.Prime)
    (hpu : ¬p ∣ u.natAbs) (hsplit : jacobiSym (u * v) p = 1) :
    ∃ c : ZMod p, (u : ZMod p) * c ^ 2 = (v : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have hu : (u : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd u p).mp hz
    exact hpu (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hd))
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hsplit
  refine ⟨r / (u : ZMod p), ?_⟩
  have hr' : r ^ 2 = (u : ZMod p) * (v : ZMod p) := by
    simpa only [Int.cast_mul, pow_two] using hr.symm
  field_simp
  rw [hr']

end Ostmann

end OAI
