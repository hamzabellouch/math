import OAI.NumberTheory.Ostmann.Characters.SymbolicHistory

namespace OAI

noncomputable section
namespace Ostmann.Characters.SymbolicHistory.Expr
variable {ι : Type*}

def DivisorsBelow (p : ℕ) : Expr ι → Prop
  | .atom _ => True
  | .fixed _ => True
  | .add a b => a.DivisorsBelow p ∧ b.DivisorsBelow p
  | .sub a b => a.DivisorsBelow p ∧ b.DivisorsBelow p
  | .mul a b => a.DivisorsBelow p ∧ b.DivisorsBelow p
  | .divide a d => a.DivisorsBelow p ∧ |d| < (p : ℤ)

theorem prime_isCoprime_frequency {p : ℕ} (hp : p.Prime) {d : ℤ}
    (hd : d ≠ 0) (hlt : |d| < (p : ℤ)) : IsCoprime (p : ℤ) d := by
  have habs : d.natAbs < p := by
    have hh : (d.natAbs : ℤ) < (p : ℤ) := by
      simpa only [Int.natCast_natAbs] using hlt
    exact_mod_cast hh
  have hc : Nat.Coprime p d.natAbs :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hd) habs)
  exact hc.isCoprime.of_isCoprime_of_dvd_right Int.dvd_natAbs_self

theorem denominator_isCoprime_of_divisorsBelow (e : Expr ι) {p : ℕ}
    (hp : p.Prime) (he : e.Valid) (hb : e.DivisorsBelow p) :
    IsCoprime (p : ℤ) e.denominator := by
  induction e with
  | atom i => exact isCoprime_one_right
  | fixed c => exact isCoprime_one_right
  | add a b ia ib => exact (ia he.1 hb.1).mul_right (ib he.2 hb.2)
  | sub a b ia ib => exact (ia he.1 hb.1).mul_right (ib he.2 hb.2)
  | mul a b ia ib => exact (ia he.1 hb.1).mul_right (ib he.2 hb.2)
  | divide a d ia =>
    exact (ia he.1 hb.1).mul_right (prime_isCoprime_frequency hp he.2 hb.2)

end Ostmann.Characters.SymbolicHistory.Expr

end

end OAI
