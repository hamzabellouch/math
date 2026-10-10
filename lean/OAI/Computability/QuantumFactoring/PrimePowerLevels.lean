import Mathlib
import OAI.Computability.QuantumFactoring.LevelBounds

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- A closed integer expression; no enumeration of residue classes. -/
def primePowerUnitCount (p e : ℕ) : ℕ := (p-1) * p^(e-1)

def closedLevelCount (R t : ℕ) : ℕ :=
  if t = 0 then R / 2^padicValNat 2 R
  else if t ≤ padicValNat 2 R then 2^(t-1) * (R / 2^padicValNat 2 R) else 0

noncomputable def primePowerLevelCard (p e t : ℕ) : ℕ :=
  Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t}

/-- Exact prime-power level counts from the already fully proved cyclicity of
odd prime-power unit groups in Mathlib. -/
theorem primePowerLevelCard_eq {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    primePowerLevelCard p e t = closedLevelCount (primePowerUnitCount p e) t := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  classical
  change Nat.card {x : (ZMod (p^e))ˣ // padicValNat 2 (orderOf x) = t} = _
  rw [Nat.card_eq_fintype_card]
  change levelCount (ZMod (p^e))ˣ t = _
  rw [levelCount_closed, hc]
  rfl

theorem primePowerLevelCard_half {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 0 < e) (t : ℕ) :
    2 * primePowerLevelCard p e t ≤ primePowerUnitCount p e := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsCyclic (ZMod (p^e))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  have hc : Fintype.card (ZMod (p^e))ˣ = primePowerUnitCount p e := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp he]
    simp [primePowerUnitCount, mul_comm]
  have hpe : 2 < p^e := by
    have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    exact hp3.trans_le (Nat.le_pow he)
  have heven : 2 ∣ Fintype.card (ZMod (p^e))ˣ := by
    rw [ZMod.card_units_eq_totient]
    exact even_iff_two_dvd.mp (Nat.totient_even hpe)
  classical
  have hh := two_mul_levelCount_le (ZMod (p^e))ˣ heven t
  rw [hc] at hh
  simpa only [primePowerLevelCard, Nat.card_eq_fintype_card, levelCount] using hh

end ExactQuantumFactoring


end

end OAI
