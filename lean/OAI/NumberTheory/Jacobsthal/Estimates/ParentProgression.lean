import OAI.NumberTheory.Jacobsthal.Primes.PrimeHitRepresentative

namespace OAI

namespace Erdos970

section

namespace ErdosInverseHits

noncomputable def parentSlope (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ) : ℕ :=
  (((a : ZMod p)-(b : ZMod p))*(↑((ZMod.unitOfCoprime q hqp)⁻¹) : ZMod p)).val

theorem parentSlope_lt (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ) :
    parentSlope p q hqp a b < p := ZMod.val_lt _

theorem parent_start_mod_p (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ) :
    Nat.ModEq p (b+q*parentSlope p q hqp a b) a := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simp only [Nat.cast_add,Nat.cast_mul,parentSlope,ZMod.natCast_zmod_val]
  have hu : (q : ZMod p)*(↑((ZMod.unitOfCoprime q hqp)⁻¹) : ZMod p) = 1 := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime q hqp).mul_inv
  calc
    (b : ZMod p)+(q : ZMod p)*(((a : ZMod p)-(b : ZMod p))*↑((ZMod.unitOfCoprime q hqp)⁻¹)) =
      (b : ZMod p)+((a : ZMod p)-(b : ZMod p))*((q : ZMod p)*↑((ZMod.unitOfCoprime q hqp)⁻¹)) := by ring
    _ = _ := by rw [hu];ring

theorem parent_start_mod_q (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ) :
    Nat.ModEq q (b+q*parentSlope p q hqp a b) b := by
  change (b+q*parentSlope p q hqp a b)%q = b%q
  simp

theorem parent_start_bounds (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b : ℕ)
    (hb1 : 1 ≤ b) (hbq : b ≤ q) :
    1 ≤ b+q*parentSlope p q hqp a b ∧ b+q*parentSlope p q hqp a b ≤ p*q := by
  have hs := parentSlope_lt p q hqp a b
  constructor
  · omega
  · nlinarith

theorem parent_hit_iff (p q : ℕ) [NeZero p] (hqp : q.Coprime p) (a b n : ℕ) :
    (Nat.ModEq p n a ∧ Nat.ModEq q n b) ↔
      Nat.ModEq (p*q) n (b+q*parentSlope p q hqp a b) := by
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hqp.symm]
  have hp := parent_start_mod_p p q hqp a b
  have hq := parent_start_mod_q p q hqp a b
  exact and_congr ⟨fun h => h.trans hp.symm,fun h => h.trans hp⟩
    ⟨fun h => h.trans hq.symm,fun h => h.trans hq⟩

end ErdosInverseHits

end

end Erdos970

end OAI
