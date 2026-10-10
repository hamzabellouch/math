import OAI.Geometry.HeilbronnTriangle.DiagonalStabilizer
import OAI.Geometry.HeilbronnTriangle.ZModAnnihilator

namespace OAI


noncomputable section

namespace Problem355

open DiagonalStabilizer

theorem card_ann_zmod_pow (B k e : ℕ) [NeZero B] (he : e ≤ k) :
    Nat.card (Ann (R := ZMod (B ^ k)) (B ^ e)) = B ^ e := by
  simpa only [Ann, mul_comm] using zmod_card_pow_mul_eq_zero B k e he

theorem card_stabilizer_prime_power_le
    (B k b e : ℕ) [NeZero B] (hb : b ≤ k) (he : e ≤ k)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) * (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))) :
    Nat.card (MulAction.stabilizer (Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k))) C) ≤
      (B ^ b) ^ 3 * (B ^ e) ^ 3 := by
  simpa only [card_ann_zmod_pow B k b hb, card_ann_zmod_pow B k e he] using
    card_stabilizer_of_diagonal_form_le C (B ^ b : ZMod (B ^ k)) (B ^ e : ZMod (B ^ k)) P Q hC

end Problem355

end

end OAI
