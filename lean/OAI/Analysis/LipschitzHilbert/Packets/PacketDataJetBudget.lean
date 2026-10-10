import OAI.Analysis.LipschitzHilbert.Packets.PacketDataJetControl

namespace OAI

/-! The smaller concentration normalization has a polynomial bound that
does not involve the later mask exponent. -/
noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

@[simp] theorem withJetControl_referenceEnvelopeConstant
    (P : PacketLatticeData N κ Label Item)
    (scale ratio : ℝ) (hratio : 1≤ratio) (hscale : |scale/P.width|≤ratio) :
    (P.withJetControl scale ratio hratio hscale).referenceEnvelopeConstant =
      ((2^P.order*P.profileBound)*ratio^2)*3^(2*P.order) := rfl

theorem smallJetRatio_ge_one {L a : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) :
    1 ≤ 4*L^a := by
  have h := Real.one_le_rpow hL ha
  linarith

theorem smallJetScale_control (P : PacketLatticeData N κ Label Item)
    {L a width : ℝ} (hL : 0 < L) (hw : 0 ≤ width) (hwidth : width ≤ P.width) :
    |(4*(L^a*width))/P.width| ≤ 4*L^a := by
  have hr : 0 ≤ L^a := Real.rpow_nonneg hL.le _
  rw [abs_of_nonneg (div_nonneg (by positivity) P.width_pos.le)]
  apply (div_le_iff₀ P.width_pos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hwidth (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hr)]

theorem smallJetControl_referenceEnvelopeConstant (P : PacketLatticeData N κ Label Item)
    {L a p width : ℝ} (hL : 16 ≤ L) (ha : 0 ≤ a)
    (hw : 0 ≤ width) (hwidth : width ≤ P.width)
    (hprofile : (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p) :
    (P.withJetControl (4*(L^a*width)) (4*L^a)
      (smallJetRatio_ge_one (by linarith) ha)
      (P.smallJetScale_control (by linarith) hw hwidth)).referenceEnvelopeConstant ≤
      L^(p+2*a+1) := by
  have hL0 : 0 < L := by linarith
  rw [withJetControl_referenceEnvelopeConstant]
  calc
    _ = ((2^P.order*P.profileBound)*3^(2*P.order))*(16*(L^a)^2) := by ring
    _ ≤ L^p*(16*(L^a)^2) := mul_le_mul_of_nonneg_right hprofile (by positivity)
    _ ≤ L^p*(L*(L^a)^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hL (sq_nonneg _)) (Real.rpow_nonneg hL0.le _)
    _ = L^(p+2*a+1) := by
      calc
        _ = L^p*(L^(1:ℝ)*(L^a)^(2:ℝ)) := by rw [Real.rpow_one,Real.rpow_two]
        _ = L^(p+(1+a*2)) := by
          rw [← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
        _ = _ := by congr 1; ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
