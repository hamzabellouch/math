import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalShortEnergySharp
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPublishedRate

namespace OAI

/-! Taking the square root of the literal typical short energy. The
first-band resolution losses are paid before character summation. -/
namespace TwoPointCorrelations

lemma major_arc_three_term_root {B s t r : ℝ}
    (hB : 0 ≤ B) (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : 0 ≤ r) :
    Real.sqrt (B*(s^2+t^2+r^2)) ≤ (B+1)*(s+t+r) := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hcoef : B ≤ (B+1)^2 := by nlinarith [sq_nonneg B]
  have hsum : s^2+t^2+r^2 ≤ (s+t+r)^2 := by
    nlinarith [mul_nonneg hs ht,mul_nonneg hs hr,mul_nonneg ht hr]
  calc
    _ ≤ (B+1)^2*(s^2+t^2+r^2) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (B+1)^2*(s+t+r)^2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

noncomputable def majorArcEnergyConstant (C : ℝ) : ℝ :=
  (139968/(2*Real.pi))*(12*(C+33792*Real.exp 1+2+2048*Real.exp 2)+2048*Real.exp 1)+1

lemma major_arc_energy_constant_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < majorArcEnergyConstant C := by
  unfold majorArcEnergyConstant
  positivity

lemma major_arc_short_energy_root {C W R P H Q M δ : ℝ}
    (hC : 0 ≤ C) (hW : 1 ≤ W) (hR : W^9 ≤ R) (hP : W^2 ≤ P)
    (hH : W ≤ H) (hQ : Q/H ≤ W^7) (hδ : 0 ≤ δ) :
    Real.sqrt ((139968/(2*Real.pi))*(12*(C*(Real.exp (-4*M/5)+δ)+
      33792*Real.exp 1*R⁻¹+2*P⁻¹+1024*Real.exp 2*R⁻¹*(1+Q/H))+
      2048*Real.exp 1/H^2)) ≤
      majorArcEnergyConstant C*(Real.exp (-2*M/5)+Real.sqrt δ+W⁻¹) := by
  have hW0 : 0 < W := by linarith
  have hR0 : 0 < R := (pow_pos hW0 9).trans_le hR
  have hP0 : 0 < P := (pow_pos hW0 2).trans_le hP
  have hH0 : 0 < H := hW0.trans_le hH
  have hW5 : 1 ≤ W^7 := one_le_pow₀ hW
  have hRR : R⁻¹ ≤ (W^2)⁻¹ := by
    apply inv_anti₀ (pow_pos hW0 2)
    exact (pow_le_pow_right₀ hW (by omega : 2 ≤ 9)).trans hR
  have hPP : P⁻¹ ≤ (W^2)⁻¹ := inv_anti₀ (pow_pos hW0 2) hP
  have hHH : 1/H^2 ≤ (W^2)⁻¹ := by
    simpa only [one_div] using inv_anti₀ (pow_pos hW0 2) (pow_le_pow_left₀ hW0.le hH 2)
  have hRQ : R⁻¹*(1+Q/H) ≤ 2*(W^2)⁻¹ := by
    have hi : R⁻¹ ≤ (W^9)⁻¹ := inv_anti₀ (pow_pos hW0 9) hR
    calc
      _ ≤ R⁻¹*(2*W^7) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hR0.le)
      _ ≤ (W^9)⁻¹*(2*W^7) := mul_le_mul_of_nonneg_right hi (by positivity)
      _ = _ := by field_simp
  let B := (139968/(2*Real.pi))*(12*(C+33792*Real.exp 1+2+2048*Real.exp 2)+2048*Real.exp 1)
  let S := Real.exp (-4*M/5)+δ+(W^2)⁻¹
  have hterm : Real.exp (-4*M/5)+δ ≤ S := by
    dsimp only [S]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg W))
  have hinv : (W^2)⁻¹ ≤ S := by
    dsimp only [S]
    exact le_add_of_nonneg_left (add_nonneg (Real.exp_pos _).le hδ)
  have hbounds :
      C*(Real.exp (-4*M/5)+δ)+33792*Real.exp 1*R⁻¹+2*P⁻¹+
        1024*Real.exp 2*R⁻¹*(1+Q/H) ≤
      (C+33792*Real.exp 1+2+2048*Real.exp 2)*S := by
    have ha := mul_le_mul_of_nonneg_left hterm hC
    have hb := mul_le_mul_of_nonneg_left (hRR.trans hinv) (show 0 ≤ 33792*Real.exp 1 by positivity)
    have hc := mul_le_mul_of_nonneg_left (hPP.trans hinv) (show (0:ℝ) ≤ 2 by norm_num)
    have hd := mul_le_mul_of_nonneg_left (hRQ.trans (mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ)≤2)))
      (show 0 ≤ 1024*Real.exp 2 by positivity)
    nlinarith only [ha,hb,hc,hd]
  have he : (139968/(2*Real.pi))*(12*(C*(Real.exp (-4*M/5)+δ)+
      33792*Real.exp 1*R⁻¹+2*P⁻¹+1024*Real.exp 2*R⁻¹*(1+Q/H))+
      2048*Real.exp 1/H^2) ≤ B*S := by
    have ht := mul_le_mul_of_nonneg_left (hHH.trans hinv) (show 0 ≤ 2048*Real.exp 1 by positivity)
    have hi : 12*(C*(Real.exp (-4*M/5)+δ)+33792*Real.exp 1*R⁻¹+2*P⁻¹+
        1024*Real.exp 2*R⁻¹*(1+Q/H))+2048*Real.exp 1/H^2 ≤
      (12*(C+33792*Real.exp 1+2+2048*Real.exp 2)+2048*Real.exp 1)*S := by
      calc
        _ = 12*(C*(Real.exp (-4*M/5)+δ)+33792*Real.exp 1*R⁻¹+2*P⁻¹+
            1024*Real.exp 2*R⁻¹*(1+Q/H))+2048*Real.exp 1*(1/H^2) := by ring
        _ ≤ 12*((C+33792*Real.exp 1+2+2048*Real.exp 2)*S)+2048*Real.exp 1*S :=
          add_le_add (mul_le_mul_of_nonneg_left hbounds (by norm_num)) ht
        _ = _ := by ring
    simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left hi (show 0 ≤ 139968/(2*Real.pi) by positivity)
  have hs : S=(Real.exp (-2*M/5))^2+(Real.sqrt δ)^2+(W⁻¹)^2 := by
    dsimp [S]
    rw [Real.sq_sqrt hδ,inv_pow]
    have hx : (Real.exp (-2*M/5))^2=Real.exp (-4*M/5) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hx]
  calc
    _ ≤ Real.sqrt (B*S) := Real.sqrt_le_sqrt he
    _ ≤ (B+1)*(Real.exp (-2*M/5)+Real.sqrt δ+W⁻¹) := by
      rw [hs]
      exact major_arc_three_term_root (by dsimp [B]; positivity)
        (Real.exp_pos _).le (Real.sqrt_nonneg _) (inv_nonneg.mpr hW0.le)
    _ = _ := rfl

end TwoPointCorrelations

end OAI
