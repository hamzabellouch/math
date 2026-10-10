import OAI.Geometry.RCD.Transport.ReducedDistortionNonpositive

namespace OAI

/-! # Exact subdivision of the reduced entropy chord -/

open Set
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

def reducedChord (K N D : ℝ) (A B : ℝ≥0∞) (t : Time) : ℝ≥0∞ :=
  sigma K N (1-(t:ℝ)) D*A+sigma K N (t:ℝ) D*B

theorem reducedChord_zero {K N D : ℝ} (hK : K ≤ 0) (hN : 1<N) (hD : 0≤D)
    (A B : ℝ≥0∞) : reducedChord K N D A B 0=A := by
  simp [reducedChord,sigma_nonpos_zero hK hN hD,sigma_nonpos_one hK hN hD]

theorem reducedChord_one {K N D : ℝ} (hK : K ≤ 0) (hN : 1<N) (hD : 0≤D)
    (A B : ℝ≥0∞) : reducedChord K N D A B 1=B := by
  simp [reducedChord,sigma_nonpos_zero hK hN hD,sigma_nonpos_one hK hN hD]

theorem reducedChord_lower {K N D : ℝ} (hK : K ≤ 0) (hN : 1<N) (hD : 0≤D)
    (A B : ℝ≥0∞) (t : Time) :
    reducedChord K N D A B (lowerTime t)=
      reducedChord K N (D/2) A (sigma K N (1/2) D*(A+B)) t := by
  have hf := sigma_nonpos_interpolation hK hN hD (a:=0) (b:=1/2) (t:= (t:ℝ))
    (by norm_num) (by norm_num) t.property.1 t.property.2
  have hb := sigma_nonpos_interpolation hK hN hD (a:=1/2) (b:=1) (t:=1-(t:ℝ))
    (by norm_num) (by norm_num) (by linarith [t.property.2]) (by linarith [t.property.1])
  have heF : (1-(t:ℝ))*0+(t:ℝ)*(1/2)=(t:ℝ)/2 := by ring
  have heB : (1-(1-(t:ℝ)))*(1/2)+(1-(t:ℝ))*1=1-(t:ℝ)/2 := by ring
  rw [heF] at hf
  rw [heB] at hb
  norm_num only [sub_zero,show (1:ℝ)-1/2=1/2 by norm_num,
    show (1/2:ℝ)*D=D/2 by ring,show (1:ℝ)-(1-(t:ℝ))=(t:ℝ) by ring,
    sigma_nonpos_zero hK hN hD,sigma_nonpos_one hK hN hD,mul_zero,add_zero,mul_one] at hf hb
  simp only [reducedChord,coe_lowerTime,hf,hb]
  ring

theorem reducedChord_upper {K N D : ℝ} (hK : K ≤ 0) (hN : 1<N) (hD : 0≤D)
    (A B : ℝ≥0∞) (t : Time) :
    reducedChord K N D A B (upperTime t)=
      reducedChord K N (D/2) (sigma K N (1/2) D*(A+B)) B t := by
  have hf := sigma_nonpos_interpolation hK hN hD (a:=1/2) (b:=1) (t:=(t:ℝ))
    (by norm_num) (by norm_num) t.property.1 t.property.2
  have hb := sigma_nonpos_interpolation hK hN hD (a:=0) (b:=1/2) (t:=1-(t:ℝ))
    (by norm_num) (by norm_num) (by linarith [t.property.2]) (by linarith [t.property.1])
  have heF : (1-(t:ℝ))*(1/2)+(t:ℝ)*1=((t:ℝ)+1)/2 := by ring
  have heB : (1-(1-(t:ℝ)))*0+(1-(t:ℝ))*(1/2)=1-((t:ℝ)+1)/2 := by ring
  rw [heF] at hf
  rw [heB] at hb
  norm_num only [sub_zero,show (1:ℝ)-1/2=1/2 by norm_num,
    show (1/2:ℝ)*D=D/2 by ring,show (1:ℝ)-(1-(t:ℝ))=(t:ℝ) by ring,
    sigma_nonpos_zero hK hN hD,sigma_nonpos_one hK hN hD,mul_zero,zero_add,mul_one] at hf hb
  simp only [reducedChord,coe_upperTime,hf,hb]
  ring

theorem reducedChord_mono {K N D : ℝ} {A B A' B' : ℝ≥0∞}
    (hA : A≤A') (hB : B≤B') (t : Time) :
    reducedChord K N D A B t≤reducedChord K N D A' B' t :=
  add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB)

end RegularPointCoordinates

end

end OAI
