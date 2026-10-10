import OAI.Geometry.RCD.Coordinates.HeatFrameGramBound

namespace OAI

/-! # Radius-independent constants in the mixed heat-frame energy estimate -/

noncomputable section
namespace RegularPointCoordinates

theorem scaled_heat_source_bound {r η κ a A d : ℝ}
    (hr : 0<r) (hη : 0<η) (hκ : 0≤κ) (ha : 0≤a) (hd : 0≤d)
    (hcurv : κ*r^2≤1) (hA : A≤a*r) :
    r*(2*d*(κ+1/(η*r^2))*A)≤2*d*(1+1/η)*a := by
  have hh : r*(2*d*(κ+1/(η*r^2))*A)≤r*(2*d*(κ+1/(η*r^2))*(a*r)) := by
    gcongr
  have he : r*(2*d*(κ+1/(η*r^2))*(a*r))=2*d*(κ*r^2+1/η)*a := by
    field_simp [hr.ne',hη.ne']
  rw [he] at hh
  exact hh.trans (by gcongr)

theorem scaled_heat_gram_energy_bound {r J C κ ℓ b L B e v m D : ℝ}
    (hr : 0<r) (hC : 0≤C) (hκ : 0≤κ) (hℓ : 0≤ℓ) (hb : 0≤b)
    (hL : ℓ ≤ L) (hB : r*b ≤ B) (he : 0 ≤ e) (hv : 0 ≤ v)
    (hcurv : κ*r^2 ≤ 1) (hem : e ≤ D*m) (hvm : v ≤ m)
    (hJ : J≤2*ℓ^2*((C/r^2)/2*e+κ*(e+v))+
      8*((C/r^2)/2*ℓ^2+κ*ℓ^2+b^2+b*ℓ*(C/r))*v) :
    r^2*J≤(2*L^2*((C/2+1)*D+1)+8*((C/2+1)*L^2+B^2+B*L*C))*m := by
  have hL0 : 0≤L := hℓ.trans hL
  have hB0 : 0≤B := (mul_nonneg hr.le hb).trans hB
  have hl2 : ℓ^2≤L^2 := pow_le_pow_left₀ hℓ hL 2
  have hb2 : (r*b)^2≤B^2 := pow_le_pow_left₀ (mul_nonneg hr.le hb) hB 2
  have hscale : r^2*J≤2*ℓ^2*((C/2)*e+(κ*r^2)*(e+v))+
      8*((C/2)*ℓ^2+(κ*r^2)*ℓ^2+(r*b)^2+(r*b)*ℓ*C)*v := by
    have hh := mul_le_mul_of_nonneg_left hJ (sq_nonneg r)
    convert hh using 1
    field_simp [hr.ne']
  have hfirst : (C/2)*e+(κ*r^2)*(e+v)≤((C/2+1)*D+1)*m := by
    calc
      _ ≤ (C/2)*(D*m)+1*(D*m+m) :=
        add_le_add (mul_le_mul_of_nonneg_left hem (by positivity))
          (mul_le_mul hcurv (add_le_add hem hvm) (add_nonneg he hv) zero_le_one)
      _ = _ := by ring
  have hsecond : (C/2)*ℓ^2+(κ*r^2)*ℓ^2+(r*b)^2+(r*b)*ℓ*C≤
      (C/2+1)*L^2+B^2+B*L*C := by
    have h₁ := mul_le_mul_of_nonneg_left hl2 (show 0≤C/2 by positivity)
    have h₂ := mul_le_mul hcurv hl2 (sq_nonneg ℓ) zero_le_one
    have h₃ := mul_le_mul_of_nonneg_right
      (mul_le_mul hB hL hℓ hB0) hC
    nlinarith only [h₁,h₂,hb2,h₃]
  have hsecond0 : 0≤(C/2+1)*L^2+B^2+B*L*C := by positivity
  apply hscale.trans
  have hleft := mul_le_mul (mul_le_mul_of_nonneg_left hl2 (by norm_num : (0:ℝ)≤2))
    hfirst (add_nonneg (mul_nonneg (by positivity) he) (mul_nonneg (mul_nonneg hκ (sq_nonneg r)) (add_nonneg he hv)))
    (by positivity : 0≤2*L^2)
  have hright := mul_le_mul (mul_le_mul_of_nonneg_left hsecond (by norm_num : (0:ℝ)≤8)) hvm hv
    (mul_nonneg (by norm_num : (0:ℝ)≤8) hsecond0)
  have hh := add_le_add hleft hright
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
