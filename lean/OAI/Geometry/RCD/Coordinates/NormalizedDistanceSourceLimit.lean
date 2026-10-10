import OAI.Geometry.RCD.Harmonic.RadialDyadicBudget

namespace OAI

/-! # Vanishing normalized distance-source mass from equal volume limits -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem radial_mass_normalized_tendsto_zero {n κ ω : ℝ}
    (hn : 0<n) (hκ : 0≤κ) (r M V W : ℕ → ℝ)
    (hr : ∀ k, 0<r k) (hM : ∀ k, 0≤M k)
    (hr0 : Tendsto r atTop (𝓝 0))
    (hV : Tendsto (fun k => (r k)^(-n)*V k) atTop (𝓝 ω))
    (hW : Tendsto (fun k => (2*r k)^(-n)*W k) atTop (𝓝 ω))
    (hmass : ∀ k, (((r k)^(-n)-(2*r k)^(-n))/n)*M k≤
      (r k)^(-n)*V k-(2*r k)^(-n)*W k+
        (κ*(4*r k)^2)*(((r k)^(-n)-(2*r k)^(-n))/n)*W k) :
    Tendsto (fun k => (r k)^(-n)*M k) atTop (𝓝 0) := by
  let C k := (2*r k)^(-n)*W k
  have hbound k : W k≤C k*(2*r k)^n := by
    apply le_of_eq
    dsimp only [C]
    have hp : 0<2*r k := mul_pos (by norm_num) (hr k)
    rw [Real.rpow_neg hp.le]
    calc
      W k = W k*((2*r k)^n)⁻¹*(2*r k)^n := by
        rw [mul_assoc, inv_mul_cancel₀ (Real.rpow_pos_of_pos hp n).ne', mul_one]
      _ = _ := by ring
  have hb k := radial_mass_normalized_le hn (hr k) (by positivity : 0≤κ*(4*r k)^2)
    (hbound k) (hmass k)
  have hcurv : Tendsto (fun k => κ*(4*r k)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : 2≠0)] using ((hr0.const_mul 4).pow 2).const_mul κ
  have hlim : Tendsto (fun k => (radialCutoffCoefficient n)⁻¹*
      ((r k)^(-n)*V k-(2*r k)^(-n)*W k)+(κ*(4*r k)^2)*C k*2^n) atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero,zero_mul,add_zero] using
      ((hV.sub hW).const_mul (radialCutoffCoefficient n)⁻¹).add ((hcurv.mul hW).mul_const (2^n))
  exact squeeze_zero (fun k => mul_nonneg (Real.rpow_nonneg (hr k).le _) (hM k)) hb hlim

end RegularPointCoordinates

end

end OAI
