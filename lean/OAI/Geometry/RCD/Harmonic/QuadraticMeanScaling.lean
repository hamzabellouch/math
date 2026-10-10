import OAI.Geometry.RCD.Sobolev.SmallRadiusPoissonMean

namespace OAI

/-! # Dimensionless quadratic mean errors at shrinking radii -/

open Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem centered_second_variation_fourth_order {K D a R : ℝ} (hD : 0≤D) (hR : 0<R) :
    (3*Real.sqrt (Real.exp |K| *(16*D*(R+32*(6*R))^2/(a/4)^2))*Real.exp |K|)^4=
      R^4*(3*Real.sqrt (Real.exp |K| *(16*D*193^2/(a/4)^2))*Real.exp |K|)^4 := by
  have hbase : 0≤Real.exp |K| *(16*D*193^2/(a/4)^2) := by positivity
  have he : Real.exp |K| *(16*D*(R+32*(6*R))^2/(a/4)^2)=
      (Real.exp |K| *(16*D*193^2/(a/4)^2))*R^2 := by ring
  rw [he,Real.sqrt_mul hbase,Real.sqrt_sq_eq_abs,abs_of_pos hR]
  ring

def poissonMeanConstant (K D a : ℝ) : ℝ :=
  Real.sqrt ((3*Real.sqrt (Real.exp |K| *(16*D*193^2/(a/4)^2))*Real.exp |K|)^4)/(4*512^2)

theorem poissonMeanConstant_nonneg (K D a : ℝ) : 0≤poissonMeanConstant K D a := by
  unfold poissonMeanConstant
  positivity

theorem centered_mean_coefficient {K D a r : ℝ} (hD : 0≤D) (hr : 0<r) :
    Real.sqrt ((3*Real.sqrt (Real.exp |K| *
      (16*D*((r/512)+32*(6*(r/512)))^2/(a/4)^2))*Real.exp |K|)^4)/4=
      poissonMeanConstant K D a*r^2 := by
  rw [centered_second_variation_fourth_order hD (div_pos hr (by norm_num)),
    Real.sqrt_mul (by positivity : 0≤(r/512)^4)]
  rw [show (r/512)^4=((r/512)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  unfold poissonMeanConstant
  ring

theorem sqrt_mass_normalization {V B : ℝ} (hV : 0<V) (hB : 0≤B) :
    Real.sqrt V*Real.sqrt B=V*Real.sqrt (B/V) := by
  rw [Real.sqrt_div hB,div_eq_mul_inv]
  have hv : Real.sqrt V≠0 := (Real.sqrt_pos.mpr hV).ne'
  apply (mul_left_inj' hv).mp
  calc
    (Real.sqrt V*Real.sqrt B)*Real.sqrt V=V*Real.sqrt B := by
      rw [mul_right_comm,← pow_two,Real.sq_sqrt hV.le]
    _ = (V*(Real.sqrt B*(Real.sqrt V)⁻¹))*Real.sqrt V := by
      field_simp

theorem normalized_quadratic_mean_error_tendsto_zero
    (r V B P E : ℕ → ℝ) {C A : ℝ}
    (hr : ∀ k, 0<r k) (hV : ∀ k, 0<V k) (hB : ∀ k, 0≤B k)
    (hA : 0≤A)
    (hcompression : ∀ k, P k*V k≤C)
    (hmass : Tendsto (fun k => B k/V k) atTop (𝓝 0))
    (hE : ∀ k, |E k|≤A*(r k)^2*P k*Real.sqrt (V k)*Real.sqrt (B k)) :
    Tendsto (fun k => E k/(r k)^2) atTop (𝓝 0) := by
  have hbound k : |E k/(r k)^2|≤(A*C)*Real.sqrt (B k/V k) := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos (hr k))]
    apply (div_le_iff₀ (sq_pos_of_pos (hr k))).mpr
    calc
      |E k| ≤ A*(r k)^2*P k*Real.sqrt (V k)*Real.sqrt (B k) := hE k
      _ = (A*(r k)^2)*(P k*V k)*Real.sqrt (B k/V k) := by
        rw [mul_assoc _ _ (Real.sqrt (B k)),sqrt_mass_normalization (hV k) (hB k)]
        ring
      _ ≤ (A*(r k)^2)*C*Real.sqrt (B k/V k) := by
        gcongr
        exact hcompression k
      _ = _ := by ring
  have hlim : Tendsto (fun k => (A*C)*Real.sqrt (B k/V k)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,mul_zero] using hmass.sqrt.const_mul (A*C)
  exact squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using hbound k) hlim

end RegularPointCoordinates

end

end OAI
