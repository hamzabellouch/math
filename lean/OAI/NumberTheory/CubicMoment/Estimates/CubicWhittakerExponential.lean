import OAI.NumberTheory.CubicMoment.Estimates.CubicWhittakerBounds

namespace OAI

/-! Exponential decay retaining an arbitrarily summable polynomial factor. -/
noncomputable section
namespace CubicFirstMoment

def cubicWhittakerExpConstant : ℝ :=
  (Real.Gamma (1/3)*2^(1/3:ℝ)/2)*(2*Real.pi)^(-1/3:ℝ)

lemma cubicWhittakerExpConstant_pos : 0 < cubicWhittakerExpConstant := by
  have hg := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/3)
  unfold cubicWhittakerExpConstant
  positivity

lemma cubicBesselKernel_exp_power_bound {x : ℝ} (hx : 0 < x) :
    cubicBesselKernel x ≤ (Real.Gamma (1/3)*2^(1/3:ℝ))*
      x^(-1/6:ℝ)*Real.exp (-Real.sqrt x) := by
  apply (cubicBesselKernel_exp_bound hx).trans_eq
  calc
    _ = (Real.Gamma (1/3)*Real.exp (-Real.sqrt x))*(x^(1/6:ℝ)*(x/2)^(-1/3:ℝ)) := by ring
    _ = _ := by rw [cubicBessel_exp_prefactor hx]; ring

lemma cubicThetaWhittaker_exponential_bound {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ ≤
      cubicWhittakerExpConstant*v^(2/3:ℝ)*Real.exp (-(2*Real.pi*v)) := by
  rw [cubicThetaWhittaker_norm hv]
  apply (mul_le_mul_of_nonneg_left
    (cubicBesselKernel_exp_power_bound (show 0 < (2*Real.pi*v)^2 by positivity))
    (by positivity : 0 ≤ v/2)).trans_eq
  have hbase : 0 < 2*Real.pi*v := by positivity
  rw [Real.sqrt_sq_eq_abs,abs_of_pos hbase]
  have hp : ((2*Real.pi*v)^2)^(-1/6:ℝ) = (2*Real.pi)^(-1/3:ℝ)*v^(-1/3:ℝ) := by
    rw [←Real.rpow_natCast_mul hbase.le]
    norm_num only [Nat.cast_ofNat]
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*Real.pi) hv.le]
  rw [hp]
  have hvp : v*v^(-1/3:ℝ) = v^(2/3:ℝ) := by
    calc
      _ = v^(1:ℝ)*v^(-1/3:ℝ) := by rw [Real.rpow_one]
      _ = v^(1+(-1/3:ℝ)) := (Real.rpow_add hv _ _).symm
      _ = _ := by congr 1; ring
  unfold cubicWhittakerExpConstant
  calc
    _ = ((Real.Gamma (1/3)*2^(1/3:ℝ)/2)*(2*Real.pi)^(-1/3:ℝ))*
      (v*v^(-1/3:ℝ))*Real.exp (-(2*Real.pi*v)) := by ring
    _ = _ := by rw [hvp]

def cubicWhittakerMixedConstant : ℝ := cubicWhittakerExpConstant*720/Real.pi^6

lemma cubicWhittakerMixedConstant_pos : 0 < cubicWhittakerMixedConstant := by
  unfold cubicWhittakerMixedConstant
  exact div_pos (mul_pos cubicWhittakerExpConstant_pos (by norm_num)) (pow_pos Real.pi_pos 6)

/-- Half the exponential is retained, while the other half supplies six
powers of decay for the two-dimensional frequency sum. -/
theorem cubicThetaWhittaker_mixed_bound {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖ ≤
      cubicWhittakerMixedConstant*v^(-16/3:ℝ)*Real.exp (-Real.pi*v) := by
  have he : Real.exp (-Real.pi*v) ≤ (720:ℝ)/(Real.pi*v)^6 := by
    have h := exp_neg_div_le_power 6 (mul_pos Real.pi_pos hv) (show (0:ℝ) < 1 by norm_num)
    norm_num at h
    simpa only [neg_mul] using h
  have hA := cubicWhittakerExpConstant_pos.le
  have hsplit : Real.exp (-(2*Real.pi*v)) = Real.exp (-Real.pi*v)*Real.exp (-Real.pi*v) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ cubicWhittakerExpConstant*v^(2/3:ℝ)*Real.exp (-(2*Real.pi*v)) :=
      cubicThetaWhittaker_exponential_bound hv
    _ = (cubicWhittakerExpConstant*v^(2/3:ℝ)*Real.exp (-Real.pi*v))*Real.exp (-Real.pi*v) := by
      rw [hsplit]; ring
    _ ≤ (cubicWhittakerExpConstant*v^(2/3:ℝ)*(720/(Real.pi*v)^6))*Real.exp (-Real.pi*v) := by
      gcongr
    _ = _ := by
      have hvp : v^(2/3:ℝ)/v^6 = v^(-16/3:ℝ) := by
        rw [←Real.rpow_natCast v 6,←Real.rpow_sub hv]
        congr 1
        norm_num
      unfold cubicWhittakerMixedConstant
      rw [mul_pow]
      calc
        _ = (cubicWhittakerExpConstant*720/Real.pi^6)*(v^(2/3:ℝ)/v^6)*Real.exp (-Real.pi*v) := by ring
        _ = _ := by rw [hvp]

end CubicFirstMoment

end

end OAI
