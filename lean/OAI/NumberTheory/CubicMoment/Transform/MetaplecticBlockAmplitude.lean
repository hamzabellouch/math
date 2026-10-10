import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBlockCoefficient

namespace OAI

/-! Scalar simplifications of the two actual retained-block amplitudes.
The ramified endpoint k=0 is included in the same geometric sequence. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_sqrt_block_base {b H P : ℝ} (hb : 0 < b) (hH : 0 < H) (hP : 0 < P) :
    Real.sqrt (b*H*P^3) = Real.sqrt b*Real.sqrt H*P*Real.sqrt P := by
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul hb.le]
  have hp : Real.sqrt (P^3) = P*Real.sqrt P := by
    rw [show P^3=P^2*P by ring,Real.sqrt_mul (sq_nonneg P),Real.sqrt_sq_eq_abs,
      abs_of_pos hP]
  rw [hp]
  ring

lemma metaplectic_block_scalar {b H P D : ℝ}
    (hb : 0 < b) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (C α g : ℝ) :
    C*α*Real.sqrt P*g/(Real.sqrt (b*H*P^3)*D) =
      (C*α/Real.sqrt b)*(g/(D*P*Real.sqrt H)) := by
  rw [metaplectic_sqrt_block_base hb hH hP]
  field_simp [(Real.sqrt_pos.mpr hb).ne',(Real.sqrt_pos.mpr hH).ne',
    (Real.sqrt_pos.mpr hP).ne',hD.ne',hP.ne']

lemma metaplectic_ramified_first_ratio (k : ℕ) :
    (3:ℝ)^((k:ℝ)/3)/Real.sqrt ((3:ℝ)^((k:ℝ)-1)) =
      Real.sqrt 3*((3:ℝ)^(-1/6:ℝ))^k := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul (by norm_num),
    ←Real.rpow_sub (by norm_num),Real.sqrt_eq_rpow,
    ←Real.rpow_mul_natCast (by norm_num),←Real.rpow_add (by norm_num)]
  congr 1
  ring

lemma metaplectic_ramified_second_ratio (k : ℕ) :
    (3:ℝ)^((k:ℝ)/3)/((3:ℝ)^((k:ℝ)-1)) =
      3*((3:ℝ)^(-2/3:ℝ))^k := by
  rw [←Real.rpow_sub (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  calc
    _ = (3:ℝ)^(1+(-2/3)*(k:ℝ)) := by congr 1; ring
    _ = _ := by rw [Real.rpow_add (by norm_num),Real.rpow_one]

lemma metaplectic_common_first_amplitude {R H P D g : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (hg : g ≤ Real.sqrt (R*(H*P))) :
    g/(D*P*Real.sqrt H) ≤ Real.sqrt R/(D*Real.sqrt P) := by
  apply (div_le_iff₀ (by positivity : 0 < D*P*Real.sqrt H)).mpr
  have he : Real.sqrt (R*(H*P)) =
      Real.sqrt R*Real.sqrt H*Real.sqrt P := by
    rw [Real.sqrt_mul hR.le,Real.sqrt_mul hH.le]
    ring
  have ht : Real.sqrt R/(D*Real.sqrt P)*(D*P*Real.sqrt H) =
      Real.sqrt R*Real.sqrt H*Real.sqrt P := by
    have hp : P/Real.sqrt P = Real.sqrt P := by
      apply (div_eq_iff (Real.sqrt_pos.mpr hP).ne').mpr
      nlinarith [Real.sq_sqrt hP.le]
    calc
      _ = Real.sqrt R*Real.sqrt H*(P/Real.sqrt P) := by
        field_simp [(Real.sqrt_pos.mpr hP).ne',hD.ne']
      _ = _ := by rw [hp]
  rw [ht]
  exact hg.trans_eq he

lemma metaplectic_common_second_amplitude {H P D g : ℝ}
    (hH : 0 < H) (hP : 0 < P) (hD : 0 < D) (hg : g ≤ H*P) :
    g/(D*P*Real.sqrt H) ≤ Real.sqrt H/D := by
  apply (div_le_iff₀ (by positivity : 0 < D*P*Real.sqrt H)).mpr
  have he : Real.sqrt H/D*(D*P*Real.sqrt H) = H*P := by
    calc
      _ = P*(Real.sqrt H)^2 := by field_simp [hD.ne']
      _ = _ := by rw [Real.sq_sqrt hH.le]; ring
  rw [he]
  exact hg

end CubicFirstMoment

end

end OAI
