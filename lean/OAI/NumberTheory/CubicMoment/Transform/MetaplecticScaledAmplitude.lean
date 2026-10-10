import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBlockAmplitude

namespace OAI

/-! The two separated scalar majorants for a retained norm dyad.
The square-root level normalization is kept explicit. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_ramified_exponent_le (k : ℕ) :
    (3:ℝ)^((max ((k:ℤ)-1) 0:ℤ)/3:ℝ) ≤ (3:ℝ)^((k:ℝ)/3) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h : max ((k:ℤ)-1) 0 ≤ (k:ℤ) := by omega
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)

lemma metaplectic_first_scaled_amplitude {R H P D g C α b : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (hb : 0 < b) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hg : g ≤ Real.sqrt (R*(H*P))) :
    (C*α*Real.sqrt P*g/(Real.sqrt (b*H*P^3)*D))/Real.sqrt R ≤
      (C*α/Real.sqrt b)/(D*Real.sqrt P) := by
  rw [metaplectic_block_scalar hb hH hP hD]
  have he := metaplectic_common_first_amplitude hR hH hP hD hg
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  calc
    _ ≤ (C*α/Real.sqrt b)*(Real.sqrt R/(D*Real.sqrt P)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

lemma metaplectic_free_sqrt {I T D b H P : ℝ}
    (hD : 0 < D) (hb : 0 < b) (hH : 0 < H) (hP : 0 < P) :
    Real.sqrt (2*(I/(D^3*(b*H*P^3)))/T) =
      Real.sqrt (2*I/T)/(D*Real.sqrt D*Real.sqrt b*Real.sqrt H*P*Real.sqrt P) := by
  rw [show 2*(I/(D^3*(b*H*P^3)))/T = (2*I/T)/(D^3*(b*H*P^3)) by ring,
    Real.sqrt_div' _ (by positivity : 0 ≤ D^3*(b*H*P^3)),
    Real.sqrt_mul (by positivity : 0 ≤ D^3),
    metaplectic_sqrt_block_base hb hH hP]
  have hd : Real.sqrt (D^3) = D*Real.sqrt D := by
    rw [show D^3=D^2*D by ring,Real.sqrt_mul (sq_nonneg D),
      Real.sqrt_sq_eq_abs,abs_of_pos hD]
  rw [hd]
  congr 1
  ring

lemma metaplectic_second_scaled_amplitude {R H P D g C α b I T : ℝ}
    (hR : 0 < R) (hH : 0 < H) (hP : 0 < P) (hD : 0 < D)
    (hb : 0 < b) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hg : g ≤ H*P) :
    (C*α*Real.sqrt P*g/(Real.sqrt (b*H*P^3)*D))/Real.sqrt R *
        Real.sqrt (2*(I/(D^3*(b*H*P^3)))/T) ≤
      C*(α/b)*Real.sqrt (2*I/(R*T))/(D^2*Real.sqrt D*P*Real.sqrt P) := by
  rw [metaplectic_block_scalar hb hH hP hD]
  have he := metaplectic_common_second_amplitude hH hP hD hg
  calc
    _ ≤ ((C*α/Real.sqrt b)*(Real.sqrt H/D))/Real.sqrt R *
        Real.sqrt (2*(I/(D^3*(b*H*P^3)))/T) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by
      rw [metaplectic_free_sqrt hD hb hH hP]
      rw [show 2*I/(R*T)=(2*I/T)/R by ring,Real.sqrt_div' _ hR.le]
      have hs := Real.sq_sqrt hb.le
      field_simp [(Real.sqrt_pos.mpr hR).ne',(Real.sqrt_pos.mpr hH).ne',
        (Real.sqrt_pos.mpr hP).ne',(Real.sqrt_pos.mpr hD).ne',
        (Real.sqrt_pos.mpr hb).ne',hD.ne',hP.ne',hb.ne']
      rw [hs]
      ring

end CubicFirstMoment

end

end OAI
