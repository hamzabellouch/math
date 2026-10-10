import OAI.NumberTheory.TotientAsymptotic.CoordinateCube

namespace OAI

/-! Fixed-tolerance arithmetic for transferring the simplex concentration event
through diagonal normalization and the unit-box correction. -/
noncomputable section
namespace TotientAsymptotic

lemma coordinate_band_transfer {u v S T κ : ℝ} (_hS : 0<S) (hT : 0<T)
    (hκ : 0 ≤ κ)
    (hcenter : (99/100:ℝ)*S ≤ κ*T ∧ κ*T ≤ (101/100:ℝ)*S)
    (hdist : |u-κ*v| ≤ S/100)
    (hgood : |v/T-1| ≤ (1/40:ℝ)) :
    (19/20:ℝ)*S ≤ u ∧ u ≤ (21/20:ℝ)*S := by
  have hvlo : (39/40:ℝ)*T ≤ v := by
    have hh := (abs_le.mp hgood).1
    have hh' : (39/40:ℝ) ≤ v/T := by linarith only [hh]
    exact (le_div_iff₀ hT).mp hh'
  have hvhi : v ≤ (41/40:ℝ)*T := by
    have hh := (abs_le.mp hgood).2
    have hh' : v/T ≤ (41/40:ℝ) := by linarith only [hh]
    exact (div_le_iff₀ hT).mp hh'
  have hlo := mul_le_mul_of_nonneg_left hvlo hκ
  have hhi := mul_le_mul_of_nonneg_left hvhi hκ
  have hdist' := abs_le.mp hdist
  constructor <;> nlinarith only [hcenter.1,hcenter.2,hlo,hhi,hdist'.1,hdist'.2]

lemma coordinate_cube_band_transfer {N : ℕ} {b : Fin N → ℕ}
    {u v κ : Fin N → ℝ} {i : Fin N} {S T : ℝ}
    (hu : u∈unitGridCell b) (hv : v∈unitGridCell b)
    (hS : 0<S) (hT : 0<T) (hκ : 1 ≤ κ i)
    (hcenter : (99/100:ℝ)*S ≤ κ i*T ∧ κ i*T ≤ (101/100:ℝ)*S)
    (herror : 1+κ i*coordinateCubeShift N i ≤ S/100)
    (hgood : |(simplexScale κ v+coordinateCubeShift N) i/T-1| ≤ (1/40:ℝ)) :
    (19/20:ℝ)*S ≤ u i ∧ u i ≤ (21/20:ℝ)*S := by
  apply coordinate_band_transfer hS hT (zero_le_one.trans hκ) hcenter _ hgood
  have hκpos : 0<κ i := zero_lt_one.trans_le hκ
  have he : u i-κ i*(simplexScale κ v+coordinateCubeShift N) i =
      (u i-v i)-κ i*coordinateCubeShift N i := by
    simp only [Pi.add_apply,simplexScale_apply]
    field_simp
    ring
  rw [he]
  have hh : |(u i-v i)-κ i*coordinateCubeShift N i| ≤
      |u i-v i|+|κ i*coordinateCubeShift N i| := by
    simpa using abs_sub_le (u i-v i) 0 (κ i*coordinateCubeShift N i)
  apply hh.trans
  have hnon : 0 ≤ κ i*coordinateCubeShift N i :=
    mul_nonneg hκpos.le (coordinateCubeShift_nonneg N i)
  rw [abs_of_nonneg hnon]
  have hdist := unitGridCell_coordinate_distance hu hv i
  linarith only [hdist,herror]

end TotientAsymptotic

end

end OAI
