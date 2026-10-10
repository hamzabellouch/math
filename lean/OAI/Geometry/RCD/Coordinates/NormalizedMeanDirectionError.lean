import OAI.Geometry.RCD.Coordinates.NormalizedDirectionError

namespace OAI

/-! # Quantitative directional error for the constructed exact normalizer -/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem normalized_mean_direction_error (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (S : Set X) (hS : MeasurableSet S)
    (hz : μ S≠0) (hf : μ S≠⊤) {ε : ℝ} (hε : 0≤ε) (hsmall : (n:ℝ)^2*ε≤1/2)
    (herr : ∀ i j : Fin n, (μ.real S)⁻¹*∫ x in S,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ≤ε)
    (A : Euclidean n ≃L[ℝ] Euclidean n)
    (hA : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) S hS A)
    (v : Euclidean n) :
    (μ.real S)⁻¹*(∫ x in S,
      |localGamma μ hQ (sobolevColumnMap μ hQ u (A v))
        (sobolevColumnMap μ hQ u (A v)) x-‖v‖^2| ∂μ)≤4*(n:ℝ)^2*ε*‖v‖^2 := by
  have hm : 0<μ.real S := ENNReal.toReal_pos hz hf
  have hraw (i j : Fin n) : (∫ x in S,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ)≤ε*μ.real S := by
    apply (div_le_iff₀ hm).mp
    simpa only [div_eq_inv_mul] using herr i j
  have hdir := directional_gram_error_le μ hQ u S hf (mul_nonneg hε hm.le) hraw (A v)
  let Q := sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) S hS
  have hQerr := meanGram_sub_id_norm_le μ hQ u S hS hz hf hε herr
  have hnorm := exact_mean_normalizer_bounds μ hQ u S hS hz hf hε herr A hA v
  have hAv : ‖A v‖^2≤2*‖v‖^2 := by
    have hb := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖A v‖)
    nlinarith [hnorm.1]
  have he : ⟪A v,Q (A v)⟫_ℝ=‖v‖^2 := by
    dsimp only [Q]
    rw [meanGram_energy_of_exact_normalization μ hQ (sobolevColumnMap μ hQ u) S hS A hA,
      A.symm_apply_apply]
  have hdelta : |‖A v‖^2-‖v‖^2|≤(n:ℝ)^2*ε*‖A v‖^2 := by
    have hlo := inner_lower_of_sub_id_norm Q hQerr (A v)
    have hup := inner_upper_of_sub_id_norm Q hQerr (A v)
    rw [he] at hlo hup
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have htri := integral_abs_sub_const_le μ
    (localGamma_memL1 μ hQ (sobolevColumnMap μ hQ u (A v))
      (sobolevColumnMap μ hQ u (A v))).integrableOn hf (‖A v‖^2) (‖v‖^2)
  have hdel := mul_le_mul_of_nonneg_left hdelta hm.le
  have hnormterm := mul_le_mul_of_nonneg_left hAv
    (mul_nonneg (mul_nonneg (sq_nonneg (n:ℝ)) hε) hm.le)
  have hbound : (∫ x in S,
      |localGamma μ hQ (sobolevColumnMap μ hQ u (A v))
        (sobolevColumnMap μ hQ u (A v)) x-‖v‖^2| ∂μ)≤4*(n:ℝ)^2*ε*μ.real S*‖v‖^2 := by
    nlinarith only [htri,hdir,hdel,hnormterm]
  calc
    _ ≤ (μ.real S)⁻¹*(4*(n:ℝ)^2*ε*μ.real S*‖v‖^2) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hm.le)
    _ = _ := by field_simp

end RegularPointCoordinates

end

end OAI
