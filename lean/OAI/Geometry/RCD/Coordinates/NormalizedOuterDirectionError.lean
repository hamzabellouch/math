import OAI.Geometry.RCD.Coordinates.NormalizedMeanDirectionError

namespace OAI

/-! # Outer-ball errors for a frame normalized on an inner set -/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem normalized_outer_direction_error (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (S Ω : Set X) (hS : MeasurableSet S)
    (hz : μ S ≠ 0) (hf : μ S ≠ ⊤) (hΩz : μ Ω ≠ 0) (hΩf : μ Ω ≠ ⊤)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hsmall : (n : ℝ)^2*δ ≤ 1/2)
    (hinner : ∀ i j : Fin n, (μ.real S)⁻¹*∫ x in S,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ ≤ δ)
    (houter : ∀ i j : Fin n, (μ.real Ω)⁻¹*∫ x in Ω,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ ≤ ε)
    (A : Euclidean n ≃L[ℝ] Euclidean n)
    (hA : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u) S hS A)
    (v : Euclidean n) :
    (μ.real Ω)⁻¹*(∫ x in Ω,
      |localGamma μ hQ (sobolevColumnMap μ hQ u (A v))
        (sobolevColumnMap μ hQ u (A v)) x-‖v‖^2| ∂μ)
      ≤ 2*(n : ℝ)^2*(ε+δ)*‖v‖^2 := by
  have hm : 0 < μ.real Ω := ENNReal.toReal_pos hΩz hΩf
  have hraw (i j : Fin n) : (∫ x in Ω,
      |localGamma μ hQ (u i) (u j) x-(if i=j then 1 else 0)| ∂μ) ≤ ε*μ.real Ω := by
    apply (div_le_iff₀ hm).mp
    simpa only [div_eq_inv_mul] using houter i j
  have hdir := directional_gram_error_le μ hQ u Ω hΩf (mul_nonneg hε hm.le) hraw (A v)
  let Q := sobolevMeanGram μ hQ (sobolevColumnMap μ hQ u) S hS
  have hQerr := meanGram_sub_id_norm_le μ hQ u S hS hz hf hδ hinner
  have hnorm := exact_mean_normalizer_bounds μ hQ u S hS hz hf hδ hinner A hA v
  have hAv : ‖A v‖^2 ≤ 2*‖v‖^2 := by
    have hb := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖A v‖)
    nlinarith [hnorm.1]
  have he : ⟪A v,Q (A v)⟫_ℝ = ‖v‖^2 := by
    dsimp only [Q]
    rw [meanGram_energy_of_exact_normalization μ hQ (sobolevColumnMap μ hQ u) S hS A hA,
      A.symm_apply_apply]
  have hshift : |‖A v‖^2-‖v‖^2| ≤ (n : ℝ)^2*δ*‖A v‖^2 := by
    have hlo := inner_lower_of_sub_id_norm Q hQerr (A v)
    have hup := inner_upper_of_sub_id_norm Q hQerr (A v)
    rw [he] at hlo hup
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have htri := integral_abs_sub_const_le μ
    (localGamma_memL1 μ hQ (sobolevColumnMap μ hQ u (A v))
      (sobolevColumnMap μ hQ u (A v))).integrableOn hΩf (‖A v‖^2) (‖v‖^2)
  have hdel := mul_le_mul_of_nonneg_left hshift hm.le
  have hnormterm := mul_le_mul_of_nonneg_left hAv
    (mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) (add_nonneg hε hδ)) hm.le)
  have hbound : (∫ x in Ω,
      |localGamma μ hQ (sobolevColumnMap μ hQ u (A v))
        (sobolevColumnMap μ hQ u (A v)) x-‖v‖^2| ∂μ)
      ≤ 2*(n : ℝ)^2*(ε+δ)*μ.real Ω*‖v‖^2 := by
    nlinarith only [htri,hdir,hdel,hnormterm]
  calc
    _ ≤ (μ.real Ω)⁻¹*(2*(n : ℝ)^2*(ε+δ)*μ.real Ω*‖v‖^2) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hm.le)
    _ = _ := by field_simp

end RegularPointCoordinates

end

end OAI
