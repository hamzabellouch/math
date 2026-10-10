import OAI.MeasureTheory.Falconer.Radial.FinitePlateException

namespace OAI

/-! # Explicit power budget for transverse plate intersections -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem plate_intersection_ratio {δ : ℝ} (hδ : 0 < δ) (A : ℝ) :
    10*(A*δ^(1/4:ℝ))/δ^(1/8:ℝ) = (10*A)*δ^(1/8:ℝ) := by
  have he : (1/4:ℝ) = 1/8+1/8 := by norm_num
  rw [he,Real.rpow_add hδ]
  field_simp

theorem plate_power_identity {δ : ℝ} (hδ : 0 < δ) (A B a q : ℝ) (hA : 0 ≤ A) :
    (A*δ^(-q))^2*(B*(10*(A*δ^(1/4:ℝ))/δ^(1/8:ℝ))^a) =
      (A^2*B*(10*A)^a)*δ^(a/8-2*q) := by
  have hsquare : (δ^(-q))^2 = δ^(-2*q) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    norm_num
    ring
  have hp : (δ^(1/8:ℝ))^a = δ^(a/8) := by
    rw [← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [mul_pow,hsquare,plate_intersection_ratio hδ,
    Real.mul_rpow (mul_nonneg (by norm_num) hA) (Real.rpow_nonneg hδ.le _),hp]
  calc
    _ = (A^2*B*(10*A)^a)*(δ^(-2*q)*δ^(a/8)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hδ]
      congr 2
      ring

theorem plate_card_power_bound {n : ℕ} {δ A B a q : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (hcard : (n:ℝ) ≤ A*δ^(-q)) :
    (n:ℝ≥0∞)^2*ENNReal.ofReal (B*(10*(A*δ^(1/4:ℝ))/δ^(1/8:ℝ))^a) ≤
      ENNReal.ofReal ((A^2*B*(10*A)^a)*δ^(a/8-2*q)) := by
  have hN : 0 ≤ A*δ^(-q) := mul_nonneg hA (Real.rpow_nonneg hδ.le _)
  have hc : (n:ℝ≥0∞) ≤ ENNReal.ofReal (A*δ^(-q)) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
  apply (mul_le_mul_left (pow_le_pow_left' hc 2) _).trans_eq
  rw [← ENNReal.ofReal_pow hN,← ENNReal.ofReal_mul (sq_nonneg _),
    plate_power_identity hδ A B a q hA]

theorem slabPairException_power {d : ℕ} (μ : Measure (Space d))
    (S : Finset (Space d × ℝ)) {M s C δ A q : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 0 < A) (hsmall : 10*A*δ^(1/8:ℝ) ≤ 1)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hunit : ∀ p ∈ S, ‖p.1‖ = 1) (hcard : (S.card:ℝ) ≤ A*δ^(-q)) :
    μ (slabPairException S (A*δ^(1/4:ℝ)) (δ^(1/8:ℝ))) ≤
      ENNReal.ofReal ((A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ)))*
        δ^((s-((d-2:ℕ):ℝ))/8-2*q)) := by
  apply (slabPairException_mass μ S hM hC hbounded hfrost hunit
    (Real.rpow_pos_of_pos hδ _) (Real.rpow_le_one hδ.le hδ1 (by norm_num))
    (mul_pos hA (Real.rpow_pos_of_pos hδ _)) ?_).trans
    (plate_card_power_bound hδ hA.le hcard)
  simpa only [plate_intersection_ratio hδ A] using hsmall

end Falconer

end OAI
