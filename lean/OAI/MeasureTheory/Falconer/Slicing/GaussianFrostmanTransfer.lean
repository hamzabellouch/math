import OAI.MeasureTheory.Falconer.Slicing.GaussianDyadicGeometry
import OAI.MeasureTheory.Falconer.Geometry.TruncatedDyadicBalls
import OAI.MeasureTheory.Falconer.Slicing.SliceNormalization

namespace OAI

/-! # Frostman bounds for the actual normalized and oriented slice laws -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d h m : ℕ}

theorem gaussian_point_normalized_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TP : Fin (N+1) → ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K L a H P f : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (ha : 1 ≤ a) (hH : 1 ≤ H)
    (hP : 0 ≤ P) (hf : 0 ≤ f)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4*L+2*K*(h:ℝ) ≤ a)
    (hTP : ∀ g, TP g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^f))
    (hα : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ ≠ 0)
    (hratio : ENNReal.ofReal P /
      (((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ) ≤ ENNReal.ofReal H) :
    ∀ (c : Space m) (s : ℝ), 1/(2:ℝ)^N ≤ s →
      (normalizedSliceLaw ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) hα : Measure (Space d))
        {x | dist (L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤
      ENNReal.ofReal (H*(4*a*s)^f) := by
  let α := (gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
    (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))
  apply truncated_dyadic_ball_bound (normalizedSliceLaw α hα : Measure (Space d))
    (fun x => L⁻¹ • e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) N ha hH hf (by simp)
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hball := gaussian_scaled_point_test μ A z e (1/(2:ℝ)^N) r TP j hK hL
    (by linarith) (by positivity) hbound haK hδ (hr j) c
  rw [normalizedSliceLaw_apply]
  calc
    _ ≤ (α univ)⁻¹*ENNReal.ofReal (P*(1/(2:ℝ)^g)^f) :=
      mul_le_mul' le_rfl (hball.trans (hTP j))
    _ = (ENNReal.ofReal P / α univ)*ENNReal.ofReal ((1/(2:ℝ)^g)^f) := by
      rw [ENNReal.ofReal_mul hP]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((1/(2:ℝ)^g)^f) := mul_le_mul' hratio le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ H)]

theorem gaussian_direction_normalized_frostman
    (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (A : Fin h → Space d)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TD : Fin (N+1) → ℝ≥0∞) (M : ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K a H P b : ℝ} (hK : 0 ≤ K) (ha : 1 ≤ a) (hH : 1 ≤ H) (hP : 0 ≤ P) (hb : 0 ≤ b)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (hsmall : K*((h:ℝ)*(1/(2:ℝ)^N)) < 1) (haK : 4+4*K*(h:ℝ) ≤ a)
    (hTD : ∀ g, TD g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^b))
    (hβ : ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
      (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) univ ≠ 0)
    (hratio : ENNReal.ofReal P /
      (((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
        (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) univ) ≤ ENNReal.ofReal H) :
    ∀ (c : Space m) (s : ℝ), 1/(2:ℝ)^N ≤ s →
      (normalizedSliceLaw ((gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
        (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)) hβ : Measure (Sphere d))
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ s} ≤
      ENNReal.ofReal (H*(4*a*s)^b) := by
  let β := (gaussianDirectionSliceMeasure ν A (1/(2:ℝ)^N)).restrict
    (gaussianDirectionGood ν (1/(2:ℝ)^N) r TD M A)
  apply truncated_dyadic_ball_bound (normalizedSliceLaw β hβ : Measure (Sphere d))
    (fun w : Sphere d => normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
    N ha hH hb (by simp)
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hball := gaussian_normalized_direction_test ν A e (1/(2:ℝ)^N) r TD M j hK
    (by linarith) (by positivity) hbound hsmall haK hδ (hr j) c
  rw [normalizedSliceLaw_apply]
  calc
    _ ≤ (β univ)⁻¹*ENNReal.ofReal (P*(1/(2:ℝ)^g)^b) :=
      mul_le_mul' le_rfl (hball.trans (hTD j))
    _ = (ENNReal.ofReal P / β univ)*ENNReal.ofReal ((1/(2:ℝ)^g)^b) := by
      rw [ENNReal.ofReal_mul hP]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ ENNReal.ofReal H*ENNReal.ofReal ((1/(2:ℝ)^g)^b) := mul_le_mul' hratio le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ H)]

end Falconer

end OAI
