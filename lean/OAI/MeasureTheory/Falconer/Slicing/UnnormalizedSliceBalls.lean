import OAI.MeasureTheory.Falconer.Slicing.GaussianDyadicGeometry
import OAI.MeasureTheory.Falconer.Geometry.TruncatedDyadicBalls

namespace OAI

/-! # All-radius point estimates before normalizing a slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {d h m : ℕ}

theorem truncated_dyadic_ball_bound_mass
    (μ : Measure X) (p : X → Space m) (N : ℕ) {a H s : ℝ}
    (ha : 1 ≤ a) (hH : 0 ≤ H) (hs : 0 ≤ s) (hmass : μ univ ≤ ENNReal.ofReal H)
    (hdyadic : ∀ g ≤ N, 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g → ∀ c : Space m,
      μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} ≤
        ENNReal.ofReal (H*(1/(2:ℝ)^g)^s)) :
    ∀ (c : Space m) (r : ℝ), 1/(2:ℝ)^N ≤ r →
      μ {x | dist (p x) c ≤ r} ≤ ENNReal.ofReal (H*(4*a*r)^s) := by
  intro c r hr
  have hrp : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hsmall : 2*a*r ≤ 1
  · have hmin : 1/(2:ℝ)^N ≤ 2*a*r := hr.trans (by nlinarith)
    obtain ⟨g,hg,hgr,hrg⟩ := Regularization.dyadic_radius_bracket hmin hsmall
    have hcut : 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g :=
      (mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 2*a)).trans hgr
    have hrad : r ≤ (1/(2:ℝ)^g)/(2*a) := (le_div_iff₀ (by linarith)).mpr (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hgr)
    calc
      _ ≤ μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} := measure_mono (fun x hx => hx.trans hrad)
      _ ≤ ENNReal.ofReal (H*(1/(2:ℝ)^g)^s) := hdyadic g hg hcut c
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith [hrg]) hs) hH)
  · apply ((measure_mono (subset_univ _)).trans hmass).trans
    apply ENNReal.ofReal_le_ofReal
    have hp : 1 ≤ (4*a*r)^s := Real.one_le_rpow (by linarith) hs
    nlinarith

theorem gaussian_point_unnormalized_frostman
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space m) (N : ℕ)
    (r : Fin (N+1) → ℝ) (TP : Fin (N+1) → ℝ≥0∞)
    (hr : ∀ g, r g = (1/(2:ℝ)^g.val)/2)
    {K a P f : ℝ} (hK : 0 ≤ K) (ha : 1 ≤ a) (hP : 0 ≤ P) (hf : 0 ≤ f)
    (hbound : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ K*‖gaussianRowMap A x‖)
    (haK : 4+2*K*(h:ℝ) ≤ a)
    (hTP : ∀ g, TP g ≤ ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^f))
    (hmass : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z))) univ ≤ ENNReal.ofReal P) :
    ∀ c s, 1/(2:ℝ)^N ≤ s →
      ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
        (gaussianPointGood μ (1/(2:ℝ)^N) r TP (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s} ≤
        ENNReal.ofReal (P*(4*a*s)^f) := by
  apply truncated_dyadic_ball_bound_mass _ _ N ha hP hf hmass
  intro g hg hcut c
  let j : Fin (N+1) := ⟨g,by omega⟩
  have hδ : 1/(2:ℝ)^N ≤ (1/(2:ℝ)^g)/(2*a) :=
    (le_div_iff₀ (by linarith)).mpr (by simpa only [mul_comm,mul_left_comm,mul_assoc] using hcut)
  have hb := gaussian_scaled_point_test μ A z e (1/(2:ℝ)^N) r TP j hK
    (by norm_num : (0:ℝ) < 1) (by linarith) (by positivity) hbound
    (by simpa only [mul_one] using haK) hδ (hr j) c
  simp only [inv_one,one_smul] at hb
  exact hb.trans (hTP j)

theorem gaussian_point_endpoint_ball
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (A : Fin h → Space d) (z : Space h)
    (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 3) (N : ℕ)
    {P s a κ : ℝ} (hP : 0 ≤ P) (hs : 0 ≤ s) (ha : 1 ≤ a)
    (haK : 4+4*(h:ℝ) ≤ a)
    (hprojection : ∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖)
    (hmass : ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
        (fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)) (A,z))) univ ≤ ENNReal.ofReal P)
    (hcoef : P*(4*a)^s ≤ (1/(2:ℝ)^N)^(-κ)) :
    ∀ p : Space 3, ((gaussianPointSliceMeasure μ A z (1/(2:ℝ)^N)).restrict
      (gaussianPointGood μ (1/(2:ℝ)^N) (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
        (fun g => ENNReal.ofReal (P*(1/(2:ℝ)^g.val)^s)) (A,z)))
      {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p < 6*(1/(2:ℝ)^N)} ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^(-κ)*(6*(1/(2:ℝ)^N))^s) := by
  intro p
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hh := gaussian_point_unnormalized_frostman μ A z e N _ _ (fun _ => rfl)
    (by norm_num) ha hP hs hprojection (by nlinarith [haK]) (fun _ => le_rfl)
    hmass p (6*δ) (by linarith)
  have hsub : {x : Space d | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p < 6*δ} ⊆
      {x : Space d | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p ≤ 6*δ} := by
    intro x hx
    change dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) p ≤ 6*δ
    exact le_of_lt hx
  apply ((measure_mono hsub).trans hh).trans
  apply ENNReal.ofReal_le_ofReal
  rw [show 4*a*(6*δ) = (4*a)*(6*δ) by ring,Real.mul_rpow (by linarith) (by positivity)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) s)

end Falconer

end OAI
