import OAI.MeasureTheory.Falconer.Angular.CapCoordinates
import OAI.MeasureTheory.Falconer.Estimates.RotatedNonstationary

namespace OAI

/-!
# Coordinate support inherited from a geometric sphere cap

The two coordinate bounds are consequences of the actual cap support.
They do not impose additional localization assumptions on the amplitude.
-/

namespace Falconer
open Set

theorem chartPole_inner {n : ℕ} (v : Space (n+2)) :
    inner ℝ (chartPole n) v = v 0 := by
  rw [PiLp.inner_apply,Fin.sum_univ_succ]
  simp [chartPole,coordinateJoin_eq]

theorem transverse_coordinate_bounds {n : ℕ} (y : Space n) (u : ℝ) :
    ‖y‖ ≤ ‖transverseLift y+u•chartAxis n‖ ∧
      |u| ≤ ‖transverseLift y+u•chartAxis n‖ := by
  have he : ‖transverseLift y+u•chartAxis n‖^2 = ‖y‖^2+u^2 := by
    rw [norm_add_sq_real,real_inner_smul_right,transverseLift_inner_axis,
      mul_zero,mul_zero,add_zero,transverseLift_norm,norm_smul,
      chartAxis_norm,mul_one,Real.norm_eq_abs,sq_abs]
  constructor
  · nlinarith [norm_nonneg y,norm_nonneg (transverseLift y+u•chartAxis n),sq_nonneg u]
  · nlinarith [abs_nonneg u,sq_abs u,norm_nonneg (transverseLift y+u•chartAxis n),
      sq_nonneg ‖y‖]

theorem rotated_cap_coordinate_bounds {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ‖(sphereMap e (gnomonicChart (coordinateJoin y u)) : Space (n+2)) -
      e (chartPole n)‖ ≤ δ) :
    ‖transverseLift y+u•chartAxis n‖ ≤ 2*δ ∧ ‖y‖ ≤ 2*δ ∧ |u| ≤ 2*δ := by
  have hc : ‖(gnomonicChart (coordinateJoin y u) : Space (n+2))-chartPole n‖ ≤ δ := by
    change ‖e (gnomonicChart (coordinateJoin y u)) - e (chartPole n)‖ ≤ δ at hcap
    rwa [← e.map_sub,e.norm_map] at hcap
  have ho : inner ℝ (chartPole n) (transverseLift y+u•chartAxis n) = 0 := by
    rw [inner_add_right,real_inner_smul_right,chartPole_inner_transverse,
      chartPole_inner_axis,mul_zero,add_zero]
  have hnear : ‖‖chartPole n+(transverseLift y+u•chartAxis n)‖⁻¹ •
      (chartPole n+(transverseLift y+u•chartAxis n))-chartPole n‖ ≤ δ := by
    simpa only [gnomonicChart_coordinateJoin,normalizedLine,add_assoc] using hc
  have hh := small_cap_chart_displacement (chartPole_norm n) ho hδ hsmall hnear
  exact ⟨hh,(transverse_coordinate_bounds y u).1.trans hh,
    (transverse_coordinate_bounds y u).2.trans hh⟩

theorem cap_mem_rotated_north {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (z : Sphere (n+2))
    {δ : ℝ} (hsmall : δ ≤ 1/2)
    (hcap : ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ) :
    sphereMap e.symm z ∈ northHemisphere (n+1) := by
  have hi := abs_real_inner_le_norm (e (chartPole n)) ((z : Space (n+2))-e (chartPole n))
  rw [e.norm_map,chartPole_norm,one_mul,inner_sub_right,
    real_inner_self_eq_norm_sq,e.norm_map,chartPole_norm,one_pow] at hi
  have hp : 0 < inner ℝ (e (chartPole n)) (z : Space (n+2)) := by
    have hh := (neg_le_abs (inner ℝ (e (chartPole n)) (z : Space (n+2))-1)).trans
      (hi.trans hcap)
    linarith
  change 0 < (e.symm (z : Space (n+2))) 0
  rw [← chartPole_inner,← inner_isometry_pullback]
  exact hp

theorem cap_amplitude_chart_support {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (b : Sphere (n+2) → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ∀ z, b z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ) :
    (∀ z, sphereMap e.symm z ∉ northHemisphere (n+1) → b z = 0) ∧
    (∀ y : Space n, 1 < ‖y‖ → ∀ u, rotatedChartAmplitude e b y u = 0) ∧
    (∀ y : Space n, tsupport (rotatedChartAmplitude e b y) ⊆ Icc (-1 : ℝ) 1) := by
  have hcoord (y : Space n) (u : ℝ) (h : rotatedChartAmplitude e b y u ≠ 0) :
      ‖y‖ ≤ 1 ∧ |u| ≤ 1 := by
    have hc := rotated_cap_coordinate_bounds e y u hδ hsmall
      (hcap (sphereMap e (gnomonicChart (coordinateJoin y u))) h)
    exact ⟨hc.2.1.trans (by linarith),hc.2.2.trans (by linarith)⟩
  refine ⟨?_,?_,?_⟩
  · intro z hz
    by_contra h
    exact hz (cap_mem_rotated_north e z hsmall (hcap z h))
  · intro y hy u
    by_contra h
    exact (not_le_of_gt hy) (hcoord y u h).1
  · intro y
    apply closure_minimal _ isClosed_Icc
    intro u hu
    exact abs_le.mp (hcoord y u hu).2

theorem cap_amplitude_chart_radius {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (b : Sphere (n+2) → ℂ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/2)
    (hcap : ∀ z, b z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ)
    (y : Space n) :
    ∀ u ∈ tsupport (rotatedChartAmplitude e b y),
      ‖transverseLift y+u•chartAxis n‖ ≤ 2*δ := by
  have hs : tsupport (rotatedChartAmplitude e b y) ⊆
      {u : ℝ | ‖transverseLift y+u•chartAxis n‖ ≤ 2*δ} := by
    apply closure_minimal
    · intro u hu
      exact (rotated_cap_coordinate_bounds e y u hδ hsmall
        (hcap (sphereMap e (gnomonicChart (coordinateJoin y u))) hu)).1
    · exact isClosed_le (by fun_prop) continuous_const
  exact fun u hu => hs hu

end Falconer

end OAI
