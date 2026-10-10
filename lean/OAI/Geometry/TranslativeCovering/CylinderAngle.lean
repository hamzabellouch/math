import OAI.Geometry.TranslativeCovering.CylinderVolume

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderAngle
open Set MeasureTheory Metric InnerProductGeometry CylinderVolume ConeStretch
open scoped ENNReal

lemma ordinary_perp_bound {n : ℕ} (u x : Space n) (hu : ‖u‖ = 1) (hx : x ≠ 0)
    {L ξ : ℝ} (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hxL : ‖x‖ ≤ L)
    (hang : InnerProductGeometry.angle u x ≤ ξ) :
    ‖x‖^2-(inner ℝ u x)^2 ≤ (L*ξ)^2 := by
  let A := InnerProductGeometry.angle u x
  have hA0 : 0 ≤ A := angle_nonneg _ _
  have hApi : A ≤ Real.pi := angle_le_pi _ _
  have hs0 : 0 ≤ Real.sin A := Real.sin_nonneg_of_nonneg_of_le_pi hA0 hApi
  have hsξ : Real.sin A ≤ ξ := (Real.sin_le hA0).trans hang
  have hc : Real.cos A*‖x‖ = inner ℝ u x := by
    dsimp [A]
    rw [cos_angle,hu,one_mul,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]
  have hid : ‖x‖^2-(inner ℝ u x)^2 = ‖x‖^2*(Real.sin A)^2 := by
    rw [← hc]
    have hh := congrArg (fun t : ℝ => ‖x‖^2*t) (Real.sin_sq_add_cos_sq A)
    nlinarith [hh]
  rw [hid,mul_pow]
  exact mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hL).mpr hxL)
    ((sq_le_sq₀ hs0 hξ).mpr hsξ) (sq_nonneg _) (sq_nonneg _)

lemma projective_perp_bound {n : ℕ} (u x : Space n) (hu : ‖u‖ = 1) (hx : x ≠ 0)
    {L ξ : ℝ} (hL : 0 ≤ L) (hξ : 0 ≤ ξ) (hxL : ‖x‖ ≤ L)
    (hang : ProjectiveCaps.angle u x ≤ ξ) :
    ‖x‖^2-(inner ℝ u x)^2 ≤ (L*ξ)^2 := by
  rcases (min_le_iff.mp hang) with h | h
  · exact ordinary_perp_bound u x hu hx hL hξ hxL h
  · simpa only [norm_neg,inner_neg_right,neg_sq] using
      ordinary_perp_bound u (-x) hu (neg_ne_zero.mpr hx) hL hξ
        (by simpa only [norm_neg] using hxL) h

lemma angular_section_volume {n : ℕ} [NeZero n] (u : Space n) (hu : ‖u‖ = 1)
    (q : Space n) {D L ξ : ℝ} (hD : 0 < D) (hL : 0 < L) (hξ : 0 < ξ) :
    volume {x : Space n | ‖x‖ ≤ D ∧ x-q ≠ 0 ∧ ‖x-q‖ ≤ L ∧
      ProjectiveCaps.angle u (x-q) ≤ ξ} ≤
    ENNReal.ofReal (3*((n:ℝ)+1)*(L*ξ/D)^(n-1))*
      volume (closedBall (0 : Space n) D) := by
  apply (measure_mono (μ := volume) (show _ ⊆
    {x : Space n | ‖x‖ ≤ D ∧ ‖x-q‖^2-(inner ℝ u (x-q))^2 ≤ (L*ξ)^2} from ?_)).trans
    (affine_cylinder_volume u hu q hD (mul_pos hL hξ))
  intro x hx
  exact ⟨hx.1,projective_perp_bound u (x-q) hu hx.2.1 hL.le hξ.le hx.2.2.1 hx.2.2.2⟩

lemma measurable_angle {n : ℕ} : Measurable (fun p : Space n × Space n => ProjectiveCaps.angle p.1 p.2) := by
  unfold ProjectiveCaps.angle InnerProductGeometry.angle
  fun_prop

end CylinderAngle

end OAI
