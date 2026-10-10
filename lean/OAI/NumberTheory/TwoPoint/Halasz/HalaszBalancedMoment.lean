import OAI.NumberTheory.TwoPoint.Halasz.HalaszMomentInterpolation

namespace OAI

/-! Equal total moments bound each mixed moment. This will be applied
to the ordinary polynomial sum and its doubled-frequency version. -/
namespace TwoPointCorrelations

open MeasureTheory

theorem halasz_equal_moment_bound {k a b : ℕ} (ha : 0<a) (hb : 0<b)
    (F G : (Fin k → AddCircle (1:ℝ)) → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    (he : (∫ x, ‖F x‖^(a+b) ∂halaszVinogradovHaar k) =
      ∫ x, ‖G x‖^(a+b) ∂halaszVinogradovHaar k) :
    (∫ x, ‖F x‖^a * ‖G x‖^b ∂halaszVinogradovHaar k) ≤
      ∫ x, ‖F x‖^(a+b) ∂halaszVinogradovHaar k := by
  let θ : ℝ := a/(a+b)
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha
  have hb0 : (0:ℝ)<b := by exact_mod_cast hb
  have hab0 : (0:ℝ)<a+b := by positivity
  have hθ0 : 0<θ := div_pos ha0 hab0
  have hθ1 : θ<1 := (div_lt_one hab0).mpr (by linarith)
  have hpowF (x : Fin k → AddCircle (1:ℝ)) : (‖F x‖^(a+b))^θ=‖F x‖^a := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    have hbal : ((a+b:ℕ):ℝ)*θ=a := by
      dsimp [θ]
      push_cast
      field_simp
    rw [hbal,Real.rpow_natCast]
  have hpowG (x : Fin k → AddCircle (1:ℝ)) : (‖G x‖^(a+b))^(1-θ)=‖G x‖^b := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _)]
    have hbal : ((a+b:ℕ):ℝ)*(1-θ)=b := by
      dsimp [θ]
      push_cast
      field_simp
      ring
    rw [hbal,Real.rpow_natCast]
  have h := halasz_torus_geometric_mean (fun x => ‖F x‖^(a+b))
    (fun x => ‖G x‖^(a+b)) (hF.norm.pow _) (hG.norm.pow _)
    (fun _ => by positivity) (fun _ => by positivity) hθ0 hθ1
  simp_rw [hpowF,hpowG] at h
  rw [← he] at h
  have hJ : 0≤∫ x, ‖F x‖^(a+b) ∂halaszVinogradovHaar k :=
    integral_nonneg (fun _ => by positivity)
  exact h.trans (by simpa only [add_sub_cancel,Real.rpow_one] using
    Real.le_rpow_add hJ θ (1-θ))

end TwoPointCorrelations

end OAI
