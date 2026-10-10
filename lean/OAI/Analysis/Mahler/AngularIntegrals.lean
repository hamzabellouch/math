import OAI.Analysis.Mahler.AngularGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! Angular integral and sine estimate. -/

noncomputable section
open Complex Set MeasureTheory
open scoped Topology
namespace MahlerConformal

lemma continuous_B (r : ℝ) : Continuous (B r) := by
  unfold B
  fun_prop

/-- Fundamental theorem of calculus for the actual angular derivative. -/
theorem integral_B {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (a b : ℝ) :
    (∫ θ in a..b, B r θ) = Q r a - Q r b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ => -Q r θ) (f' := B r)
    (fun θ (_ : θ ∈ uIcc a b) => by
      convert (hasDerivAt_Q hr hr1 θ).neg using 1
      simp only [neg_neg])
    (show IntervalIntegrable (B r) volume a b from (continuous_B r).intervalIntegrable a b)
  simpa only [neg_neg, neg_sub_neg] using h

/-- The normalization identity for the angular integral. -/
theorem integral_B_semicircle {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (∫ θ in (0 : ℝ)..Real.pi, B r θ) = 2*(F (r : ℂ)).re := by
  rw [integral_B hr hr1, Q_zero, Q_pi]
  ring

lemma arctan_le_self_nonneg {v : ℝ} (hv : 0 ≤ v) : Real.arctan v ≤ v := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr hv) (Real.arctan_lt_pi_div_two v)

lemma B_le_linear {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    B r θ ≤ (8*r/(Real.pi^2*(1-r^2))) * θ := by
  have hd : 0 < 1-r^2 := by nlinarith
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hv : 0 ≤ 2*r*Real.sin θ/(1-r^2) := by positivity
  calc
    B r θ ≤ 4/Real.pi^2 * (2*r*Real.sin θ/(1-r^2)) :=
      mul_le_mul_of_nonneg_left (arctan_le_self_nonneg hv) (by positivity)
    _ ≤ 4/Real.pi^2 * (2*r*θ/(1-r^2)) := by
      gcongr
      exact Real.sin_le hθ.1
    _ = _ := by field_simp; ring

/-- The quadratic angular estimate, with C=4/pi². -/
theorem Q_drop_le_quadratic {r d : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hd : d ∈ Icc 0 Real.pi) :
    (F (r : ℂ)).re - Q r d ≤ 4*r*d^2/(Real.pi^2*(1-r^2)) := by
  let c : ℝ := 8*r/(Real.pi^2*(1-r^2))
  have hi : (∫ θ in (0 : ℝ)..d, c*θ) = c*d^2/2 := by
    have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => c*θ^2/2) (f' := fun θ => c*θ)
      (fun θ (_ : θ ∈ uIcc 0 d) => by
        convert ((hasDerivAt_pow 2 θ).const_mul c).div_const 2 using 1 ; first | rfl | ring)
      (show IntervalIntegrable (fun θ => c*θ) volume 0 d from
        (continuous_const.mul continuous_id).intervalIntegrable 0 d)
    simpa using ht
  have hle := intervalIntegral.integral_mono_on (μ := volume) hd.1
    ((continuous_B r).intervalIntegrable 0 d)
    ((continuous_const.mul continuous_id : Continuous (fun θ : ℝ => c*θ)).intervalIntegrable 0 d)
    (fun θ (hθ : θ ∈ Icc 0 d) => B_le_linear hr hr1 ⟨hθ.1, hθ.2.trans hd.2⟩)
  simp only [Pi.mul_apply] at hle
  rw [integral_B hr hr1, Q_zero, hi] at hle
  change (F (r : ℂ)).re - Q r d ≤ c*d^2/2 at hle
  have he : c*d^2/2 = 4*r*d^2/(Real.pi^2*(1-r^2)) := by dsimp [c]; ring
  rwa [he] at hle

/-- The reflected angle gives the sine estimate with the explicit
absolute constant c=1. This theorem is about F itself and assumes no inverse map. -/
theorem sine_bound {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) :
    Real.sqrt ((1-r^2)*((F (r : ℂ)).re - |Q r θ|)/r) ≤ Real.sin θ := by
  let d := min θ (Real.pi-θ)
  have hd0 : 0 ≤ d := le_min hθ.1 (sub_nonneg.mpr hθ.2)
  have hdπ : d ≤ Real.pi/2 := by
    dsimp [d]
    by_cases h : θ ≤ Real.pi/2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  have hd : d ∈ Icc 0 Real.pi := ⟨hd0, hdπ.trans (by linarith [Real.pi_pos])⟩
  have hsin : Real.sin d = Real.sin θ := by
    dsimp [d]
    rcases le_total θ (Real.pi-θ) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Real.sin_pi_sub]
  have hdrop := Q_drop_le_quadratic hr hr1 hd
  rw [Q_min_angle hr hr1 hθ] at hdrop
  have hden : 0 < Real.pi^2*(1-r^2) := mul_pos (sq_pos_of_pos Real.pi_pos) (by nlinarith)
  have hsqrt : Real.sqrt ((1-r^2)*((F (r : ℂ)).re - |Q r θ|)/r) ≤ 2/Real.pi*d := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hh := (le_div_iff₀ hden).mp hdrop
    apply (div_le_iff₀ hr).mpr
    have he : (2/Real.pi*d)^2*r * Real.pi^2 = 4*r*d^2 := by field_simp; ring
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos Real.pi_pos)).mp
    nlinarith
  exact hsqrt.trans (hsin ▸ Real.mul_le_sin hd0 hdπ)

end MahlerConformal

end

end OAI
