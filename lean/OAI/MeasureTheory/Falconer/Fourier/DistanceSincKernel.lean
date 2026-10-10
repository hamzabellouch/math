import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def distanceSincKernel (u s : ℝ) : ℝ := (Real.sinc (u*s))^2

theorem distanceSincKernel_nonneg (u s : ℝ) : 0 ≤ distanceSincKernel u s := sq_nonneg _

theorem distanceSincKernel_le_one (u s : ℝ) : distanceSincKernel u s ≤ 1 := by
  have h := Real.abs_sinc_le_one (u*s)
  dsimp [distanceSincKernel]
  exact (sq_abs _).symm.trans_le ((pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (by norm_num))

theorem continuous_distanceSincKernel (u : ℝ) : Continuous (distanceSincKernel u) :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem exists_distanceSincKernel : ∃ u : ℝ, 0 < u ∧ 2*u ≤ 1 ∧
    ∀ s : ℝ, |s| ≤ 100 → (1/4:ℝ) ≤ distanceSincKernel u s := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    Real.continuous_sinc.continuousAt (1/2:ℝ) (by norm_num)
  let u := min (δ/201) (1/4:ℝ)
  have hu : 0 < u := lt_min (by positivity) (by norm_num)
  refine ⟨u,hu,by have := min_le_right (δ/201) (1/4:ℝ); dsimp [u]; linarith,?_⟩
  intro s hs
  have hb : |u*s| < δ := by
    rw [abs_mul,abs_of_pos hu]
    have h₁ := mul_le_mul_of_nonneg_left hs hu.le
    have h₂ := min_le_left (δ/201) (1/4:ℝ)
    dsimp [u] at h₁ ⊢
    nlinarith
  have hc := hclose (show dist (u*s) 0 < δ by simpa [Real.dist_eq] using hb)
  rw [Real.dist_eq,Real.sinc_zero] at hc
  have hp : 1/2 < Real.sinc (u*s) := by have := (abs_lt.mp hc).1; linarith
  dsimp [distanceSincKernel]
  nlinarith

theorem interval_exp_eq_sinc (u s : ℝ) :
    (∫ r in -u..u, Complex.exp ((r*s:ℝ)*Complex.I)) =
      ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  by_cases hs : s = 0
  · simp [hs]
    ring
  have h := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => Complex.exp (t*Complex.I)) (a := -u) (b := u) hs
  rw [neg_mul,integral_exp_mul_I_eq_sinc] at h
  rw [h]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

theorem distanceSincKernel_box_square {u : ℝ} (hu : 0 < u) (s : ℝ) :
    distanceSincKernel u s =
      ‖∫ r in -u..u, Complex.exp ((r*s:ℝ)*Complex.I)‖^2 / (2*u)^2 := by
  rw [interval_exp_eq_sinc,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  dsimp [distanceSincKernel]
  field_simp

end PlanarFalconer

end OAI
