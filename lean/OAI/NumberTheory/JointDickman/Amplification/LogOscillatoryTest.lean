import OAI.NumberTheory.JointDickman.Amplification.OscillatoryTests
import OAI.NumberTheory.JointDickman.Amplification.CellAverageOscillation
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # Oscillation of the actual major-arc tests in logarithmic coordinates -/

namespace JointDickman
open MeasureTheory

noncomputable def logOscillatoryTest (w : ℝ → ℝ) (B N ω : ℝ) (x : ℝ) : ℂ :=
  oscillatoryTest w ω (Real.exp (B*x)/N)

noncomputable def logOscillatoryTestDeriv (w w' : ℝ → ℝ) (B N ω : ℝ) (x : ℝ) : ℂ :=
  oscillatoryTestDeriv w w' ω (Real.exp (B*x)/N) * (B*(Real.exp (B*x)/N) : ℝ)

theorem hasDerivAt_logOscillatoryTest {w w' : ℝ → ℝ} {B N ω x : ℝ}
    (hw : HasDerivAt w (w' (Real.exp (B*x)/N)) (Real.exp (B*x)/N)) :
    HasDerivAt (logOscillatoryTest w B N ω)
      (logOscillatoryTestDeriv w w' B N ω x) x := by
  have hz := (((hasDerivAt_id x).const_mul B).exp).div_const N
  have hh := (hasDerivAt_oscillatoryTest (ξ := ω) hw).scomp x hz
  convert hh using 1
  · rfl
  change oscillatoryTestDeriv w w' ω (Real.exp (B*x)/N) *
    (B*(Real.exp (B*x)/N) : ℝ) = _
  simp only [oscillatoryTestDeriv,Complex.real_smul,id_eq,mul_one]
  push_cast
  ring

theorem logOscillatoryTest_norm (w : ℝ → ℝ) (B N ω x : ℝ) :
    ‖logOscillatoryTest w B N ω x‖ = |w (Real.exp (B*x)/N)| :=
  oscillatoryTest_norm w ω _

theorem logOscillatoryTest_deriv_bound {w w' : ℝ → ℝ} {B N ω x b M D : ℝ}
    (hB : 0 ≤ B) (hN : 0 < N) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hb : Real.exp (B*x)/N ≤ b)
    (hw : |w (Real.exp (B*x)/N)| ≤ M)
    (hw' : |w' (Real.exp (B*x)/N)| ≤ D) :
    ‖logOscillatoryTestDeriv w w' B N ω x‖ ≤
      (D+2*Real.pi*|ω| * M)*(B*b) := by
  have hz : 0 ≤ Real.exp (B*x)/N := (div_pos (Real.exp_pos _) hN).le
  have he := (oscillatoryTestDeriv_norm_le w w' ω (Real.exp (B*x)/N)).trans
    (add_le_add hw' (mul_le_mul_of_nonneg_left hw (by positivity)))
  rw [logOscillatoryTestDeriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hB hz)]
  exact mul_le_mul he (mul_le_mul_of_nonneg_left hb hB) (mul_nonneg hB hz) (by positivity)

theorem logOscillatoryTest_lipschitz {w w' : ℝ → ℝ} {B N ω a b R M D : ℝ}
    (hB : 0 ≤ B) (hN : 0 < N) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hw : ∀ t, HasDerivAt w (w' t) t)
    (hbound : ∀ x ∈ Set.Icc a b, Real.exp (B*x)/N ≤ R)
    (hwbound : ∀ t, |w t| ≤ M) (hw'bound : ∀ t, |w' t| ≤ D)
    {u v : ℝ} (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b) :
    ‖logOscillatoryTest w B N ω u-logOscillatoryTest w B N ω v‖ ≤
      ((D+2*Real.pi*|ω| * M)*(B*R))*|u-v| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_hx : x ∈ Set.Icc a b) => (hasDerivAt_logOscillatoryTest (ω := ω) (hw _)).hasDerivWithinAt)
    (fun x hx => logOscillatoryTest_deriv_bound (ω := ω) hB hN hM hD (hbound x hx)
      (hwbound _) (hw'bound _)) (convex_Icc a b) hv hu
  simpa only [Real.norm_eq_abs] using hh

/-- Exact major-arc phase after the logarithmic change of variables. -/
theorem logOscillatoryTest_majorArc (w : ℝ → ℝ) {B N j X k ξ : ℝ}
    (hB : B ≠ 0) (hN : N ≠ 0) (hk : 0 < k) :
    logOscillatoryTest w B N (ξ*N/(j*X)) (Real.log k/B) =
      (w (k/N) : ℂ)*additivePhase (ξ*k/(j*X)) := by
  unfold logOscillatoryTest oscillatoryTest
  rw [mul_div_cancel₀ _ hB,Real.exp_log hk]
  congr 2
  field_simp

end JointDickman

end OAI
