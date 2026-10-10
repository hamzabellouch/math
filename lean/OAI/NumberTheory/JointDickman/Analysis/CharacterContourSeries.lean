import OAI.NumberTheory.JointDickman.Analysis.SquarefreeCharacterFactorization
import OAI.NumberTheory.JointDickman.Analysis.CharacterRectangleLog
import OAI.NumberTheory.JointDickman.Analysis.AnalyticLogUniqueness
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerBound

namespace OAI

/-! # Identifying the continued character series on the Perron line -/
namespace JointDickman
open Set

noncomputable def characterContourSeries {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  squarefreeCharacterAnalyticFactor χ z s * Complex.exp ((z:ℂ)*f s)

theorem character_rectangle_log_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T))
    (hf0 : f (3/2) = primeCharacterLog χ (3/2))
    (he : ∀ s ∈ zetaOpenRectangle δ T, Complex.exp (f s) = χ.LFunction s) :
    EqOn f (primeCharacterLog χ) (zetaOpenRectangle 0 T) := by
  have hsub : zetaOpenRectangle 0 T ⊆ zetaOpenRectangle δ T := by
    intro s hs
    have hh : 1 < s.re := by simpa using hs.1.1
    exact ⟨⟨by linarith, hs.1.2⟩, hs.2⟩
  have hx : (3/2:ℂ) ∈ zetaOpenRectangle 0 T := by
    constructor <;> constructor <;> norm_num <;> linarith
  apply analytic_log_unique (zetaOpenRectangle_isOpen 0 T)
    (zetaOpenRectangle_convex 0 T).isPreconnected (hf.mono hsub)
    (fun s hs => primeCharacterLog_analyticOnNhd χ s (by simpa using hs.1.1))
    (fun s hs => (he s (hsub hs)).trans (primeCharacterLog_exp χ
      (by simpa using hs.1.1)).symm) hx hf0

theorem characterContourSeries_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z δ T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T))
    (hf0 : f (3/2) = primeCharacterLog χ (3/2))
    (he : ∀ s ∈ zetaOpenRectangle δ T, Complex.exp (f s) = χ.LFunction s)
    {s : ℂ} (hs : s ∈ zetaOpenRectangle 0 T) :
    characterContourSeries χ z f s =
      LSeries (fun n => (squarefreeWeight z n:ℂ)*χ (n:ZMod q)) s := by
  rw [characterContourSeries, character_rectangle_log_eq χ hδ hT hf hf0 he hs]
  exact (squarefreeCharacterDirichletSeries_factorization χ hz hz1 (by simpa using hs.1.1)).symm

theorem characterContourSeries_analyticOnNhd {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ T : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : δ ≤ 1/4)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T)) :
    AnalyticOnNhd ℂ (characterContourSeries χ z f) (zetaOpenRectangle δ T) := by
  intro s hs
  have hre : 1/2 < s.re := by have hh : 1-δ < s.re := hs.1.1; linarith
  exact (squarefreeCharacterAnalyticFactor_analyticOnNhd χ hz hz1 s hre).mul
    ((analyticAt_const.mul (hf s hs)).cexp)

theorem characterContourSeries_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z σ C : ℝ} {f : ℂ → ℂ}
    (hG : ∀ s : ℂ, σ ≤ s.re → ‖squarefreeCharacterAnalyticFactor χ z s‖ ≤ C)
    {s : ℂ} (hs : σ ≤ s.re) (he : Complex.exp (f s) = χ.LFunction s) :
    ‖characterContourSeries χ z f s‖ ≤ C * ‖χ.LFunction s‖^z := by
  rw [characterContourSeries, norm_mul, norm_exp_real_mul_of_exp_eq z he]
  exact mul_le_mul_of_nonneg_right (hG s hs) (Real.rpow_nonneg (norm_nonneg _) _)

end JointDickman

end OAI
