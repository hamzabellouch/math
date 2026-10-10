import OAI.NumberTheory.JointDickman.Analysis.CharacterZeroFreeStrip
import OAI.NumberTheory.JointDickman.Analysis.ZetaRectangleLog

namespace OAI

/-! # Analytic logarithms on the character zero-free rectangles -/
namespace JointDickman
open Set

noncomputable def characterContourWidth (A ε : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  A * (((q:ℝ)+2)*(T+2))^(-ε)

private theorem exists_analytic_log_with_value {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {x₀ v : ℂ} (hx₀ : x₀ ∈ U)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) (hne : ∀ x ∈ U, g x ≠ 0)
    (hv : Complex.exp v = g x₀) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ f x₀ = v ∧
      ∀ x ∈ U, Complex.exp (f x) = g x := by
  obtain ⟨f,hf,he⟩ := exists_analytic_log_on hUc hUo hg hne
  refine ⟨fun x => f x-f x₀+v, fun x hx => ((hf x hx).sub analyticAt_const).add
    analyticAt_const, by simp, ?_⟩
  intro x hx
  rw [Complex.exp_add, Complex.exp_sub, he x hx, he x₀ hx₀, hv,
    div_mul_cancel₀ _ (hne x₀ hx₀)]

/-- A normalized logarithm exists uniformly on rectangles with a power-sized width. -/
theorem character_rectangle_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1/4 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ T : ℝ, 0 < T → ∀ v : ℂ, Complex.exp v = χ.LFunction (3/2) →
      ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f (zetaOpenRectangle (characterContourWidth A ε q T) T) ∧
        f (3/2) = v ∧ ∀ s ∈ zetaOpenRectangle (characterContourWidth A ε q T) T,
          Complex.exp (f s) = χ.LFunction s := by
  obtain ⟨A,hA,hA4,hzero⟩ := nonprincipal_character_zero_free_strip hε hε1
  refine ⟨A,hA,hA4,?_⟩
  intro q _ χ hn T hT v hv
  have hw : 0 < characterContourWidth A ε q T := by
    dsimp [characterContourWidth]
    exact mul_pos hA (Real.rpow_pos_of_pos (by positivity) _)
  have hx : (3/2:ℂ) ∈ zetaOpenRectangle (characterContourWidth A ε q T) T := by
    constructor <;> constructor <;> norm_num <;> linarith
  let : ContractibleSpace (zetaOpenRectangle (characterContourWidth A ε q T) T) :=
    (zetaOpenRectangle_convex _ _).contractibleSpace ⟨3/2,hx⟩
  have hsimp : IsSimplyConnected (zetaOpenRectangle (characterContourWidth A ε q T) T) := by
    change SimplyConnectedSpace _
    infer_instance
  apply exists_analytic_log_with_value hsimp (zetaOpenRectangle_isOpen _ _) hx
    (fun s _ => (DirichletCharacter.differentiable_LFunction hn).analyticAt s) ?_ hv
  intro s hs
  have habs : |s.im| ≤ T := abs_le.mpr ⟨hs.2.1.le,hs.2.2.le⟩
  have hpow : (((q:ℝ)+2)*(T+2))^(-ε) ≤ (((q:ℝ)+2)*(|s.im|+2))^(-ε) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
  have hlo : 1-A*(((q:ℝ)+2)*(|s.im|+2))^(-ε) ≤ s.re := by
    have hh := mul_le_mul_of_nonneg_left hpow hA.le
    have hh' := hs.1.1
    change 1-A*(((q:ℝ)+2)*(T+2))^(-ε) < s.re at hh'
    linarith
  have hne := hzero q χ hn s.re s.im hlo hs.1.2.le
  have he : (s.re:ℂ)+Complex.I*(s.im:ℂ) = s := by
    simpa only [mul_comm Complex.I] using Complex.re_add_im s
  rwa [he] at hne

end JointDickman

end OAI
