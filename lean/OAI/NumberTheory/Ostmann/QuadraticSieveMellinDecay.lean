import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDeriv

namespace OAI

namespace Ostmann
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap

theorem schwartz_mellin_im_mul_norm_le (ρ : 𝓢(ℝ, ℂ)) {s : ℂ} (hs : 0 < s.re) :
    |s.im| * ‖mellin (ρ : ℝ → ℂ) s‖ ≤
      ‖mellin (SchwartzMap.derivCLM ℂ ℂ ρ : ℝ → ℂ) (s + 1)‖ := by
  calc
    |s.im| * ‖mellin (ρ : ℝ → ℂ) s‖ ≤ ‖s‖ * ‖mellin (ρ : ℝ → ℂ) s‖ :=
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) (norm_nonneg _)
    _ = _ := by rw [schwartz_mellin_deriv ρ hs, norm_mul, norm_neg]

theorem schwartz_mellin_weighted_bound (A : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1 + |t|) ^ A * ‖mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)‖ ≤ C := by
  induction A generalizing ρ σ with
  | zero =>
      refine ⟨mellinVerticalBound ρ σ + 1, by linarith [mellinVerticalBound_nonneg ρ σ], ?_⟩
      intro t
      have h := norm_mellin_le_verticalBound ρ (σ + t * Complex.I)
      simpa using h.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  | succ A ih =>
      obtain ⟨C, hC, hCb⟩ := ih ρ σ hσ
      obtain ⟨D, hD, hDb⟩ := ih (SchwartzMap.derivCLM ℂ ℂ ρ) (σ + 1) (by linarith)
      refine ⟨C + D, add_pos hC hD, ?_⟩
      intro t
      have hr := schwartz_mellin_im_mul_norm_le ρ
        (s := σ + t * Complex.I) (by simpa using hσ)
      have heq : (σ : ℂ) + t * Complex.I + 1 = (σ + 1 : ℝ) + t * Complex.I := by
        push_cast
        ring
      rw [heq] at hr
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hr
      calc
        (1 + |t|) ^ (A + 1) * ‖mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)‖ =
            (1 + |t|) ^ A * ‖mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)‖ +
            (1 + |t|) ^ A * (|t| * ‖mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)‖) := by
          rw [pow_succ]
          ring
        _ ≤ C + D := add_le_add (hCb t)
          ((mul_le_mul_of_nonneg_left hr (by positivity)).trans (hDb t))

theorem schwartz_mellin_vertical_decay (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ) (hσ : 0 < σ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖mellin (ρ : ℝ → ℂ) (σ + t * Complex.I)‖ ≤ C * (1 + |t|) ^ (-(A : ℤ)) := by
  obtain ⟨C, hC, hb⟩ := schwartz_mellin_weighted_bound A ρ σ hσ
  refine ⟨C, hC, ?_⟩
  intro t
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + |t|) ^ A)).mpr
  simpa only [mul_comm] using hb t

end Ostmann

end OAI
