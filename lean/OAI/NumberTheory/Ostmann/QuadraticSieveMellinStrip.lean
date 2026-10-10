import OAI.NumberTheory.Ostmann.QuadraticSieveMellinDecay

namespace OAI

namespace Ostmann
open MeasureTheory Set
open scoped SchwartzMap

theorem mellinVerticalBound_integrable (ρ : 𝓢(ℝ, ℂ)) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => x ^ (σ - 1) * ‖ρ x‖) (Ioi 0) := by
  have h := (schwartz_mellin_convergent ρ (s := (σ:ℂ)) (by simpa using hσ)).norm
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [norm_smul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]

theorem mellinVerticalBound_le_endpoints (ρ : 𝓢(ℝ, ℂ)) {a b σ : ℝ}
    (ha : 0 < a) (has : a ≤ σ) (hsb : σ ≤ b) :
    mellinVerticalBound ρ σ ≤ mellinVerticalBound ρ a + mellinVerticalBound ρ b := by
  have hb : 0 < b := ha.trans_le (has.trans hsb)
  have hσ : 0 < σ := ha.trans_le has
  rw [mellinVerticalBound,mellinVerticalBound,mellinVerticalBound,
    ← integral_add (mellinVerticalBound_integrable ρ ha) (mellinVerticalBound_integrable ρ hb)]
  apply integral_mono_ae (mellinVerticalBound_integrable ρ hσ)
    ((mellinVerticalBound_integrable ρ ha).add (mellinVerticalBound_integrable ρ hb))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpow : x ^ (σ - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
    by_cases hx1 : 1 ≤ x
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : σ-1 ≤ b-1)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hx.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1)
        (by linarith : a-1 ≤ σ-1)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hx.le _))
  simpa only [Pi.add_apply,add_mul] using mul_le_mul_of_nonneg_right hxpow (norm_nonneg (ρ x))

theorem schwartz_mellin_strip_weighted_bound (A : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ,
      (1 + |t|)^A * ‖mellin (ρ:ℝ→ℂ) (σ + t * Complex.I)‖ ≤ C := by
  induction A generalizing ρ a b with
  | zero =>
    refine ⟨mellinVerticalBound ρ a + mellinVerticalBound ρ b + 1,
      by linarith [mellinVerticalBound_nonneg ρ a,mellinVerticalBound_nonneg ρ b],?_⟩
    intro σ hσ t
    have hn := norm_mellin_le_verticalBound ρ (σ + t * Complex.I)
    have hs := mellinVerticalBound_le_endpoints ρ ha hσ.1 hσ.2
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_im,mul_zero,mul_one,sub_zero,add_zero] at hn
    simpa only [pow_zero,one_mul] using (hn.trans hs).trans
      (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))
  | succ A ih =>
    obtain ⟨C,hC,hCb⟩ := ih ρ a b ha hab
    obtain ⟨D,hD,hDb⟩ := ih (SchwartzMap.derivCLM ℂ ℂ ρ) (a+1) (b+1) (by linarith) (by linarith)
    refine ⟨C+D,add_pos hC hD,?_⟩
    intro σ hσ t
    have hr := schwartz_mellin_im_mul_norm_le ρ
      (s := σ + t * Complex.I) (by simpa using ha.trans_le hσ.1)
    have heq : (σ:ℂ) + t * Complex.I + 1 = (σ+1:ℝ) + t * Complex.I := by push_cast; ring
    rw [heq] at hr
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hr
    calc
      _ = (1+|t|)^A * ‖mellin (ρ:ℝ→ℂ) (σ+t*Complex.I)‖ +
          (1+|t|)^A * (|t| * ‖mellin (ρ:ℝ→ℂ) (σ+t*Complex.I)‖) := by rw [pow_succ]; ring
      _ ≤ C+D := add_le_add (hCb σ hσ t)
        ((mul_le_mul_of_nonneg_left hr (by positivity)).trans
          (hDb (σ+1) ⟨by linarith [hσ.1],by linarith [hσ.2]⟩ t))

theorem schwartz_mellin_strip_decay (ρ : 𝓢(ℝ, ℂ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖mellin (ρ:ℝ→ℂ) (σ + t * Complex.I)‖ ≤ C * (1+|t|)^(-(A:ℤ)) := by
  obtain ⟨C,hC,hb⟩ := schwartz_mellin_strip_weighted_bound A ρ a b ha hab
  refine ⟨C,hC,?_⟩
  intro σ hσ t
  rw [zpow_neg,zpow_natCast,← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0:ℝ) < (1+|t|)^A)).mpr
  simpa only [mul_comm] using hb σ hσ t

end Ostmann

end OAI
