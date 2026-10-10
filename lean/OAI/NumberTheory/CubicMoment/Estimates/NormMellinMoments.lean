import OAI.NumberTheory.CubicMoment.Estimates.NormDenominatorMellin

namespace OAI

/-! Integrated decay with polynomial Mellin-height weights. This controls
truncated shifts in the dispersion kernel. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominatorMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀,hC₀,hc₀⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') 0 0 (2*A)
  obtain ⟨C₁,hC₁,hc₁⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') (B+k) 0 (2*A)
  refine ⟨D*(C₀+C₁)+1,by positivity,?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have h₀ := hc₀ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  have h₁ := hc₁ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h₀ h₁
  have hb : (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+Real.sqrt ρ)^(2*A) * (D *
          (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
           SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
        mul_le_mul hs h (integral_nonneg (fun t => by positivity)) (by positivity)
      _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
        (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) hD
  linarith

lemma mellin_window_majorant {g : ℝ → ℝ} {B C T : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : 0 < T) (k : ℕ) (hg : ∀ t, g t ≤ C) (hsmall : ∀ t, ‖t‖ ≤ T → g t ≤ B) (t : ℝ) :
    g t ≤ B+C/T^k*‖t‖^k := by
  by_cases ht : ‖t‖ ≤ T
  · exact (hsmall t ht).trans (le_add_of_nonneg_right (by positivity))
  · have hp : T^k ≤ ‖t‖^k := pow_le_pow_left₀ hT.le (le_of_not_ge ht) _
    have hratio : 1 ≤ ‖t‖^k/T^k := (le_div_iff₀ (pow_pos hT _)).mpr (by simpa using hp)
    calc
      _ ≤ C := hg t
      _ ≤ C*(‖t‖^k/T^k) := le_mul_of_one_le_right hC hratio
      _ = C/T^k*‖t‖^k := by ring
      _ ≤ B+C/T^k*‖t‖^k := le_add_of_nonneg_left hB


theorem integral_schwartz_window (f : 𝓢(ℝ,ℂ)) {g : ℝ → ℝ}
    (hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t) {B C T : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hT : 0 < T) (k : ℕ)
    (hgC : ∀ t, g t ≤ C) (hsmall : ∀ t, ‖t‖ ≤ T → g t ≤ B) :
    (∫ t : ℝ, ‖f t‖*g t) ≤
      B*(∫ t : ℝ, ‖f t‖)+C/T^k*(∫ t : ℝ, ‖t‖^k*‖f t‖) := by
  have hi : Integrable (fun t : ℝ => ‖f t‖*g t) := f.integrable.norm.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hg0 t)]
      exact hgC t))
  have hw := f.integrable_pow_mul volume k
  have hm := (f.integrable.norm.const_mul B).add (hw.const_mul (C/T^k))
  calc
    _ ≤ ∫ t : ℝ, B*‖f t‖+(C/T^k)*(‖t‖^k*‖f t‖) := by
      apply integral_mono hi hm
      intro t
      calc
        _ ≤ ‖f t‖*(B+C/T^k*‖t‖^k) :=
          mul_le_mul_of_nonneg_left (mellin_window_majorant hB hC hT k hgC hsmall t) (_root_.norm_nonneg _)
        _ = _ := by dsimp only [Pi.add_apply]; ring
    _ = _ := by rw [integral_add (f.integrable.norm.const_mul B) (hw.const_mul (C/T^k)),
      integral_const_mul,integral_const_mul]

end CubicFirstMoment

end

end OAI
