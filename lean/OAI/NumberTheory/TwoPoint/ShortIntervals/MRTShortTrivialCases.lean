import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPublishedRate
import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortBoundedLength

namespace OAI

/-! Uniform absorption of the bounded outer scales and small values of
the common arc parameter in the exact published short-interval error. -/

namespace TwoPointCorrelations

lemma mrt_allowed_short_log {H : ℕ} (hH : 10 ≤ H) :
    1 ≤ Real.log (H:ℝ) := by
  have hHr : (10:ℝ) ≤ H := by exact_mod_cast hH
  have hh := Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ (H:ℝ) by linarith [Real.exp_one_lt_three])
  simpa only [Real.log_exp] using hh

lemma mrt_large_parameter_logs {L M : ℝ} {H : ℕ} (hH : 10≤H)
    (hlarge : Real.exp 5 ≤ majorArcParameter L H M) :
    1 ≤ Real.log (H:ℝ) ∧ 1 ≤ Real.log (Real.log (H:ℝ)) := by
  have hLH := mrt_allowed_short_log hH
  have hp : (Real.exp 1)^5 ≤ (Real.log (H:ℝ))^5 := by
    calc
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ majorArcParameter L H M := hlarge
      _ ≤ _ := min_le_left _ _
  have he : Real.exp 1 ≤ Real.log (H:ℝ) :=
    (pow_le_pow_iff_left₀ (Real.exp_pos 1).le (by linarith) (by decide : 5≠0)).mp hp
  refine ⟨hLH,?_⟩
  have hh := Real.log_le_log (Real.exp_pos 1) he
  simpa only [Real.log_exp] using hh

lemma mrt_short_error_nonneg {X H : ℕ} (hH : 10 ≤ H) (hHX : H ≤ X) :
    0 ≤ mrtShortError X H := by
  have hLH := mrt_allowed_short_log hH
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  unfold mrtShortError
  exact add_nonneg
    (div_nonneg (Real.log_nonneg hLH) (by linarith))
    (Real.rpow_nonneg (Real.log_nonneg hX1) _)

/-- A bounded arc parameter forces either a bounded short length or a
bounded exponential-distance parameter. -/
lemma mrt_small_arc_parameter {X H : ℕ} {B M : ℝ}
    (hB : 2 ≤ B) (hH : 10 ≤ H) (hHX : H ≤ X)
    (hsmall : majorArcParameter (Real.log (X:ℝ)) H M ≤ B) :
    (H:ℝ) ≤ Real.exp (B^(125:ℕ)) ∨ Real.exp (M/3) ≤ B := by
  have hLH := mrt_allowed_short_log hH
  have hLX := mrt_allowed_short_log (hH.trans hHX)
  have hHp : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  have hB1 : 1 ≤ B := by linarith
  have hconvert (hlog : Real.log (H:ℝ) ≤ B^(125:ℕ)) :
      (H:ℝ) ≤ Real.exp (B^(125:ℕ)) := by
    calc
      _ = Real.exp (Real.log (H:ℝ)) := (Real.exp_log hHp).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  simp only [majorArcParameter,min_le_iff] at hsmall
  rcases hsmall with hh | hx | hm
  · left
    apply hconvert
    exact (le_self_pow₀ hLH (by decide : 5 ≠ 0)).trans
      (hh.trans (le_self_pow₀ hB1 (by decide : 125 ≠ 0)))
  · left
    have hp : Real.log (X:ℝ) ≤ B^(125:ℕ) := by
      calc
        _ = ((Real.log (X:ℝ))^(1/125:ℝ))^(125:ℕ) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith : 0≤Real.log (X:ℝ))]
          norm_num
        _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hx 125
    apply hconvert
    exact (Real.log_le_log hHp (by exact_mod_cast hHX)).trans hp
  · exact Or.inr hm

lemma mrt_small_exponential_parameter {B M : ℝ} (hB : 2 ≤ B)
    (hM : Real.exp (M/3) ≤ B) :
    1 ≤ B*Real.exp (-M/20) := by
  have hB0 : 0<B := by linarith
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hm := Real.log_le_log (Real.exp_pos (M/3)) hM
  rw [Real.log_exp] at hm
  have he : Real.exp (-Real.log B) ≤ Real.exp (-M/20) :=
    Real.exp_le_exp.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left he hB0.le
  rw [Real.exp_neg,Real.exp_log hB0,mul_inv_cancel₀ hB0.ne'] at hh
  exact hh

/-- No lower-distance assumption is needed in any bounded-scale case.
The constant is independent of the original function and frequency. -/
theorem mrt_short_trivial_absorption (B₀ : ℝ) (X₀ : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ X H : ℕ, 10≤H → H≤X → ∀ M : ℝ,
      (majorArcParameter (Real.log (X:ℝ)) H M ≤ B₀ ∨ X≤X₀) →
      1 ≤ C*(Real.exp (-M/20)+mrtShortError X H) := by
  let B := max 2 B₀
  let Z := max 10 (max (Real.exp (B^(125:ℕ))) (X₀:ℝ))
  let K := Real.log Z/Real.log (Real.log (10:ℝ))
  have hB : 2≤B := le_max_left _ _
  have hZ : 10≤Z := le_max_left _ _
  have hK : 0≤K := div_nonneg
    (Real.log_nonneg (by linarith)) halasz_loglog_ten_pos.le
  refine ⟨K+B+1,by positivity,?_⟩
  intro X H hH hHX M hcase
  have hδ := mrt_short_error_nonneg hH hHX
  have hR : 0 ≤ Real.exp (-M/20)+mrtShortError X H := by positivity
  have hbound (hHZ : (H:ℝ)≤Z) :
      1 ≤ (K+B+1)*(Real.exp (-M/20)+mrtShortError X H) := by
    have hh := halasz_bounded_length_ratio hZ hH hHZ
    have hr : Real.log (Real.log (H:ℝ))/Real.log H ≤
        Real.exp (-M/20)+mrtShortError X H := by
      unfold mrtShortError
      linarith [Real.exp_pos (-M/20),
        Real.rpow_nonneg (Real.log_nonneg
          (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))) (-1/700:ℝ)]
    calc
      _ ≤ K*(Real.log (Real.log (H:ℝ))/Real.log H) := hh
      _ ≤ K*(Real.exp (-M/20)+mrtShortError X H) := mul_le_mul_of_nonneg_left hr hK
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR
  rcases hcase with hsmall | hX
  · rcases mrt_small_arc_parameter hB hH hHX
      (hsmall.trans (le_max_right _ _)) with hlength | hexp
    · apply hbound
      exact hlength.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have hh := mrt_small_exponential_parameter hB hexp
      calc
        _ ≤ B*Real.exp (-M/20) := hh
        _ ≤ B*(Real.exp (-M/20)+mrtShortError X H) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ) (by linarith)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hR
  · apply hbound
    have hHXr : (H:ℝ)≤X₀ := by exact_mod_cast hHX.trans hX
    exact hHXr.trans ((le_max_right _ _).trans (le_max_right _ _))

theorem mrt_short_trivial_cases (B₀ : ℝ) (X₀ : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ X H : ℕ, 10≤H → H≤X →
      ∀ F : ℕ → ℂ, OneBounded F → ∀ M : ℝ,
      (majorArcParameter (Real.log (X:ℝ)) H M ≤ B₀ ∨ X≤X₀) →
      ∀ α : ℝ, shortExponentialIntegral F X H α ≤
        C*(H:ℝ)*X*(Real.exp (-M/20)+mrtShortError X H) := by
  obtain ⟨C,hC,hbound⟩ := mrt_short_trivial_absorption B₀ X₀
  refine ⟨C,hC,?_⟩
  intro X H hH hHX F hF M hcase α
  have hh := mul_le_mul_of_nonneg_left (hbound X H hH hHX M hcase)
    (show 0≤(X:ℝ)*H by positivity)
  calc
    _ ≤ (X:ℝ)*H := minor_arc_short_integral_trivial F hF X H α
    _ ≤ _ := by convert hh using 1 <;> ring

end TwoPointCorrelations

end OAI
