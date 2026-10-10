import OAI.NumberTheory.JointDickman.Counting.CoefficientProfileFreeze

namespace OAI

/-! # Uniform coefficient-profile freezing on the manuscript exponential scale -/

namespace JointDickman
open Filter MeasureTheory
open scoped Topology

theorem abs_log_le_box {a b s : ℝ} (ha : 0 < a) (hs : s ∈ Set.Icc a b) :
    |Real.log s| ≤ max |Real.log a| |Real.log b| := by
  apply abs_le.mpr
  constructor
  · have hl := Real.log_le_log ha hs.1
    have hm := le_max_left |Real.log a| |Real.log b|
    linarith [neg_abs_le (Real.log a)]
  · exact (Real.log_le_log (ha.trans_le hs.1) hs.2).trans
      ((le_abs_self _).trans (le_max_right _ _))

theorem coefficientFourier_freeze_uniform
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2)) (H : ℕ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → ∀ (w : ℝ → ℝ) (M : ℝ), 0 ≤ M →
      Continuous w → (∀ s, |w s| ≤ M) →
      (∀ s, s ≤ a ∨ b < s → w s = 0) → ∀ ξ : ℝ,
      ‖coefficientFourierTransform c H B X w ξ-
        (coefficientDensity c H B (Real.log X/B) : ℂ)*testFourierTransform w ξ‖ ≤ C*M/B := by
  obtain ⟨_,L,_,hL,hreg⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  let R := max |Real.log a| |Real.log b|
  have hR : 0 ≤ R := (abs_nonneg _).trans (le_max_left _ _)
  refine ⟨(b-a)*L*R,by positivity,?_⟩
  filter_upwards [hreg,coefficient_support_window ha,eventually_gt_atTop 0,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (5*R/2)] with B hregB hwindow hB hBR
  intro X hX hlog w M hM0 hw hwb hsupp ξ
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hx : (1/2 : ℝ) ≤ Real.log X/B := (le_div_iff₀ hB0).mpr (by linarith)
  have hsx : ∀ s ∈ Set.Icc a b, (1/2 : ℝ) ≤ Real.log (s*X)/B := by
    intro s hs
    rw [le_div_iff₀ hB0,Real.log_mul (ha.trans_le hs.1).ne' hX.ne']
    have hl := abs_log_le_box ha hs
    change |Real.log s| ≤ R at hl
    linarith [neg_abs_le (Real.log s)]
  have hh := coefficientFourier_freeze_bound c H B hB hX ha hab
    (lt_of_lt_of_le (by norm_num) (hwindow X hX hlog).1) hM0 hL
    hx hsx hregB.2 hw hwb hsupp (fun s hs => abs_log_le_box ha hs) ξ
  convert hh using 1; ring

end JointDickman

end OAI
