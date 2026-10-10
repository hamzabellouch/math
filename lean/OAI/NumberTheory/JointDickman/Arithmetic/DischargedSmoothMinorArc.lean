import OAI.NumberTheory.JointDickman.Arithmetic.SmoothCoefficientMinorArc
import OAI.NumberTheory.JointDickman.Amplification.ComplexPartialSummation
import OAI.NumberTheory.JointDickman.Counting.MinorArcSupportWindow
import OAI.NumberTheory.JointDickman.Counting.DischargedCoefficientMinorArc

namespace OAI

/-! # Discharged smooth minor arcs in the logarithmic range used by the main proof -/

namespace JointDickman
open Filter Finset
open scoped Topology

open Classical in
theorem smooth_coefficient_minorArc_bounded_log
    {a b ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop, ∀ X θ : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (11/5 : ℝ)*B →
      ¬ InRationalArc θ ((B : ℝ)^12) ((B : ℝ)^13/X) →
      ∀ (w w' : ℝ → ℝ) (M N : ℝ), 0 ≤ M → 0 ≤ N →
      (∀ t, HasDerivAt w (w' t) t) → Continuous w' →
      (∀ t, |w t| ≤ M) → (∀ t, |w' t| ≤ N) →
      (∀ t, t ≤ a ∨ b < t → w t = 0) →
      ‖smoothCoefficientAdditiveSum B X θ w‖ ≤
        C*b*(2*M+N*(b-a))*X*(B : ℝ)^(-1/2+ε) := by
  obtain ⟨C₀,hC₀,hbound⟩ := coefficient_minorArc_bounded_log hε
  have hb : 0 < b := ha.trans_le hab
  let C := C₀*(1+2*Real.pi*b)
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogb : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (4/5:ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<4/5)).eventually_ge_atTop _
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,minorArc_support_window (b := b) ha,eventually_ge_atTop 1,hlogb]
    with B hboundB hwindow hB hlogbB
  intro X θ hX hlogX hlogXhi hminor w w' M N hM hN hw hw' hwbound hw'bound hsupport
  obtain ⟨hXlarge,hwindowX⟩ := hwindow X hX hlogX
  let D := C*b*X*(B : ℝ)^(-1/2+ε)
  have hpartial : ∀ t ∈ Set.Icc (a*X) (b*X),
      ‖∑ n ∈ Icc 0 ⌊t⌋₊, (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)‖ ≤ D := by
    intro t ht
    obtain ⟨hY,hlogY,hXY,hYb⟩ := hwindowX t ht
    rw [coefficient_partial_sum_from_zero]
    have hY0 : (0:ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
    have hlogYhi : Real.log (⌊t⌋₊:ℝ) ≤ 3*(B:ℝ) := by
      have hh := Real.log_le_log hY0 hYb
      rw [Real.log_mul hb.ne' hX.ne'] at hh
      linarith
    exact (hboundB ⌊t⌋₊ X θ b (by omega) hlogY hlogYhi hXlarge hXY hYb hminor).trans
      (by
        dsimp [D,C]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
        nlinarith)
  have htest := complex_partial_summation_bound
    (fun n => (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ))
    (scaledOscillatoryTest w 0 X) (scaledOscillatoryTestDeriv w w' 0 X)
    (a := a*X) (b := b*X) (D := D) (M := M) (N := N/X)
    (mul_nonneg ha.le hX.le) (mul_le_mul_of_nonneg_right hab hX.le)
    (by dsimp [D]; positivity) hM (div_nonneg hN hX.le)
    (fun t _ => hasDerivAt_scaledOscillatoryTest (hw (t/X)))
    (scaledOscillatoryTestDeriv_continuous (continuous_iff_continuousAt.mpr (fun t => (hw t).continuousAt)) hw' 0 X).continuousOn
    (fun t _ => scaledOscillatoryTest_norm_le (hwbound (t/X)))
    (fun t _ => by
      simpa using scaledOscillatoryTestDeriv_norm_le (ξ := 0) hX
        (hwbound (t/X)) (hw'bound (t/X))) hpartial
  have hsum := tsum_eq_Ioc_of_scaled_support ha.le hab hX hsupport
    (fun n => (coefficientWeight B n : ℂ)*(w (n/X) : ℂ)*additivePhase ((n : ℝ)*θ))
    (fun n hn => by simp [hn])
  have hsum' : smoothCoefficientAdditiveSum B X θ w =
      ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
        scaledOscillatoryTest w 0 X n *
          ((coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)) := by
    rw [smoothCoefficientAdditiveSum,hsum]
    apply sum_congr rfl
    intro n _
    simp only [scaledOscillatoryTest,oscillatoryTest,zero_mul]
    have hzero : additivePhase 0 = 1 := by simp [additivePhase]
    rw [hzero,mul_one]
    ring
  rw [hsum']
  refine htest.trans_eq ?_
  dsimp [D]
  field_simp

end JointDickman

end OAI
