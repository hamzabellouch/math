import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra

namespace OAI

/-! # The upper-time cutoff costs a fifth power of the deleted interval length -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem iterate_zero_before (a b : ℝ) (K : Kernel KineticPhase Velocity)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ≤ b → f z = 0) (n : ℕ) :
    ∀ z, z.1.1 ≤ b → iterate a K f n z = 0 := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro z hz
    apply setLIntegral_eq_zero measurableSet_Ioc
    intro s hs
    change (∫⁻ v, iterate a K f n ((flight z s).1,v) ∂K (flight z s)) = 0
    have hzero : (fun v => iterate a K f n ((flight z s).1,v)) = fun _ => 0 := by
      funext v
      exact ih _ (hs.2.trans hz)
    rw [hzero,lintegral_zero]

theorem iterate_late_bound {a b T : ℝ} (K : Kernel KineticPhase Velocity)
    {C B : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B)
    (hzero : ∀ z, z.1.1 ≤ b → f z = 0) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T → iterate a K f n z ≤ B*(C*ENNReal.ofReal (T-b))^n := by
  induction n with
  | zero => simpa only [iterate,pow_zero,mul_one] using hf
  | succ n ih =>
    intro z hz
    let A := B*(C*ENNReal.ofReal (T-b))^n
    change step a K (iterate a K f n) z ≤ _
    unfold step
    calc
      _ ≤ ∫⁻ s in Ioc a z.1.1, (Ioc b T).indicator (fun _ => A*C) s := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have ht : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
        by_cases hb : b < s
        · rw [indicator_of_mem (show s ∈ Ioc b T from ⟨hb,ht.2⟩)]
          calc
            _ ≤ ∫⁻ _v, A ∂K (flight z s) := lintegral_mono (fun v => ih _ ht)
            _ = A*K (flight z s) univ := by rw [lintegral_const,mul_comm]
            _ ≤ A*C := mul_le_mul' le_rfl (hK _ ht)
        · have hz' : (fun v => iterate a K f n ((flight z s).1,v)) = fun _ => 0 := by
            funext v
            exact iterate_zero_before a b K hzero n _ (le_of_not_gt hb)
          rw [hz',lintegral_zero]
          exact zero_le
      _ ≤ ∫⁻ s, (Ioc b T).indicator (fun _ => A*C) s := setLIntegral_le_lintegral _ _
      _ = (A*C)*ENNReal.ofReal (T-b) := by
        rw [lintegral_indicator_const measurableSet_Ioc,Real.volume_Ioc]
      _ = B*(C*ENNReal.ofReal (T-b))^(n+1) := by
        dsimp only [A]
        rw [pow_succ]
        ring

theorem late_terminal_five_bound {a T δ : ℝ} (K : Kernel KineticPhase Velocity)
    {C B : ℝ≥0∞} (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ B)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    iterate a K ({y : KineticPhase | T-δ < y.1.1}.indicator f) 5 z ≤
      B*(C*ENNReal.ofReal δ)^5 := by
  have hbound (y : KineticPhase) (hy : y.1.1 ∈ Icc a T) :
      {y : KineticPhase | T-δ < y.1.1}.indicator f y ≤ B := by
    by_cases h : T-δ < y.1.1
    · rw [indicator_of_mem (show y ∈ {y : KineticPhase | T-δ < y.1.1} from h)]
      exact hf y hy
    · rw [indicator_of_notMem (show y ∉ {y : KineticPhase | T-δ < y.1.1} from h)]
      exact zero_le
  have hzero (y : KineticPhase) (hy : y.1.1 ≤ T-δ) :
      {y : KineticPhase | T-δ < y.1.1}.indicator f y = 0 :=
    indicator_of_notMem (show y ∉ {y : KineticPhase | T-δ < y.1.1} from not_lt_of_ge hy) _
  simpa only [sub_sub_cancel] using iterate_late_bound K hK hbound hzero 5 z hz

end BoltzmannNonuniqueness.PositiveIteration

end

end OAI
