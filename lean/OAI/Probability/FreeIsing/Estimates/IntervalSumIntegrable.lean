import OAI.Probability.FreeIsing.Stochastic.StoppedSimpleIntegral

namespace OAI

noncomputable section

open MeasureTheory Filter

namespace Problem367.StoppedSimpleIntegral

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [LinearOrder ι]
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
  {B : ι → Ω → ℝ}

theorem intervalSum_eq_condExp_terminal_of_integrable
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H)
    (hYint : Integrable (fun ω => H ω * (B b ω - B a ω)) P) (t : ι) :
    P[(fun ω => H ω * (B b ω - B a ω)) | F t] =ᵐ[P]
      intervalSum B H a b t := by
  have hDint : Integrable (fun ω => B b ω - B a ω) P :=
    (hB.integrable b).sub (hB.integrable a)
  rcases le_total t a with hta | hat
  · have hzero : P[(fun ω => B b ω - B a ω) | F a] =ᵐ[P] fun _ => 0 := by
      have hs := condExp_sub (hB.integrable b) (hB.integrable a) (F a)
      filter_upwards [hs, hB.condExp_ae_eq hab, hB.condExp_ae_eq (le_refl a)]
        with ω hs hb ha
      change P[(fun ω => B b ω - B a ω) | F a] ω =
        P[B b | F a] ω - P[B a | F a] ω at hs
      simpa only [hb, ha, sub_self] using hs
    have hyzero : P[(fun ω => H ω * (B b ω - B a ω)) | F a] =ᵐ[P] fun _ => 0 := by
      have hp := condExp_mul_of_stronglyMeasurable_left hH hYint hDint
      filter_upwards [hp, hzero] with ω hp hz
      change P[(fun ω => H ω * (B b ω - B a ω)) | F a] ω =
        H ω * P[(fun ω => B b ω - B a ω) | F a] ω at hp
      simpa only [hz, mul_zero] using hp
    have htower := condExp_condExp_of_le (μ := P) (F.mono hta) (F.le a)
      (f := fun ω => H ω * (B b ω - B a ω))
    calc
      P[(fun ω => H ω * (B b ω - B a ω)) | F t] =ᵐ[P]
          P[P[(fun ω => H ω * (B b ω - B a ω)) | F a] | F t] := htower.symm
      _ =ᵐ[P] P[(fun _ : Ω => (0 : ℝ)) | F t] := condExp_congr_ae hyzero
      _ =ᵐ[P] intervalSum B H a b t := by
        change P[(0 : Ω → ℝ) | F t] =ᵐ[P] intervalSum B H a b t
        rw [condExp_zero]
        apply Filter.Eventually.of_forall
        intro ω
        simp only [intervalSum, min_eq_left hta, min_eq_left (hta.trans hab),
          Pi.zero_apply, sub_self, mul_zero]
  · have hp := condExp_mul_of_stronglyMeasurable_left (hH.mono (F.mono hat)) hYint hDint
    have hs := condExp_sub (hB.integrable b) (hB.integrable a) (F t)
    filter_upwards [hp, hs, condExp_eval_eq_min hB t b, condExp_eval_eq_min hB t a]
      with ω hp hs hb ha
    change P[(fun ω => H ω * (B b ω - B a ω)) | F t] ω =
      H ω * P[(fun ω => B b ω - B a ω) | F t] ω at hp
    change P[(fun ω => B b ω - B a ω) | F t] ω =
      P[B b | F t] ω - P[B a | F t] ω at hs
    rw [hp, hs, hb, ha]
    rfl

theorem intervalSum_martingale_of_integrable_terminal
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H)
    (hYint : Integrable (fun ω => H ω * (B b ω - B a ω)) P) :
    Martingale (intervalSum B H a b) F P :=
  (martingale_condExp (fun ω => H ω * (B b ω - B a ω)) F P).congr
    (intervalSum_stronglyAdapted hB hab hH)
    (intervalSum_eq_condExp_terminal_of_integrable hB hab hH hYint)

theorem intervalSum_martingale_of_memLp_two
    (hB : Martingale B F P) {a b : ι} (hab : a ≤ b)
    {H : Ω → ℝ} (hH : StronglyMeasurable[F a] H) (hH2 : MemLp H 2 P)
    (ha2 : MemLp (B a) 2 P) (hb2 : MemLp (B b) 2 P) :
    Martingale (intervalSum B H a b) F P :=
  intervalSum_martingale_of_integrable_terminal hB hab hH
    (hH2.integrable_mul (hb2.sub ha2))

end Problem367.StoppedSimpleIntegral

end

end OAI
