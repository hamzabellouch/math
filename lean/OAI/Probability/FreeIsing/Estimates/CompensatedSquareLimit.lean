import OAI.Probability.FreeIsing.Stochastic.StoppedSimpleIntegral

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem367.CompensatedSquareLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem eLpNorm_sq_sub_le {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => (f ω) ^ 2 - (g ω) ^ 2) 1 μ ≤
      eLpNorm (f - g) 2 μ *
        (eLpNorm (f - g) 2 μ + (eLpNorm g 2 μ + eLpNorm g 2 μ)) := by
  have hfactor : (fun ω => (f ω) ^ 2 - (g ω) ^ 2) =
      fun ω => (f ω - g ω) * (f ω + g ω) := by
    funext ω
    ring
  have hsum : eLpNorm (f + g) 2 μ ≤
      eLpNorm (f - g) 2 μ + (eLpNorm g 2 μ + eLpNorm g 2 μ) := by
    have heq : f + g = (f - g) + (g + g) := by
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq]
    exact (eLpNorm_add_le (by norm_num)).trans
      (add_le_add le_rfl (eLpNorm_add_le (p := 2) (by norm_num)))
  rw [hfactor]
  calc
    _ ≤ eLpNorm (f - g) 2 μ * eLpNorm (f + g) 2 μ := by
      simpa using
        (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
          (p := 2) (q := 2) (r := 1)
          (fun first second : ℝ => first * second) 1 continuous_mul
          (hf.sub hg) (hf.add hg)
          (Eventually.of_forall (fun ω => by simp [norm_mul])))
    _ ≤ _ := mul_le_mul_right hsum _

theorem tendsto_eLpNorm_sq_sub {N : Type*} {l : Filter N}
    {f : N → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => (f n ω) ^ 2 - (g ω) ^ 2) 1 μ)
      l (𝓝 0) := by
  have hsum := hlim.add_const (eLpNorm g 2 μ + eLpNorm g 2 μ)
  have hfinite : (0 : ℝ≥0∞) + (eLpNorm g 2 μ + eLpNorm g 2 μ) ≠ ∞ := by
    simpa using ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  have hb := ENNReal.Tendsto.mul hlim (Or.inr hfinite) hsum
    (Or.inr ENNReal.zero_ne_top)
  simp only [zero_mul] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun n => eLpNorm_sq_sub_le (hf n) hg.aestronglyMeasurable)

theorem martingale_compensatedSquare_of_limits
    {ι N : Type*} [LinearOrder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {l : Filter N} [l.NeBot]
    {X A : N → ι → Ω → ℝ} {Y Q : ι → Ω → ℝ}
    (hX : ∀ n t, MemLp (X n t) 2 P)
    (_hA : ∀ n t, Integrable (A n t) P)
    (hcomp : ∀ n, Martingale (fun t ω => (X n t ω) ^ 2 - A n t ω) F P)
    (hY : StronglyAdapted F Y) (hY2 : ∀ t, MemLp (Y t) 2 P)
    (hQ : StronglyAdapted F Q) (hQint : ∀ t, Integrable (Q t) P)
    (hlim : ∀ t, Tendsto (fun n => eLpNorm (X n t - Y t) 2 P) l (𝓝 0))
    (hAlim : ∀ t, Tendsto (fun n => eLpNorm (A n t - Q t) 1 P) l (𝓝 0)) :
    Martingale (fun t ω => (Y t ω) ^ 2 - Q t ω) F P := by
  apply StoppedSimpleIntegral.martingale_of_pointwise_time_L1_limit (l := l) hcomp
  · intro t
    exact ((hY t).pow 2).sub (hQ t)
  · intro t
    exact (hY2 t).integrable_sq.sub (hQint t)
  · intro t
    have hs := tendsto_eLpNorm_sq_sub
      (fun n => (hX n t).aestronglyMeasurable) (hY2 t) (hlim t)
    have hb := hs.add (hAlim t)
    simp only [add_zero] at hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
    intro n
    have heq : (fun ω => (X n t ω) ^ 2 - A n t ω) -
        (fun ω => (Y t ω) ^ 2 - Q t ω) =
        (fun ω => (X n t ω) ^ 2 - (Y t ω) ^ 2) - (A n t - Q t) := by
      funext ω
      simp only [Pi.sub_apply]
      ring
    dsimp only
    rw [heq]
    exact eLpNorm_sub_le le_rfl

theorem eLpNorm_two_eq_ofReal_integral_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = (ENNReal.ofReal (∫ ω, (f ω) ^ 2 ∂μ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Eventually.of_forall (fun ω => sq_nonneg _))]
  apply lintegral_congr
  intro ω
  simp [← ofReal_norm, ← ENNReal.ofReal_pow, Real.norm_eq_abs, sq_abs]

theorem tendsto_eLpNorm_two_of_meanSquare {N : Type*} {l : Filter N}
    {f : N → Ω → ℝ} {g : Ω → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - g) 2 μ) l (𝓝 0) := by
  have ho : Tendsto (fun n => ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ)) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  have h := (ENNReal.continuous_rpow_const (y := 1 / 2).tendsto (0 : ℝ≥0∞)).comp ho
  have heq (n) := eLpNorm_two_eq_ofReal_integral_sq ((hf n).sub hg)
  simpa only [Function.comp_def, heq, Pi.sub_apply, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h

end Problem367.CompensatedSquareLimit

end

end OAI
