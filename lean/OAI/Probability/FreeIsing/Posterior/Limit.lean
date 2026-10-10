import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

theorem tendsto_conditional_covariance_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[fun x => f x * g x | ℱ n]) ω -
        (μ[f | ℱ n]) ω * (μ[g | ℱ n]) ω)
      atTop (𝓝 ((μ[fun x => f x * g x | ⨆ n, ℱ n]) ω -
        (μ[f | ⨆ n, ℱ n]) ω * (μ[g | ⨆ n, ℱ n]) ω)) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (fun x => f x * g x),
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) g] with ω hfg hf hg
  exact hfg.sub (hf.mul hg)

private theorem artanh_continuous_at_interior {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) : ContinuousAt Real.artanh x := by
  have hd : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hp : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) (sub_pos.mpr hx.2)
  unfold Real.artanh
  exact ((continuousAt_const.add continuousAt_id).div
    (continuousAt_const.sub continuousAt_id) hd).sqrt.log
      (ne_of_gt (Real.sqrt_pos.2 hp))

theorem posterior_field_limit_of_tanh_bounds
    {u : ℕ → ℝ} {z X K : ℝ} (hu : Tendsto u atTop (𝓝 z))
    (hb : ∀ n, Real.tanh (X - K) ≤ u n ∧ u n ≤ Real.tanh (X + K)) :
    z ∈ Set.Ioo (-1 : ℝ) 1 ∧ |Real.artanh z - X| ≤ K ∧
      Tendsto (fun n => Real.artanh (u n)) atTop (𝓝 (Real.artanh z)) := by
  have hlo : Real.tanh (X - K) ≤ z :=
    ge_of_tendsto hu (Filter.Eventually.of_forall (fun n => (hb n).1))
  have hhi : z ≤ Real.tanh (X + K) :=
    le_of_tendsto hu (Filter.Eventually.of_forall (fun n => (hb n).2))
  have hz : z ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (Real.neg_one_lt_tanh _) hlo,
      lt_of_le_of_lt hhi (Real.tanh_lt_one _)⟩
  refine ⟨hz, ?_, (artanh_continuous_at_interior hz).tendsto.comp hu⟩
  have hleft := Real.artanh_le_artanh (Real.neg_one_lt_tanh (X - K)) hz.2 hlo
  have hright := Real.artanh_le_artanh hz.1 (Real.tanh_lt_one (X + K)) hhi
  rw [Real.artanh_tanh] at hleft hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_posterior_fields_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f X : Ω → ℝ) (K : ℝ)
    (hb : ∀ n, ∀ᵐ ω ∂μ,
      Real.tanh (X ω - K) ≤ (μ[f | ℱ n]) ω ∧
        (μ[f | ℱ n]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ,
      (μ[f | ⨆ n, ℱ n]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | ⨆ n, ℱ n]) ω) - X ω| ≤ K ∧
      Tendsto (fun n => Real.artanh ((μ[f | ℱ n]) ω)) atTop
        (𝓝 (Real.artanh ((μ[f | ⨆ n, ℱ n]) ω))) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    ae_all_iff.mpr hb] with ω hlim hbound
  exact posterior_field_limit_of_tanh_bounds hlim hbound

theorem tendsto_integral_sq_sub_condExp_of_bounded
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f : Ω → ℝ) (K : ℝ)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ K) :
    Tendsto (fun n => ∫ ω,
      ((μ[f | ℱ n]) ω - (μ[f | ⨆ n, ℱ n]) ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hsup : (⨆ n, ℱ n) ≤ m := iSup_le (fun n => ℱ.le n)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ω => ((μ[f | ℱ n]) ω - (μ[f | ⨆ n, ℱ n]) ω) ^ 2) μ :=
    (((stronglyMeasurable_condExp.mono (ℱ.le n)).sub
      (stronglyMeasurable_condExp.mono hsup)).pow 2).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖((μ[f | ℱ n]) ω - (μ[f | ⨆ n, ℱ n]) ω) ^ 2‖ ≤ 4 * K ^ 2 := by
    filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (m := ℱ n) hb,
      ae_bdd_abs_condExp_of_ae_bdd_abs (m := ⨆ n, ℱ n) hb] with ω hn hlimBound
    have hK : 0 ≤ K := (abs_nonneg _).trans hn
    have hd : |(μ[f | ℱ n]) ω - (μ[f | ⨆ n, ℱ n]) ω| ≤ 2 * K :=
      (abs_sub _ _).trans (by linarith)
    have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 2 * K by positivity)).2 hd
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs ((μ[f | ℱ n]) ω - (μ[f | ⨆ n, ℱ n]) ω)]
  have hlimit : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ((μ[f | ℱ n]) ω - (μ[f | ⨆ n, ℱ n]) ω) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f] with ω hω
    simpa using (hω.sub_const ((μ[f | ⨆ n, ℱ n]) ω)).pow 2
  simpa using tendsto_integral_of_dominated_convergence (fun _ : Ω => 4 * K ^ 2)
    hmeas (integrable_const _) hbound hlimit

end Problem367

end

end OAI
