import Mathlib

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Problem336AdditiveD139.InnovationMean

variable {T : Type u_1} {Ω : Type u_2} [MeasurableSpace T] {m n : MeasurableSpace Ω}
  [mΩ : MeasurableSpace Ω]
  {ν : Measure T} {μ : Measure Ω} [IsFiniteMeasure ν] [IsFiniteMeasure μ]

theorem condExp_integral_of_posteriors
    (hm : m ≤ mΩ)
    (H : T → MeasurableSpace Ω) (hH : ∀ t, H t ≤ mΩ)
    (hmH : ∀ᵐ t ∂ν, m ≤ H t)
    {X : Ω → ℝ} (hX : Integrable X μ)
    {b : T → Ω → ℝ}
    (hb : Integrable (Function.uncurry b) (ν.prod μ))
    (hpost : ∀ᵐ t ∂ν, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ∫ t, b t ω ∂ν | m] =ᵐ[μ]
      fun ω => ν.real Set.univ * μ[X | m] ω := by
  have hint : Integrable (fun ω => ∫ t, b t ω ∂ν) μ :=
    hb.integral_prod_right
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (fun s _ _ => (integrable_condExp.const_mul _).integrableOn) ?_
    (stronglyMeasurable_condExp.const_mul _).aestronglyMeasurable
  intro s hs _
  have hbs : Integrable (Function.uncurry b) (ν.prod (μ.restrict s)) := by
    simpa only [← Measure.prod_restrict, Measure.restrict_univ] using
      hb.restrict (s := Set.univ ×ˢ s)
  rw [integral_const_mul, setIntegral_condExp hm hX hs]
  rw [← integral_integral_swap hbs]
  have heq : (fun t => ∫ ω in s, b t ω ∂μ) =ᵐ[ν]
      fun _ => ∫ ω in s, X ω ∂μ := by
    filter_upwards [hmH, hpost] with t hmt hpt
    calc
      (∫ ω in s, b t ω ∂μ) = ∫ ω in s, μ[X | H t] ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hpt)
      _ = ∫ ω in s, X ω ∂μ := setIntegral_condExp (hH t) hX (hmt s hs)
  rw [integral_congr_ae heq, integral_const]
  rfl

theorem condExp_intervalIntegral_of_posteriors
    (H : Filtration ℝ mΩ) {u v : ℝ} (huv : u ≤ v)
    {X : Ω → ℝ} (hX : Integrable X μ)
    {b : ℝ → Ω → ℝ}
    (hb : Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ))
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ∫ t in u..v, b t ω | H u] =ᵐ[μ]
      fun ω => (v - u) * μ[X | H u] ω := by
  have hle : ∀ᵐ t ∂volume.restrict (Set.Ioc u v), H u ≤ H t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact H.mono ht.1.le
  have hp : ∀ᵐ t ∂volume.restrict (Set.Ioc u v), b t =ᵐ[μ] μ[X | H t] := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpost t ht
  have h := condExp_integral_of_posteriors (H.le u) H H.le hle hX hb hp
  simpa only [intervalIntegral.integral_of_le huv, measureReal_def,
    Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr huv)] using h

theorem integrable_bounded_drift
    {u v C : ℝ} {b : ℝ → Ω → ℝ}
    (hb : Measurable (Function.uncurry b))
    (hbound : ∀ t ω, |b t ω| ≤ C) :
    Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ) := by
  exact Integrable.of_bound hb.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs, Function.uncurry] using hbound p.1 p.2))

theorem condExp_innovation_increment_eq_zero
    (H : Filtration ℝ mΩ) {u v : ℝ} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ → Ω → ℝ}
    (hb : Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ))
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] =ᵐ[μ] 0 := by
  have hi : Integrable (fun ω => ∫ t in u..v, b t ω) μ := by
    simpa only [intervalIntegral.integral_of_le huv, Function.uncurry] using hb.integral_prod_right
  have hci := condExp_intervalIntegral_of_posteriors H huv hX hb hpost
  have hsub := condExp_sub ((hX.const_mul (v - u)).add hQ) hi (H u)
  have hadd := condExp_add (hX.const_mul (v - u)) hQ (H u)
  have hmul := condExp_smul (μ := μ) (v - u) X (H u)
  filter_upwards [hsub, hadd, hmul, hQmean, hci] with ω hs ha hm hq hc
  change μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] ω = 0
  change μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] ω =
    μ[fun ω => (v - u) * X ω + Q ω | H u] ω -
      μ[fun ω => ∫ t in u..v, b t ω | H u] ω at hs
  change μ[fun ω => (v - u) * X ω + Q ω | H u] ω =
    μ[fun ω => (v - u) * X ω | H u] ω + μ[Q | H u] ω at ha
  change μ[fun ω => (v - u) * X ω | H u] ω = (v - u) * μ[X | H u] ω at hm
  change μ[Q | H u] ω = 0 at hq
  rw [hs, ha, hm, hq, hc]
  ring

theorem condExp_innovation_increment_eq_zero_of_indep
    (H : Filtration ℝ mΩ) {u v : ℝ} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hn : n ≤ mΩ) (hQn : StronglyMeasurable[n] Q)
    (hindep : ProbabilityTheory.Indep n (H u) μ)
    (hQmean : ∫ ω, Q ω ∂μ = 0)
    {b : ℝ → Ω → ℝ}
    (hb : Integrable (Function.uncurry b)
      ((volume.restrict (Set.Ioc u v)).prod μ))
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] =ᵐ[μ] 0 := by
  apply condExp_innovation_increment_eq_zero H huv hX hQ _ hb hpost
  change μ[Q | H u] =ᵐ[μ] fun _ => (0 : ℝ)
  simpa only [hQmean] using condExp_indep_eq hn (H.le u) hQn hindep

theorem bounded_innovation_condExp_eq_zero
    (H : Filtration ℝ mΩ) {u v C : ℝ} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    (hbound : ∀ t ω, |b t ω| ≤ C)
    (hpost : ∀ t ∈ Set.Ioc u v, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => (v - u) * X ω + Q ω - ∫ t in u..v, b t ω | H u] =ᵐ[μ] 0 :=
  condExp_innovation_increment_eq_zero H huv hX hQ hQmean
    (integrable_bounded_drift hb hbound) hpost

theorem condExp_intervalIntegral_nnreal_of_posteriors
    (H : Filtration ℝ≥0 mΩ) {u v : ℝ≥0} (huv : u ≤ v)
    {X : Ω → ℝ} (hX : Integrable X μ)
    {b : ℝ≥0 → Ω → ℝ}
    (hb : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (u : ℝ) (v : ℝ))).prod μ))
    (hpost : ∀ t : ℝ≥0, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω | H u] =ᵐ[μ]
      fun ω => ((v : ℝ) - (u : ℝ)) * μ[X | H u] ω := by
  have hle : ∀ᵐ t ∂volume.restrict (Set.Ioc (u : ℝ) (v : ℝ)),
      H u ≤ H t.toNNReal := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply H.mono
    exact_mod_cast (ht.1.le.trans (Real.le_coe_toNNReal t))
  have hp : ∀ᵐ t ∂volume.restrict (Set.Ioc (u : ℝ) (v : ℝ)),
      b t.toNNReal =ᵐ[μ] μ[X | H t.toNNReal] :=
    Filter.Eventually.of_forall (fun t => hpost t.toNNReal)
  have h := condExp_integral_of_posteriors (H.le u)
    (fun t : ℝ => H t.toNNReal) (fun t => H.le t.toNNReal) hle hX
    (b := fun t ω => b t.toNNReal ω) (by
      change Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2) _
      exact hb) hp
  have huv' : (u : ℝ) ≤ (v : ℝ) := huv
  simpa only [intervalIntegral.integral_of_le huv', measureReal_def,
    Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr huv')] using h

theorem condExp_innovation_increment_nnreal_eq_zero
    (H : Filtration ℝ≥0 mΩ) {u v : ℝ≥0} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ≥0 → Ω → ℝ}
    (hb : Integrable (fun p : ℝ × Ω => b p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (u : ℝ) (v : ℝ))).prod μ))
    (hpost : ∀ t : ℝ≥0, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ((v : ℝ) - (u : ℝ)) * X ω + Q ω -
      ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω | H u] =ᵐ[μ] 0 := by
  have hi : Integrable (fun ω => ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω) μ := by
    simpa only [intervalIntegral.integral_of_le (show (u : ℝ) ≤ (v : ℝ) from huv)]
      using hb.integral_prod_right
  have hci := condExp_intervalIntegral_nnreal_of_posteriors H huv hX hb hpost
  have hsub := condExp_sub ((hX.const_mul ((v : ℝ) - u)).add hQ) hi (H u)
  have hadd := condExp_add (hX.const_mul ((v : ℝ) - u)) hQ (H u)
  have hmul := condExp_smul (μ := μ) ((v : ℝ) - u) X (H u)
  filter_upwards [hsub, hadd, hmul, hQmean, hci] with ω hs ha hm hq hc
  change μ[(fun ω => ((v : ℝ) - u) * X ω) + Q -
    (fun ω => ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω) | H u] ω = 0
  dsimp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    at hs ha hm hq
  change μ[fun ω => ((v : ℝ) - u) * X ω | H u] ω =
    ((v : ℝ) - u) * μ[X | H u] ω at hm
  rw [hs, ha, hm, hq, hc]
  ring

theorem bounded_innovation_condExp_nnreal_eq_zero
    (H : Filtration ℝ≥0 mΩ) {u v : ℝ≥0} (huv : u ≤ v)
    {X Q : Ω → ℝ} (hX : Integrable X μ) (hQ : Integrable Q μ)
    (hQmean : μ[Q | H u] =ᵐ[μ] 0)
    {b : ℝ≥0 → Ω → ℝ} (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hbound : ∀ t ω, |b t ω| ≤ C)
    (hpost : ∀ t : ℝ≥0, b t =ᵐ[μ] μ[X | H t]) :
    μ[fun ω => ((v : ℝ) - (u : ℝ)) * X ω + Q ω -
      ∫ t in (u : ℝ)..(v : ℝ), b t.toNNReal ω | H u] =ᵐ[μ] 0 := by
  apply condExp_innovation_increment_nnreal_eq_zero H huv hX hQ hQmean _ hpost
  have hb' : Measurable (Function.uncurry (fun (t : ℝ) ω => b t.toNNReal ω)) :=
    hb.comp (show Measurable (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) by fun_prop)
  exact integrable_bounded_drift hb' (fun t ω => hbound t.toNNReal ω)

end Problem336AdditiveD139.InnovationMean

end

end OAI
