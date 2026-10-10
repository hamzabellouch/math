import OAI.Probability.StrongRayleigh.ContinuousModification

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

namespace Problem336AdditiveD139.BrownianStochasticContinuity

variable {Ω : Type u_1} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem tendstoInMeasure_eval {ι : Type u_2} {l : Filter ι}
    (hB : IsPreBrownianReal B P) {u : ι → ℝ≥0} {t : ℝ≥0}
    (hu : Tendsto u l (𝓝 t)) : TendstoInMeasure P (fun i => B (u i)) l (B t) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hbound (i : ι) : P {ω | ε ≤ ‖B (u i) ω - B t ω‖} ≤
      ENNReal.ofReal (dist (u i : ℝ) (t : ℝ) / ε ^ 2) := by
    have hL := hB.hasLaw_sub (u i) t
    have hmean : (∫ ω, B (u i) ω - B t ω ∂P) = 0 := by
      change P[B (u i) - B t] = 0
      rw [hL.integral_eq, integral_id_gaussianReal]
    have hvar : Var[B (u i) - B t; P] = dist (u i : ℝ) (t : ℝ) := by
      rw [hL.variance_eq, variance_id_gaussianReal]
      rfl
    simpa only [hmean, sub_zero, hvar, Pi.sub_apply, Real.norm_eq_abs] using
      meas_ge_le_variance_div_sq hL.hasGaussianLaw.memLp_two hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => bot_le) hbound
  have hu' : Tendsto (fun i => (u i : ℝ)) l (𝓝 (t : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp hu
  have hd := (hu'.dist (tendsto_const_nhds (x := (t : ℝ)))).div_const (ε ^ 2)
  simpa only [Function.comp_def, dist_self, zero_div, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hd

theorem ae_eq_of_tendsto_times (hB : IsPreBrownianReal B P)
    (W : Ω → C(ℝ≥0, ℝ)) {u : ℕ → ℝ≥0} {t : ℝ≥0}
    (hu : Tendsto u atTop (𝓝 t))
    (hversion : ∀ n, (fun ω => W ω (u n)) =ᵐ[P] B (u n)) :
    (fun ω => W ω t) =ᵐ[P] B t := by
  apply ContinuousModification.ae_eq_of_ae_tendsto_of_tendstoInMeasure _
    (tendstoInMeasure_eval hB hu)
  filter_upwards [ae_all_iff.mpr hversion] with ω hω
  have hlim := ((W ω).continuous.tendsto t).comp hu
  simpa only [Function.comp_def, hω] using hlim

theorem ae_eq_of_dense (hB : IsPreBrownianReal B P)
    (W : Ω → C(ℝ≥0, ℝ)) {D : Type u_3} (e : D → ℝ≥0) (he : DenseRange e)
    (hversion : ∀ d, (fun ω => W ω (e d)) =ᵐ[P] B (e d)) (t : ℝ≥0) :
    (fun ω => W ω t) =ᵐ[P] B t := by
  classical
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (he t)
  choose v hv using hu
  have hvlim : Tendsto (fun n => e (v n)) atTop (𝓝 t) := by
    simpa only [hv] using hlim
  exact ae_eq_of_tendsto_times hB W hvlim (fun n => hversion (v n))

theorem isBrownianReal_of_dense (hB : IsPreBrownianReal B P)
    (W : Ω → C(ℝ≥0, ℝ)) {D : Type u_4} (e : D → ℝ≥0) (he : DenseRange e)
    (hversion : ∀ d, (fun ω => W ω (e d)) =ᵐ[P] B (e d)) :
    IsBrownianReal (fun t ω => W ω t) P := by
  exact ⟨hB.congr (fun t => (ae_eq_of_dense hB W e he hversion t).symm),
    ae_of_all _ (fun ω => (W ω).continuous)⟩

end Problem336AdditiveD139.BrownianStochasticContinuity

end

end OAI
