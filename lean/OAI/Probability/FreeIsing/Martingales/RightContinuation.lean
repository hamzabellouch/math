import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

theorem martingale_rightCont_of_L1_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X F P)
    (hcont : ∀ s, Tendsto (fun t => eLpNorm (X t - X s) 1 P)
      (𝓝[>] s) (𝓝 0)) :
    Martingale X F.rightCont P := by
  have had : StronglyAdapted F.rightCont X :=
    fun s => (hX.stronglyAdapted s).mono (F.le_rightCont s)
  refine ⟨had, ?_⟩
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact (condExp_of_stronglyMeasurable (F.rightCont.le s) (had s)
      (hX.integrable s)).eventuallyEq
  · apply (ae_eq_condExp_of_forall_setIntegral_eq (F.rightCont.le s)
      (hX.integrable t) (fun A hA _ => (hX.integrable s).integrableOn) ?_
      (had s).aestronglyMeasurable).symm
    intro A hA hAfin
    have hlim := tendsto_setIntegral_of_L1' (X s)
      (Eventually.of_forall hX.integrable) (hcont s) A
    have heq : ∀ᶠ u in 𝓝[>] s, (∫ ω in A, X u ω ∂P) = ∫ ω in A, X t ω ∂P := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds]
        with u hsu hut
      have hFu : F.rightCont s ≤ F u := by
        rw [F.rightCont_eq]
        exact iInf₂_le u hsu
      exact hX.setIntegral_eq hut.le (hFu A hA)
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

theorem condExp_rightCont_of_L1_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}
    (hZ : Integrable Z P) (had : StronglyAdapted F X)
    (hversion : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hcont : ∀ s, Tendsto (fun t => eLpNorm (X t - X s) 1 P)
      (𝓝[>] s) (𝓝 0)) (s : ℝ≥0) :
    X s =ᵐ[P] P[Z | F.rightCont s] := by
  have hint (t) : Integrable (X t) P := integrable_condExp.congr (hversion t).symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.rightCont.le s) hZ
    (fun A hA _ => (hint s).integrableOn) ?_
    ((had s).mono (F.le_rightCont s)).aestronglyMeasurable
  intro A hA hAfin
  have hlim := tendsto_setIntegral_of_L1' (X s)
    (Eventually.of_forall hint) (hcont s) A
  have heq : ∀ᶠ u in 𝓝[>] s, (∫ ω in A, X u ω ∂P) = ∫ ω in A, Z ω ∂P := by
    filter_upwards [self_mem_nhdsWithin] with u hsu
    have hFu : F.rightCont s ≤ F u := by
      rw [F.rightCont_eq]
      exact iInf₂_le u hsu
    calc
      (∫ ω in A, X u ω ∂P) = ∫ ω in A, P[Z | F u] ω ∂P :=
        integral_congr_ae (ae_restrict_of_ae (hversion u))
      _ = ∫ ω in A, Z ω ∂P := setIntegral_condExp (F.le u) hZ (hFu A hA)
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

theorem tendsto_L1_of_ae_continuous_bounded
    {T Ω : Type*} [TopologicalSpace T] [FirstCountableTopology T]
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : T → Ω → ℝ} {C : ℝ}
    (hint : ∀ t, Integrable (X t) P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ C)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) (s : T) :
    Tendsto (fun t => eLpNorm (X t - X s) 1 P) (𝓝 s) (𝓝 0) := by
  have hc : Continuous (fun t => ∫ ω, ‖X t ω - X s ω‖ ∂P) := by
    apply continuous_of_dominated
      (fun t => ((hint t).sub (hint s)).aestronglyMeasurable.norm)
      (bound := fun _ => 2 * C)
    · intro t
      filter_upwards [hbound t, hbound s] with ω ht hs
      simpa only [norm_norm, Pi.sub_apply] using (norm_sub_le (X t ω) (X s ω)).trans (by linarith)
    · exact integrable_const _
    · filter_upwards [hcont] with ω hω
      exact (hω.sub continuous_const).norm
  have heq (t : T) : eLpNorm (X t - X s) 1 P =
      ENNReal.ofReal (∫ ω, ‖X t ω - X s ω‖ ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((hint t).sub (hint s)).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hint t).sub (hint s))]
    rfl
  simp_rw [heq]
  simpa [Function.comp_def] using (ENNReal.continuous_ofReal.comp hc).tendsto s

theorem martingale_rightCont_of_ae_continuous_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hX : Martingale X F P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ C)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) :
    Martingale X F.rightCont P := by
  apply martingale_rightCont_of_L1_rightContinuous hX
  intro s
  exact (tendsto_L1_of_ae_continuous_bounded hX.integrable hbound hcont s).mono_left
    nhdsWithin_le_nhds

theorem condExp_rightCont_of_ae_continuous_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} {C : ℝ}
    (hZ : Integrable Z P) (had : StronglyAdapted F X)
    (hversion : ∀ t, X t =ᵐ[P] P[Z | F t])
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖X t ω‖ ≤ C)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => X t ω)) (s : ℝ≥0) :
    X s =ᵐ[P] P[Z | F.rightCont s] := by
  apply condExp_rightCont_of_L1_rightContinuous hZ had hversion _ s
  intro u
  exact (tendsto_L1_of_ae_continuous_bounded
    (fun t => integrable_condExp.congr (hversion t).symm) hbound hcont u).mono_left
    nhdsWithin_le_nhds

end Problem367

end

end OAI
