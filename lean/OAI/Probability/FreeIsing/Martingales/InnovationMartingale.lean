import OAI.Probability.FreeIsing.Conditioning.Fubini

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem martingale_increment_condExp_subfiltration
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F G : Filtration ι mΩ}
    {B : ι → Ω → ℝ} (hB : Martingale B G P)
    (hFG : ∀ t, F t ≤ G t) {s t : ι} (hst : s ≤ t) :
    P[B t - B s | F s] =ᵐ[P] fun _ => 0 := by
  have hGB : P[B t - B s | G s] =ᵐ[P] fun _ => 0 := by
    have hsub := condExp_sub (hB.integrable t) (hB.integrable s) (G s)
    filter_upwards [hsub, hB.condExp_ae_eq hst, hB.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
    simpa only [Pi.sub_def, h2, h3, sub_self] using h1
  calc
    P[B t - B s | F s] =ᵐ[P] P[P[B t - B s | G s] | F s] :=
      (condExp_condExp_of_le (hFG s) (G.le s)).symm
    _ =ᵐ[P] P[(fun _ : Ω => (0 : ℝ)) | F s] := condExp_congr_ae hGB
    _ =ᵐ[P] fun _ => 0 := by simp

theorem observation_increment_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[(fun ω => (B t ω + (t : ℝ) * σ ω) - (B s ω + (s : ℝ) * σ ω)) | F s] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) * P[σ | F s] ω := by
  have hfun : (fun ω => (B t ω + (t : ℝ) * σ ω) - (B s ω + (s : ℝ) * σ ω)) =
      (B t - B s) + (((t : ℝ) - (s : ℝ)) • σ) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  have hadd := condExp_add ((hB.integrable t).sub (hB.integrable s))
    (hσ.const_mul ((t : ℝ) - (s : ℝ))) (F s)
  have hscale := condExp_smul (μ := P) ((t : ℝ) - (s : ℝ)) σ (F s)
  have hzero := martingale_increment_condExp_subfiltration hB hFG hst
  filter_upwards [hadd, hscale, hzero] with ω ha hc hz
  simp only [Pi.add_def, Pi.smul_def, smul_eq_mul] at ha hc ⊢
  rw [hc, hz, zero_add] at ha
  exact ha

theorem condExp_nnrealIntervalIntegral_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ} (hm : Martingale m F P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    P[(fun ω => ∫ u in (s : ℝ)..(t : ℝ), m u.toNNReal ω) | F s] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) * m s ω := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))
  have hGm : StronglyMeasurable[@MeasurableSpace.prod ℝ Ω inferInstance (F s)]
      (fun p : ℝ × Ω => m s p.2) := by
    let : MeasurableSpace Ω := F s
    exact (hm.stronglyMeasurable s).comp_measurable measurable_snd
  have hcond : ∀ᵐ u ∂ν, (fun ω => m s ω) =ᵐ[P]
      P[(fun ω => m u.toNNReal ω) | F s] := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    apply (hm.condExp_ae_eq ?_).symm
    simpa using Real.toNNReal_mono hu.1.le
  have h := integral_of_conditional_versions (F s) ν P (F.le s)
    hInt ((hm.integrable s).comp_snd ν) hGm hcond
  simpa [ν, Real.volume_real_Ioc_of_le (show (s : ℝ) ≤ (t : ℝ) from hst),
    intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)] using h.symm

noncomputable def nnrealTimePrimitive {Ω : Type*} (m : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := ∫ u in (0 : ℝ)..(t : ℝ), m u.toNNReal ω

theorem nnrealTimePrimitive_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    (hInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))).prod P)) :
    Integrable (nnrealTimePrimitive m t) P := by
  change Integrable (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), m u.toNNReal ω) P
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hInt.integral_prod_right

theorem nnrealTimePrimitive_increment_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {m : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s ≤ t)
    (h0s : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (s : ℝ))).prod P))
    (hstInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    nnrealTimePrimitive m t - nnrealTimePrimitive m s =ᵐ[P]
      fun ω => ∫ u in (s : ℝ)..(t : ℝ), m u.toNNReal ω := by
  filter_upwards [h0s.prod_left_ae, hstInt.prod_left_ae] with ω h0sω hstω
  have hi0s := (intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg).mpr h0sω
  have hist := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (s : ℝ) ≤ (t : ℝ) from hst)).mpr hstω
  have h := intervalIntegral.integral_add_adjacent_intervals hi0s hist
  dsimp [nnrealTimePrimitive]
  linarith

theorem nnrealTimePrimitive_increment_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 mΩ) {m : ℝ≥0 → Ω → ℝ} (hm : Martingale m F P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (h0s : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (s : ℝ))).prod P))
    (hstInt : Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
      ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    P[nnrealTimePrimitive m t - nnrealTimePrimitive m s | F s] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) * m s ω :=
  (condExp_congr_ae (nnrealTimePrimitive_increment_ae hst h0s hstInt)).trans
    (condExp_nnrealIntervalIntegral_martingale P F hm hst hstInt)

theorem martingale_of_conditional_increment_zero
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {W : ι → Ω → ℝ} (had : StronglyAdapted F W) (hint : ∀ t, Integrable (W t) P)
    (hzero : ∀ s t, s ≤ t → P[W t - W s | F s] =ᵐ[P] fun _ => 0) :
    Martingale W F P := by
  refine ⟨had, ?_⟩
  intro s t hst
  have hs : P[W s | F s] = W s := condExp_of_stronglyMeasurable (F.le s) (had s) (hint s)
  have hd := condExp_sub (hint t) (hint s) (F s)
  filter_upwards [hd, hzero s t hst] with ω hd hz
  rw [hs] at hd
  simp only [Pi.sub_apply] at hd
  rw [hz] at hd
  linarith

theorem compensated_observation_martingale_of_posterior_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hmAd : StronglyAdapted F m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t])
    (hAad : StronglyAdapted F (nnrealTimePrimitive m))
    (hInt : ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
        ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive m t ω) F P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω => B t ω + (t : ℝ) * σ ω
  let A := nnrealTimePrimitive m
  have hXint (t : ℝ≥0) : Integrable (X t) P :=
    (hB.integrable t).add (hσ.const_mul (t : ℝ))
  have hAint (t : ℝ≥0) : Integrable (A t) P :=
    nnrealTimePrimitive_integrable (hInt 0 t (by positivity))
  apply martingale_of_conditional_increment_zero (hXad.sub hAad)
    (fun t => (hXint t).sub (hAint t))
  intro s t hst
  have hXce := observation_increment_condExp hB hFG hσ hst
  have hm : Martingale m F P := (martingale_condExp σ F P).congr hmAd
    (fun t => (hposterior t).symm)
  have hAce := nnrealTimePrimitive_increment_condExp P F hm hst
    (hInt 0 s (by positivity)) (hInt s t hst)
  have hfun :
      ((fun ω => X t ω - A t ω) - (fun ω => X s ω - A s ω)) =
      (X t - X s) - (A t - A s) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  change P[(fun ω => X t ω - A t ω) - (fun ω => X s ω - A s ω) | F s] =ᵐ[P] _
  rw [hfun]
  have hd := condExp_sub ((hXint t).sub (hXint s)) ((hAint t).sub (hAint s)) (F s)
  filter_upwards [hd, hXce, hAce, hposterior s] with ω hd hx ha hmω
  change P[X t - X s | F s] ω = ((t : ℝ) - (s : ℝ)) * P[σ | F s] ω at hx
  change P[A t - A s | F s] ω = ((t : ℝ) - (s : ℝ)) * m s ω at ha
  rw [hmω] at ha
  simpa only [Pi.sub_apply, hx, ha, sub_self] using hd

theorem compensated_observation_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hB : Martingale B G P) (hFG : ∀ t, F t ≤ G t) (hσ : Integrable σ P)
    (hXad : StronglyAdapted F (fun t ω => B t ω + (t : ℝ) * σ ω))
    (hAad : StronglyAdapted F (nnrealTimePrimitive (fun t => P[σ | F t])))
    (hInt : ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun p : ℝ × Ω => P[σ | F p.1.toNNReal] p.2)
        ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    Martingale (fun t ω => B t ω + (t : ℝ) * σ ω -
      nnrealTimePrimitive (fun t => P[σ | F t]) t ω) F P :=
  compensated_observation_martingale_of_posterior_version hB hFG hσ hXad
    (fun _ => stronglyMeasurable_condExp) (fun _ => Filter.EventuallyEq.rfl) hAad hInt

end Problem367

end OAI
