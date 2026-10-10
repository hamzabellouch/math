import OAI.Probability.FreeIsing.Brownian.ArrayLaw
import OAI.Probability.FreeIsing.Estimates.BoundedInnovationDrift
import OAI.Probability.FreeIsing.Factors.ContinuousRecovery

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem stronglyMeasurable_joint_of_isStronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    StronglyMeasurable (fun p : ℝ≥0 × Ω => m p.1 p.2) := by
  have hstop (n : ℕ) : StronglyMeasurable
      (fun p : ℝ≥0 × Ω => m (min p.1 (n : ℝ≥0)) p.2) := by
    have hlocal : StronglyMeasurable[
        @MeasurableSpace.prod ℝ≥0 Ω inferInstance (F n)]
        (fun p : ℝ≥0 × Ω => m (min p.1 (n : ℝ≥0)) p.2) := by
      let : MeasurableSpace Ω := F n
      have htime : Measurable (fun t : ℝ≥0 =>
          (⟨min t (n : ℝ≥0), by simp⟩ : Set.Iic (n : ℝ≥0))) :=
        (measurable_id.min measurable_const).subtype_mk
      exact (hm n).comp_measurable ((htime.comp measurable_fst).prodMk measurable_snd)
    exact hlocal.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le n)))
  apply stronglyMeasurable_of_tendsto atTop hstop
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge p.1
  filter_upwards [eventually_ge_atTop N] with n hn
  have hpn : p.1 ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn)
  simp [min_eq_left hpn]

theorem measurable_nnrealTimePrimitive_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (t : ℝ≥0) :
    Measurable (nnrealTimePrimitive m t) := by
  have hj : StronglyMeasurable (fun p : ℝ × Ω => m p.1.toNNReal p.2) :=
    (stronglyMeasurable_joint_of_isStronglyProgressive hm).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  change Measurable (fun ω => ∫ r in (0 : ℝ)..(t : ℝ), m r.toNNReal ω)
  simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using
    (hj.integral_prod_left' (μ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)))).measurable

theorem nnrealTimePrimitive_congr_on_Iic
    {Ω Ω' : Type*} {m : ℝ≥0 → Ω → ℝ} {m' : ℝ≥0 → Ω' → ℝ}
    {ω : Ω} {ω' : Ω'} {t : ℝ≥0}
    (h : ∀ s ≤ t, m s ω = m' s ω') :
    nnrealTimePrimitive m t ω = nnrealTimePrimitive m' t ω' := by
  simp only [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact h _ (Real.toNNReal_le_iff_le_coe.mpr hr.2)

def innovationPath
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} (X : Ω → C(ℝ≥0, ℝ))
    (m : ℝ≥0 → Ω → ℝ) (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (ω : Ω) :
    C(ℝ≥0, ℝ) :=
  ⟨fun t => X ω t - nnrealTimePrimitive m t ω,
    (X ω).continuous.sub (lipschitzWith_nnrealTimePrimitive_of_progressive hm hbound ω).continuous⟩

@[simp] theorem innovationPath_apply
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} (X : Ω → C(ℝ≥0, ℝ))
    (m : ℝ≥0 → Ω → ℝ) (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (ω : Ω) (t : ℝ≥0) :
    innovationPath X m hm hbound ω t = X ω t - nnrealTimePrimitive m t ω := rfl

@[simp] theorem innovationPath_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} (X : Ω → C(ℝ≥0, ℝ))
    (m : ℝ≥0 → Ω → ℝ) (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (ω : Ω) :
    innovationPath X m hm hbound ω 0 = X ω 0 := by
  simp [innovationPath, nnrealTimePrimitive]

theorem measurable_innovationPath
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    [StandardBorelSpace C(ℝ≥0, ℝ)]
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → C(ℝ≥0, ℝ)}
    {m : ℝ≥0 → Ω → ℝ} (hm : IsStronglyProgressive F m)
    {K : ℝ≥0} (hbound : ∀ t ω, ‖m t ω‖ ≤ (K : ℝ)) (hX : Measurable X) :
    Measurable (innovationPath X m hm hbound) := by
  apply measurable_continuousPath_of_evaluations
  intro t
  exact ((continuous_eval_const t).measurable.comp hX).sub
    (measurable_nnrealTimePrimitive_of_progressive hm t)

theorem measurable_innovationPath_array
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    [StandardBorelSpace C(ℝ≥0, ℝ)]
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, IsStronglyProgressive F (m i))
    {K : ℝ≥0} (hbound : ∀ i t ω, ‖m i t ω‖ ≤ (K : ℝ)) (hX : Measurable X) :
    Measurable (fun ω i => innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) ω) := by
  apply Measurable.of_eval
  intro i
  exact measurable_innovationPath (hm i) (hbound i) ((measurable_pi_apply i).comp hX)

theorem innovationPath_array_equivariant
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, IsStronglyProgressive F (m i))
    {K : ℝ≥0} (hbound : ∀ i t ω, ‖m i t ω‖ ≤ (K : ℝ))
    (T : Ω → Ω) (e : ι → ι)
    (hX : ∀ ω i, X (T ω) i = X ω (e i))
    (hpost : ∀ ω i t, m i t (T ω) = m (e i) t ω) (ω : Ω) (i : ι) :
    innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) (T ω) =
      innovationPath (fun ω => X ω (e i)) (m (e i)) (hm (e i)) (hbound (e i)) ω := by
  ext t
  simp only [innovationPath_apply, hX]
  congr 1
  exact nnrealTimePrimitive_congr_on_Iic (fun s _ => hpost ω i s)

theorem innovationPath_array_causal
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, IsStronglyProgressive F (m i))
    {K : ℝ≥0} (hbound : ∀ i t ω, ‖m i t ω‖ ≤ (K : ℝ))
    (hcausal : ∀ T ω ω',
      (∀ i s, s ≤ T → X ω i s = X ω' i s) →
      ∀ i s, s ≤ T → m i s ω = m i s ω')
    {T : ℝ≥0} {ω ω' : Ω}
    (hpast : ∀ i s, s ≤ T → X ω i s = X ω' i s) :
    ∀ i s, s ≤ T →
      innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) ω s =
        innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) ω' s := by
  intro i s hs
  simp only [innovationPath_apply, hpast i s hs]
  congr 1
  exact nnrealTimePrimitive_congr_on_Iic
    (fun r hr => hcausal T ω ω' hpast i r (hr.trans hs))

theorem nnrealTimePrimitive_ae_eq_of_jointlyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {m m' : ℝ≥0 → Ω → ℝ}
    (hm : Measurable (fun p : ℝ≥0 × Ω => m p.1 p.2))
    (hm' : Measurable (fun p : ℝ≥0 × Ω => m' p.1 p.2))
    (heq : ∀ s, m s =ᵐ[P] m' s) (t : ℝ≥0) :
    nnrealTimePrimitive m t =ᵐ[P] nnrealTimePrimitive m' t := by
  have hj : Measurable (fun p : ℝ × Ω => m p.1.toNNReal p.2) :=
    hm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hj' : Measurable (fun p : ℝ × Ω => m' p.1.toNNReal p.2) :=
    hm'.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hswap : ∀ᵐ ω ∂P, ∀ᵐ r ∂volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)),
      m r.toNNReal ω = m' r.toNNReal ω :=
    (Measure.ae_ae_comm
      (μ := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ))) (ν := P)
      (p := fun r ω => m r.toNNReal ω = m' r.toNNReal ω)
      (measurableSet_eq_fun hj hj')).mp
      (Filter.Eventually.of_forall (fun (r : ℝ) => heq r.toNNReal))
  filter_upwards [hswap] with ω hω
  simp only [nnrealTimePrimitive, intervalIntegral.integral_of_le t.coe_nonneg]
  exact integral_congr_ae hω

theorem innovationPath_array_ae_equivariant
    {ι Ω : Type*} [Countable ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, IsStronglyProgressive F (m i))
    {K : ℝ≥0} (hbound : ∀ i t ω, ‖m i t ω‖ ≤ (K : ℝ))
    (T : Ω → Ω) (hT : Measurable T) (e : ι → ι)
    (hX : ∀ i, (fun ω => X (T ω) i) =ᵐ[P] (fun ω => X ω (e i)))
    (hpost : ∀ i t, (fun ω => m i t (T ω)) =ᵐ[P] m (e i) t) :
    ∀ᵐ ω ∂P, ∀ i,
      innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) (T ω) =
        innovationPath (fun ω => X ω (e i)) (m (e i)) (hm (e i)) (hbound (e i)) ω := by
  apply ae_all_iff.mpr
  intro i
  have hprim (t : ℝ≥0) :
      nnrealTimePrimitive (fun s ω => m i s (T ω)) t =ᵐ[P]
        nnrealTimePrimitive (m (e i)) t := by
    apply nnrealTimePrimitive_ae_eq_of_jointlyMeasurable
    · exact (stronglyMeasurable_joint_of_isStronglyProgressive (hm i)).measurable.comp
        (measurable_fst.prodMk (hT.comp measurable_snd))
    · exact (stronglyMeasurable_joint_of_isStronglyProgressive (hm (e i))).measurable
    · exact hpost i
  have hpaths := ae_eq_of_continuous_of_evaluation_ae_eq
    (μ := P)
    (f := fun ω t => innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) (T ω) t)
    (g := fun ω t => innovationPath (fun ω => X ω (e i)) (m (e i))
      (hm (e i)) (hbound (e i)) ω t)
    (Filter.Eventually.of_forall (fun ω => (innovationPath _ _ _ _ (T ω)).continuous))
    (Filter.Eventually.of_forall (fun ω => (innovationPath _ _ _ _ ω).continuous))
    (fun t => ?_)
  · filter_upwards [hpaths] with ω hω
    exact ContinuousMap.coe_injective hω
  · filter_upwards [hX i, hprim t] with ω hx hp
    change X (T ω) i t - nnrealTimePrimitive (fun s ω => m i s (T ω)) t ω =
      X ω (e i) t - nnrealTimePrimitive (m (e i)) t ω
    rw [hx, hp]

theorem stronglyAdapted_causal_of_past_comap
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, StronglyAdapted F (m i))
    (hF : ∀ t, F t ≤ MeasurableSpace.comap
      (fun ω i (s : Set.Iic t) => X ω i s) inferInstance)
    {T : ℝ≥0} {ω ω' : Ω}
    (hpast : ∀ i s, s ≤ T → X ω i s = X ω' i s) :
    ∀ i s, s ≤ T → m i s ω = m i s ω' := by
  intro i s hs
  have hms : StronglyMeasurable[MeasurableSpace.comap
      (fun ω i (r : Set.Iic s) => X ω i r) inferInstance] (m i s) :=
    (hm i s).mono (hF s)
  obtain ⟨f, _, hf⟩ := hms.exists_eq_measurable_comp
  have hx : (fun i (r : Set.Iic s) => X ω i r) =
      (fun i (r : Set.Iic s) => X ω' i r) := by
    funext j r
    exact hpast j r (r.property.trans hs)
  rw [hf]
  exact congrArg f hx

theorem innovationPath_array_causal_of_past_comap
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {X : Ω → ι → C(ℝ≥0, ℝ)}
    {m : ι → ℝ≥0 → Ω → ℝ} (hm : ∀ i, IsStronglyProgressive F (m i))
    {K : ℝ≥0} (hbound : ∀ i t ω, ‖m i t ω‖ ≤ (K : ℝ))
    (hF : ∀ t, F t ≤ MeasurableSpace.comap
      (fun ω i (s : Set.Iic t) => X ω i s) inferInstance)
    {T : ℝ≥0} {ω ω' : Ω}
    (hpast : ∀ i s, s ≤ T → X ω i s = X ω' i s) :
    ∀ i s, s ≤ T →
      innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) ω s =
        innovationPath (fun ω => X ω i) (m i) (hm i) (hbound i) ω' s :=
  innovationPath_array_causal hm hbound
    (fun _ _ _ h => stronglyAdapted_causal_of_past_comap
      (fun i => (hm i).stronglyAdapted) hF h) hpast

end Problem367

end

end OAI
