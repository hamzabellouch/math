import OAI.Probability.SLE.Multipoint.MultipointPiecewiseClock

namespace OAI

/-! Each completed multipoint coordinate is frozen at its own stopping
time. The finite vector remains an adapted Lipschitz state, with the
expected stopped velocity almost everywhere in time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

def stoppedCoordinateState {Ω ι : Type*}
    (Q : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0) (t : ℝ) (ω : Ω) (i : ι) : ℂ × ℝ :=
  Q (min t (τ i ω : ℝ)) ω i

def stoppedCoordinateVelocity {Ω ι : Type*}
    (V : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0) (t : ℝ) (ω : Ω) (i : ι) : ℂ × ℝ :=
  if t < (τ i ω : ℝ) then V t ω i else 0

lemma stoppedCoordinateState_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Q : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0)
    (hQ : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hτ : ∀ i, Measurable (τ i)) :
    Measurable (fun p : ℝ × Ω => stoppedCoordinateState Q τ p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  have hQi : Measurable (fun p : ℝ × Ω => Q p.1 p.2 i) :=
    (measurable_pi_apply i).comp hQ
  have htime : Measurable (fun p : ℝ × Ω => min p.1 (τ i p.2 : ℝ)) :=
    measurable_fst.min (NNReal.continuous_coe.measurable.comp ((hτ i).comp measurable_snd))
  exact hQi.comp (htime.prodMk measurable_snd)

lemma stoppedCoordinateVelocity_measurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (V : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0)
    (hV : Measurable (fun p : ℝ × Ω => V p.1 p.2))
    (hτ : ∀ i, Measurable (τ i)) :
    Measurable (fun p : ℝ × Ω => stoppedCoordinateVelocity V τ p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.ite _ ((measurable_pi_apply i).comp hV) measurable_const
  exact measurableSet_lt measurable_fst
    (NNReal.continuous_coe.measurable.comp ((hτ i).comp measurable_snd))

lemma stoppedCoordinateState_lipschitz {Ω ι : Type*} [Fintype ι]
    (Q : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0) (L : ℝ≥0)
    (hQ : ∀ ω, LipschitzWith L (fun t => Q t ω)) (ω : Ω) :
    LipschitzWith L (fun t => stoppedCoordinateState Q τ t ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  apply (dist_pi_le_iff (mul_nonneg L.coe_nonneg dist_nonneg)).mpr
  intro i
  have hmin := (LipschitzWith.id.min_const (τ i ω : ℝ)).dist_le_mul t u
  calc
    dist (Q (min t (τ i ω : ℝ)) ω i) (Q (min u (τ i ω : ℝ)) ω i) ≤
        dist (Q (min t (τ i ω : ℝ)) ω) (Q (min u (τ i ω : ℝ)) ω) :=
      dist_le_pi_dist _ _ i
    _ ≤ (L : ℝ) * dist (min t (τ i ω : ℝ)) (min u (τ i ω : ℝ)) :=
      (hQ ω).dist_le_mul _ _
    _ ≤ (L : ℝ) * dist t u := by
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      simpa only [NNReal.coe_one, one_mul, id_eq] using hmin

lemma stoppedCoordinateVelocity_bound {Ω ι : Type*} [Fintype ι]
    (V : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0) (L : ℝ≥0)
    (hV : ∀ t ω, ‖V t ω‖ ≤ L) (t : ℝ) (ω : Ω) :
    ‖stoppedCoordinateVelocity V τ t ω‖ ≤ L := by
  apply (pi_norm_le_iff_of_nonneg L.coe_nonneg).mpr
  intro i
  unfold stoppedCoordinateVelocity
  split_ifs
  · exact (norm_le_pi_norm (V t ω) i).trans (hV t ω)
  · simpa only [norm_zero] using L.coe_nonneg

lemma stoppedCoordinateState_ae_derivative {Ω ι : Type*} [Fintype ι]
    (Q V : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0)
    (hQd : ∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => Q u ω) (V t ω) t)
    (ω : Ω) : ∀ᵐ t : ℝ, 0 < t →
      HasDerivAt (fun u => stoppedCoordinateState Q τ u ω)
        (stoppedCoordinateVelocity V τ t ω) t := by
  have hne : ∀ᵐ t : ℝ, ∀ i, t ≠ (τ i ω : ℝ) :=
    ae_all_iff.mpr (fun i => volume.ae_ne (τ i ω : ℝ))
  filter_upwards [hQd ω, hne] with t ht hne
  intro ht0
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hti : t < (τ i ω : ℝ)
  · have hd := hasDerivAt_pi.mp (ht ht0) i
    have he : (fun u => stoppedCoordinateState Q τ u ω i) =ᶠ[𝓝 t] (fun u => Q u ω i) := by
      filter_upwards [eventually_lt_nhds hti] with u hu
      simp only [stoppedCoordinateState, min_eq_left hu.le]
    simpa only [stoppedCoordinateVelocity, ite_eq_left hti] using hd.congr_of_eventuallyEq he
  · have hit : (τ i ω : ℝ) < t := lt_of_le_of_ne (le_of_not_gt hti) (hne i).symm
    have he : (fun u => stoppedCoordinateState Q τ u ω i) =ᶠ[𝓝 t]
        (fun _ => Q (τ i ω : ℝ) ω i) := by
      filter_upwards [eventually_gt_nhds hit] with u hu
      simp only [stoppedCoordinateState, min_eq_right hu.le]
    simpa only [stoppedCoordinateVelocity, ite_eq_right hti] using
      (hasDerivAt_const t (Q (τ i ω : ℝ) ω i)).congr_of_eventuallyEq he

lemma stoppedCoordinateState_adapted {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (ℱ : Filtration ℝ≥0 mΩ) (Q : ℝ → Ω → ι → ℂ × ℝ)
    (τ : ι → Ω → ℝ≥0) (L : ℝ≥0)
    (hQa : Adapted ℱ (fun t : ℝ≥0 => Q t))
    (hQl : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (hτ : ∀ i, IsStoppingTime ℱ (fun ω => (τ i ω : WithTop ℝ≥0))) :
    Adapted ℱ (fun t : ℝ≥0 => stoppedCoordinateState Q τ t) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  apply Measurable.of_eval
  intro i
  have hQi : StronglyAdapted ℱ (fun t : ℝ≥0 => fun ω => Q t ω i) := fun u =>
    ((measurable_pi_apply i).comp (hQa u)).stronglyMeasurable
  have hQc (ω : Ω) : Continuous (fun u : ℝ≥0 => Q u ω i) :=
    ((continuous_apply i).comp (hQl ω).continuous).comp NNReal.continuous_coe
  have hs := ((hQi.stoppedProcess hQc (hτ i)) t).measurable
  convert hs using 1
  funext ω
  simp only [stoppedCoordinateState, MeasureTheory.stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA, WithTop.untopD_coe, NNReal.coe_min]

@[simp] lemma stoppedCoordinateState_initial {Ω ι : Type*}
    (Q : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0) (ω : Ω) :
    stoppedCoordinateState Q τ 0 ω = Q 0 ω := by
  funext i
  simp only [stoppedCoordinateState, min_eq_left (τ i ω).coe_nonneg]

lemma stoppedCoordinateState_frozen {Ω ι : Type*}
    (Q : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0)
    (t : ℝ) (ω : Ω) (i : ι) (ht : (τ i ω : ℝ) ≤ t) :
    stoppedCoordinateState Q τ t ω i = Q (τ i ω : ℝ) ω i := by
  rw [stoppedCoordinateState, min_eq_right ht]

/-- Stop each coordinate separately while preserving all state hypotheses
of the compact Brownian field adapter. -/
theorem stoppedCoordinateState_regular {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (ℱ : Filtration ℝ≥0 mΩ) (Q V : ℝ → Ω → ι → ℂ × ℝ)
    (τ : ι → Ω → ℝ≥0) (L : ℝ≥0)
    (hQm : Measurable (fun p : ℝ × Ω => Q p.1 p.2))
    (hQa : Adapted ℱ (fun t : ℝ≥0 => Q t))
    (hQl : ∀ ω, LipschitzWith L (fun t => Q t ω))
    (hVm : Measurable (fun p : ℝ × Ω => V p.1 p.2))
    (hVb : ∀ t ω, ‖V t ω‖ ≤ L)
    (hQd : ∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => Q u ω) (V t ω) t)
    (hτ : ∀ i, IsStoppingTime ℱ (fun ω => (τ i ω : WithTop ℝ≥0))) :
    Measurable (fun p : ℝ × Ω => stoppedCoordinateState Q τ p.1 p.2) ∧
    Adapted ℱ (fun t : ℝ≥0 => stoppedCoordinateState Q τ t) ∧
    (∀ ω, LipschitzWith L (fun t => stoppedCoordinateState Q τ t ω)) ∧
    Measurable (fun p : ℝ × Ω => stoppedCoordinateVelocity V τ p.1 p.2) ∧
    (∀ t ω, ‖stoppedCoordinateVelocity V τ t ω‖ ≤ L) ∧
    (∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => stoppedCoordinateState Q τ u ω)
      (stoppedCoordinateVelocity V τ t ω) t) := by
  have hτm (i : ι) : Measurable (τ i) := stopping_time_measurable_nnreal (hτ i)
  exact ⟨stoppedCoordinateState_measurable Q τ hQm hτm,
    stoppedCoordinateState_adapted ℱ Q τ L hQa hQl hτ,
    stoppedCoordinateState_lipschitz Q τ L hQl,
    stoppedCoordinateVelocity_measurable V τ hVm hτm,
    stoppedCoordinateVelocity_bound V τ L hVb,
    stoppedCoordinateState_ae_derivative Q V τ hQd⟩

end SLEExactGauge.Multipoint

end

end OAI
