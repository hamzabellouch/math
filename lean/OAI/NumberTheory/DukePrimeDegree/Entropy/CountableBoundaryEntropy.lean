import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableObservationInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaLimit
import OAI.NumberTheory.PrimePackets.FiniteGeneratingObservations

namespace OAI

/-! # A countable boundary label has sublinear information cost

Finite clipping controls the information in a single countable label,
even when that label has infinite Shannon entropy. The clipping error
depends only on its tail probability and the alphabet of the observed
word, rather than on the entropy of the countable label.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem heightClip_sigma_monotone {Y : Type*} (Q : Y → ℕ) :
    Monotone (fun L => observationSigma (heightClip Q L)) := by
  intro L J hLJ
  let f : Fin (J+1) → Fin (L+1) := fun a =>
    ⟨min a.val L,Nat.lt_succ_of_le (min_le_right _ _)⟩
  have he : heightClip Q L = f ∘ heightClip Q J := by
    funext y
    apply Fin.ext
    change min (Q y) L=min (min (Q y) J) L
    omega
  change observationSigma (heightClip Q L) ≤ observationSigma (heightClip Q J)
  rw [he]
  exact observationSigma_comp_le (heightClip Q J) f

theorem heightClip_sigma_generate {Y : Type*} (Q : Y → ℕ) :
    (⨆ L, observationSigma (heightClip Q L)) =
      MeasurableSpace.comap Q inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace Y := MeasurableSpace.comap Q inferInstance
    have hQ : Measurable Q := comap_measurable Q
    exact iSup_le fun L => observationSigma_le _
      (fun a => heightClip_measurable hQ L (measurableSet_singleton a))
  · let : MeasurableSpace Y := ⨆ L, observationSigma (heightClip Q L)
    have hQ : Measurable Q := by
      apply measurable_to_countable'
      intro a
      have hc : Measurable (heightClip Q (a+1)) := by
        apply measurable_to_countable'
        intro b
        exact (le_iSup (fun L => observationSigma (heightClip Q L)) (a+1))
          _ ⟨{b},trivial,rfl⟩
      have he : {y | Q y=a} =
          {y | (heightClip Q (a+1) y).val=a} := by
        ext y
        change Q y=a ↔ min (Q y) (a+1)=a
        omega
      change MeasurableSet {y | Q y=a}
      rw [he]
      exact measurableSet_eq_fun
        ((measurable_of_finite (fun b : Fin (a+2) => b.val)).comp hc) measurable_const
    exact hQ.comap_le

theorem conditional_heightClip_tendsto {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun L => conditionalObservationEntropy μ P (heightClip Q L)) atTop
      (𝓝 (conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance))) := by
  have H := conditionalObservationEntropy_tendsto_sigma μ P hP (heightClip Q)
    (fun L a => heightClip_measurable hQ L (measurableSet_singleton a))
    (heightClip_sigma_monotone Q)
  rwa [heightClip_sigma_generate] at H

private theorem conditional_heightClip_le_larger {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) {L J : ℕ} (hLJ : L ≤ J) :
    conditionalObservationEntropy μ P (heightClip Q L) ≤
      conditionalObservationEntropy μ P (heightClip Q J) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
  let F (M : ℕ) (y : Y) :=
    finiteShannon (fun a => observationConditionalProbability μ P (heightClip Q M) a y)
  have hFint (M : ℕ) : Integrable (F M) μ :=
    integrable_finite_values μ (heightClip Q M)
      (fun a => heightClip_measurable hQ M (measurableSet_singleton a))
      (fun b => finiteShannon (fun a =>
        μ.real {y | (heightClip Q M y,P y)=(b,a)} /
          μ.real {y | heightClip Q M y=b}))
  have hB : MeasurableSet {y | L ≤ Q y} := hQ measurableSet_Ici
  have hbound : F L ≤ᵐ[μ] fun y => F J y +
      {y | L ≤ Q y}.indicator (fun _ => Real.log (Fintype.card α)) y := by
    filter_upwards [observationConditionalProbability_ae_sum μ P (heightClip Q L) hP
      (fun a => heightClip_measurable hQ L (measurableSet_singleton a)),
      observationConditionalProbability_ae_sum μ P (heightClip Q J) hP
      (fun a => heightClip_measurable hQ J (measurableSet_singleton a))] with y hyL hyJ
    by_cases hy : L ≤ Q y
    · rw [Set.indicator_of_mem (show y ∈ {y | L ≤ Q y} from hy)]
      have hlow : 0 ≤ F J y := finiteShannon_nonneg
        (fun a => observationConditionalProbability_nonneg μ P (heightClip Q J) a y) hyJ
      have hu : F L y ≤ Real.log (Fintype.card α) := finiteShannon_le_log_card
        (fun a => observationConditionalProbability_nonneg μ P (heightClip Q L) a y) hyL
      linarith
    · have hyL' : Q y < L := Nat.lt_of_not_ge hy
      have hyJ' : Q y < J := lt_of_lt_of_le hyL' hLJ
      have he : F L y=F J y := by
        apply congrArg finiteShannon
        funext a
        unfold observationConditionalProbability
        have hnum (M : ℕ) (hM : Q y < M) :
            {z | (heightClip Q M z,P z)=(heightClip Q M y,a)} =
              {z | Q z=Q y ∧ P z=a} := by
          ext z
          simp only [Prod.mk.injEq,Set.mem_ofPred_eq]
          have hh := Set.ext_iff.mp (heightClip_atom_eq_of_lt Q y hM) z
          exact and_congr_left fun _ => hh
        rw [hnum L hyL',hnum J hyJ',heightClip_atom_eq_of_lt Q y hyL',
          heightClip_atom_eq_of_lt Q y hyJ']
      rw [Set.indicator_of_notMem (show y ∉ {y | L ≤ Q y} from hy),he,add_zero]
  rw [conditionalObservationEntropy_eq_integral μ P (heightClip Q L) hP
    (fun a => heightClip_measurable hQ L (measurableSet_singleton a)),
    conditionalObservationEntropy_eq_integral μ P (heightClip Q J) hP
    (fun a => heightClip_measurable hQ J (measurableSet_singleton a))]
  have H := integral_mono_ae (hFint L)
    ((hFint J).add ((integrable_const _).indicator hB)) hbound
  simp only [Pi.add_apply] at H
  rw [integral_add (hFint J) ((integrable_const _).indicator hB),
    integral_indicator_const _ hB,smul_eq_mul] at H
  exact H

/-- Removing a finite clipping of the conditioning label changes entropy
only on the clipped tail. -/
theorem conditional_heightClip_le_countable {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) (L : ℕ) :
    conditionalObservationEntropy μ P (heightClip Q L) ≤
      conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
  apply ge_of_tendsto ((conditional_heightClip_tendsto μ P hP Q hQ).add_const _)
  filter_upwards [eventually_ge_atTop L] with J hLJ
  exact conditional_heightClip_le_larger μ P hP Q hQ hLJ

theorem observationEntropy_le_countable_conditioning {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) (L : ℕ) :
    observationEntropy μ P ≤ Real.log (L+1) +
      conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
  have hC a := heightClip_measurable hQ L (measurableSet_singleton a)
  have hjoint := observationEntropy_le_add_conditional μ P (heightClip Q L) hP hC
  have hcard := finiteShannon_le_log_card (fun a =>
    measureReal_nonneg (μ := μ) (s := {y | heightClip Q L y=a}))
    (observation_distribution_sum μ (heightClip Q L) hC)
  have htail := conditional_heightClip_le_countable μ P hP Q hQ L
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hcard
  change observationEntropy μ (heightClip Q L) ≤ _ at hcard
  linarith

theorem conditional_countable_le_observationEntropy {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap Q inferInstance) ≤
      observationEntropy μ P := by
  apply le_of_tendsto (conditional_heightClip_tendsto μ P hP Q hQ)
  exact Eventually.of_forall fun L => conditionalObservationEntropy_le μ P
    (heightClip Q L) hP
    (fun a => heightClip_measurable hQ L (measurableSet_singleton a))

theorem countable_tail_measureReal_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun L => μ.real {y | L ≤ Q y}) atTop (𝓝 0) := by
  have he : (⋂ L : ℕ, {y | L ≤ Q y}) = ∅ := by
    ext y
    simp only [mem_iInter,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro h
    exact Nat.not_succ_le_self (Q y) (h (Q y+1))
  have H := tendsto_measure_iInter_atTop
    (μ := μ) (fun L => (hQ measurableSet_Ici).nullMeasurableSet)
    (show Antitone (fun L => {y | L ≤ Q y}) from fun L J h y hy => h.trans hy)
    ⟨0,measure_ne_top _ _⟩
  change Tendsto (fun L => μ {y | L ≤ Q y}) atTop
    (𝓝 (μ (⋂ L : ℕ, {y | L ≤ Q y}))) at H
  rw [he,measure_empty] at H
  simpa only [measureReal_def,ENNReal.toReal_zero,Function.comp_def] using
    (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp H

/-- A single countable observation at the end of an orbit word carries
sublinear information about that word. Its Shannon entropy may be infinite. -/
theorem countable_boundary_information_sublinear {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun N : ℕ =>
      (observationEntropy μ (orbitName T P N) -
        conditionalSigmaEntropy μ (orbitName T P N)
          (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance)) / N)
      atTop (𝓝 0) := by
  let E (N : ℕ) := observationEntropy μ (orbitName T P N) -
    conditionalSigmaEntropy μ (orbitName T P N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance)
  have hE (N : ℕ) : 0 ≤ E N := sub_nonneg.mpr
    (conditional_countable_le_observationEntropy μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) (Q ∘ T^[N])
      (hQ.comp (hT.measurable.iterate N)))
  have hbound (L N : ℕ) :
      E N ≤ Real.log (L+1) + μ.real {y | L ≤ Q y} *
        ((N : ℝ) * Real.log (Fintype.card α)) := by
    have H := observationEntropy_le_countable_conditioning μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable hP N) (Q ∘ T^[N])
      (hQ.comp (hT.measurable.iterate N)) L
    have htail : μ.real {y | L ≤ (Q ∘ T^[N]) y} = μ.real {y | L ≤ Q y} :=
      (hT.iterate N).measureReal_preimage (hQ measurableSet_Ici).nullMeasurableSet
    rw [htail,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at H
    dsimp only [E]
    linarith
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun L => μ.real {y | L ≤ Q y} *
      Real.log (Fintype.card α)) atTop (𝓝 0) := by
    simpa using (countable_tail_measureReal_tendsto_zero μ Q hQ).mul_const
      (Real.log (Fintype.card α))
  obtain ⟨L,hL⟩ := (ht.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))).exists
  have hl : Tendsto (fun N : ℕ => Real.log (L+1)/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hl.eventually (gt_mem_nhds (show 0 < ε/2 by positivity)),
    eventually_ge_atTop (1 : ℕ)] with N hlog hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have he : E N/(N : ℝ) ≤ Real.log (L+1)/(N : ℝ) +
      μ.real {y | L ≤ Q y} * Real.log (Fintype.card α) := by
    apply (div_le_iff₀ hn).mpr
    have hh := hbound L N
    have heq : (Real.log (L+1)/(N : ℝ) +
        μ.real {y | L ≤ Q y} * Real.log (Fintype.card α)) * N =
        Real.log (L+1) + μ.real {y | L ≤ Q y} *
          ((N : ℝ) * Real.log (Fintype.card α)) := by
      field_simp
    rwa [heq]
  change dist (E N/(N : ℝ)) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hE N) hn.le)]
  linarith

theorem conditional_boundary_entropy_rate {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a})
    (Q : Y → ℕ) (hQ : Measurable Q) :
    Tendsto (fun N : ℕ => conditionalSigmaEntropy μ (orbitName T P N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) / N) atTop
      (𝓝 (observationEntropyRate μ T P)) := by
  have H := (tendsto_observationEntropyRate μ hT P hP).sub
    (countable_boundary_information_sublinear μ hT P hP Q hQ)
  simp only [sub_zero] at H
  convert H using 1
  funext N
  rw [sub_div]
  ring

end DukePrimeDegree

end

end OAI
