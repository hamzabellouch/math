import OAI.NumberTheory.DukePrimeDegree.Entropy.RareLabelEntropy

namespace OAI

/-! # Entropy of finite names controlled by their coordinate errors -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalVectorEntropy_le_sum {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (N : ℕ)
    (P R : Y → Fin N → α) (hP : Measurable P) (hR : Measurable R) :
    conditionalObservationEntropy μ P R ≤
      ∑ i : Fin N, conditionalObservationEntropy μ (fun y => P y i) (fun y => R y i) := by
  induction N with
  | zero =>
    let : Unique ((Fin 0 → α) × (Fin 0 → α)) :=
      uniqueOfSubsingleton (default,default)
    simp only [conditionalObservationEntropy,observationEntropy_unique,sub_self,
      Fin.sum_univ_zero,le_refl]
  | succ N ih =>
    let e := (Fin.consEquiv (fun _ : Fin (N+1) => α)).symm
    let P₀ := fun y => P y 0
    let R₀ := fun y => R y 0
    let Pt := fun y (i : Fin N) => P y i.succ
    let Rt := fun y (i : Fin N) => R y i.succ
    have hp0 : Measurable P₀ := (measurable_pi_apply 0).comp hP
    have hr0 : Measurable R₀ := (measurable_pi_apply 0).comp hR
    have hpt : Measurable Pt := measurable_pi_iff.mpr fun i =>
      (measurable_pi_apply i.succ).comp hP
    have hrt : Measurable Rt := measurable_pi_iff.mpr fun i =>
      (measurable_pi_apply i.succ).comp hR
    have he : conditionalObservationEntropy μ (fun y => (P₀ y,Pt y))
        (fun y => (R₀ y,Rt y)) = conditionalObservationEntropy μ P R :=
      conditionalObservationEntropy_injective μ P R e e e.injective e.injective
    rw [←he]
    have H := conditionalObservationEntropy_pair_pair_le μ P₀ Pt R₀ Rt
      (fun a => hp0 (measurableSet_singleton a))
      (fun a => hpt (measurableSet_singleton a))
      (fun a => hr0 (measurableSet_singleton a))
      (fun a => hrt (measurableSet_singleton a))
    refine H.trans ?_
    have HH := ih Pt Rt hpt hrt
    rw [Fin.sum_univ_succ]
    exact add_le_add le_rfl HH

theorem conditionalNameEntropy_le_errors {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (N : ℕ)
    (P R : Y → Fin N → α) (hP : Measurable P) (hR : Measurable R)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    conditionalObservationEntropy μ P R ≤
      (N : ℝ)*(-Real.log (1-δ)) +
        (∑ i : Fin N, μ.real {y | P y i ≠ R y i}) *
          (Real.log (Fintype.card α)-Real.log δ) := by
  refine (conditionalVectorEntropy_le_sum μ N P R hP hR).trans ?_
  have H := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin N) _ =>
    conditionalObservationEntropy_le_error μ (fun y => P y i) (fun y => R y i)
      ((measurable_pi_apply i).comp hP) ((measurable_pi_apply i).comp hR) hδ hδ1)
  refine H.trans_eq ?_
  simp only [rareLabelCost,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Finset.sum_mul]

/-- A finite list of reference names pays its logarithmic cardinality;
the remaining cost is proportional to the expected number of errors. -/
theorem nameEntropy_le_reference_errors {Y α β : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    [Fintype α] [Nonempty α] [DecidableEq α] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ] (N : ℕ)
    (P : Y → Fin N → α) (hP : Measurable P)
    (r : Y → β) (hr : Measurable r) (v : β → Fin N → α)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (herr : (∑ i : Fin N, μ.real {y | P y i ≠ v (r y) i}) ≤ ε*N) :
    observationEntropy μ P ≤ Real.log (Fintype.card β) +
      (N : ℝ)*rareLabelCost (Fintype.card α) δ ε := by
  let R := v ∘ r
  have hR : Measurable R := (measurable_of_finite v).comp hr
  have href : observationEntropy μ R ≤ observationEntropy μ r :=
    observationEntropy_le_of_refines μ R r
      (fun a => hR (measurableSet_singleton a))
      (fun a => hr (measurableSet_singleton a))
      (fun x y h => congrArg v h)
  have hcard : observationEntropy μ r ≤ Real.log (Fintype.card β) :=
    finiteShannon_le_log_card (fun _ => measureReal_nonneg)
      (observation_distribution_sum μ r (fun a => hr (measurableSet_singleton a)))
  have hjoint := observationEntropy_le_add_conditional μ P R
    (fun a => hP (measurableSet_singleton a))
    (fun a => hR (measurableSet_singleton a))
  have he := conditionalNameEntropy_le_errors μ N P R hP hR hδ hδ1
  have hslope : 0 ≤ Real.log (Fintype.card α)-Real.log δ := by
    have hc : 1 ≤ (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    have hd : Real.log δ < 0 := Real.log_neg hδ hδ1
    linarith [Real.log_nonneg hc]
  have hm := mul_le_mul_of_nonneg_right herr hslope
  change (∑ i : Fin N, μ.real {y | P y i ≠ R y i}) * _ ≤ _ at hm
  unfold rareLabelCost
  nlinarith

theorem observationEntropyRate_le_approximate_names {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (hP : Measurable P)
    (M : ℕ → ℕ) (r : ∀ N, Y → Fin (M N)) (hr : ∀ N, Measurable (r N))
    (v : ∀ N, Fin (M N) → Fin N → α)
    {a ε δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (herr : ∀ᶠ N : ℕ in Filter.atTop,
      (∑ i : Fin N, μ.real {y | P (T^[i.val] y) ≠ v N (r N y) i}) ≤ ε*N)
    (hcard : ∀ᶠ N : ℕ in Filter.atTop, Real.log (M N) ≤ a*N) :
    observationEntropyRate μ T P ≤ a+rareLabelCost (Fintype.card α) δ ε := by
  have H : ∀ᶠ N : ℕ in Filter.atTop,
      observationEntropy μ (orbitName T P N)/(N : ℝ) ≤
        a+rareLabelCost (Fintype.card α) δ ε := by
    filter_upwards [herr,hcard,Filter.eventually_ge_atTop (1 : ℕ)] with N he hc hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hPN : Measurable (orbitName T P N) :=
      measurable_pi_iff.mpr fun i => hP.comp (hT.measurable.iterate i.val)
    have hb := nameEntropy_le_reference_errors μ N (orbitName T P N) hPN
      (r N) (hr N) (v N) hδ hδ1 he
    simp only [Fintype.card_fin] at hb
    apply (div_le_iff₀ hn).mpr
    nlinarith
  exact le_of_tendsto (tendsto_observationEntropyRate μ hT P
    (fun a => hP (measurableSet_singleton a))) H

/-- Orbit errors confined to a fixed measurable bad set cost at most its
measure at each coordinate. -/
theorem name_errors_le_bad_visits {Y α : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (N : ℕ)
    (R : Y → Fin N → α) (B : Set Y) (hB : MeasurableSet B)
    (hbad : ∀ y i, P (T^[i.val] y) ≠ R y i → T^[i.val] y ∈ B) :
    (∑ i : Fin N, μ.real {y | P (T^[i.val] y) ≠ R y i}) ≤ (N : ℝ)*μ.real B := by
  calc
    _ ≤ ∑ i : Fin N, μ.real ((T^[i.val]) ⁻¹' B) := by
      apply Finset.sum_le_sum
      intro i _
      exact measureReal_mono (fun y hy => hbad y i hy)
    _ = _ := by
      have hi (i : Fin N) : μ.real ((T^[i.val]) ⁻¹' B) = μ.real B :=
        (hT.iterate i.val).measureReal_preimage hB.nullMeasurableSet
      simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- A fixed finite list of reference trajectories has zero asymptotic
coding cost. Only the coordinate errors contribute to the entropy rate. -/
theorem observationEntropyRate_le_fixed_reference_errors
    {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (hP : Measurable P)
    (M : ℕ) (r : ℕ → Y → Fin M) (hr : ∀ N, Measurable (r N))
    (v : ∀ N, Fin M → Fin N → α)
    {ε δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (herr : ∀ N,
      (∑ i : Fin N, μ.real {y | P (T^[i.val] y) ≠ v N (r N y) i}) ≤ ε*N) :
    observationEntropyRate μ T P ≤ rareLabelCost (Fintype.card α) δ ε := by
  have H : ∀ᶠ N : ℕ in Filter.atTop,
      observationEntropy μ (orbitName T P N)/(N : ℝ) ≤
        Real.log M/(N : ℝ)+rareLabelCost (Fintype.card α) δ ε := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hPN : Measurable (orbitName T P N) :=
      measurable_pi_iff.mpr fun i => hP.comp (hT.measurable.iterate i.val)
    have hb := nameEntropy_le_reference_errors μ N (orbitName T P N) hPN
      (r N) (hr N) (v N) hδ hδ1 (herr N)
    simp only [Fintype.card_fin] at hb
    apply (div_le_iff₀ hn).mpr
    have heq : (Real.log M/(N : ℝ)+rareLabelCost (Fintype.card α) δ ε)*N =
        Real.log M+(N : ℝ)*rareLabelCost (Fintype.card α) δ ε := by
      field_simp
    rwa [heq]
  have hlim : Filter.Tendsto
      (fun N : ℕ => Real.log M/(N : ℝ)+rareLabelCost (Fintype.card α) δ ε)
      Filter.atTop (𝓝 (rareLabelCost (Fintype.card α) δ ε)) := by
    simpa only [zero_add] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun N : ℕ => Real.log M/(N : ℝ)) Filter.atTop (𝓝 0)).add
          tendsto_const_nhds
  exact le_of_tendsto_of_tendsto
    (tendsto_observationEntropyRate μ hT P (fun a => hP (measurableSet_singleton a))) hlim H

/-- Arbitrarily accurate approximation by a fixed finite list of
trajectories forces zero entropy for a finite observation. -/
theorem observationEntropyRate_le_zero_of_fixed_reference_approximations
    {Y α : Type*} [MeasurableSpace Y]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype α] [Nonempty α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α) (hP : Measurable P)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ (M : ℕ) (r : ℕ → Y → Fin M) (v : ∀ N, Fin M → Fin N → α),
        (∀ N, Measurable (r N)) ∧ ∀ N,
          (∑ i : Fin N, μ.real {y | P (T^[i.val] y) ≠ v N (r N y) i}) ≤ ε*N) :
    observationEntropyRate μ T P ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨δ,ε,hd,hd1,he,hcost⟩ := rareLabelCost_small (Fintype.card α) hη
  obtain ⟨M,r,v,hr,herr⟩ := happrox (ε/2) (by positivity)
  have h := observationEntropyRate_le_fixed_reference_errors μ hT P hP
    M r hr v hd hd1 herr
  exact h.trans ((hcost (ε/2) (by positivity) (by linarith)).le.trans_eq (zero_add η).symm)

end DukePrimeDegree

end

end OAI
