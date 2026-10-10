import OAI.Analysis.Brenier.Wasserstein

namespace OAI

noncomputable section

open MeasureTheory Set Metric

namespace Problem358

/-- Select, measurably, a point of a finite family of balls covering the input.
Outside their union the selector takes a fixed default value. -/
theorem exists_measurable_ball_selector
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : Finset X) (y₀ : X) (ε : ℝ) :
    ∃ Q : X → X, Measurable Q ∧
      (∀ x, Q x = y₀ ∨ Q x ∈ s) ∧
      (∀ x, (∃ y ∈ s, dist x y < ε) → dist x (Q x) < ε) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => y₀, measurable_const, ?_, ?_⟩
      · simp
      · simp
  | @insert y s hys ih =>
      obtain ⟨Q, hQ, hQr, hQdist⟩ := ih
      let R : X → X := fun x => if dist x y < ε then y else Q x
      refine ⟨R, ?_, ?_, ?_⟩
      · exact Measurable.ite (isOpen_lt (continuous_id.dist continuous_const)
          continuous_const).measurableSet measurable_const hQ
      · intro x
        dsimp [R]
        split_ifs with h
        · simp
        · rcases hQr x with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_insert_of_mem h)
      · intro x hx
        dsimp [R]
        split_ifs with h
        · exact h
        · apply hQdist
          obtain ⟨z, hz, hdist⟩ := hx
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact False.elim (h hdist)
          · exact ⟨z, hz, hdist⟩

/-- A compact nonempty set admits measurable finite-valued quantizers with
arbitrarily small error. The quantizer takes values in the set even away from it. -/
theorem IsCompact.exists_measurable_finite_quantizer
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Set X} (hY : IsCompact Y) (hne : Y.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : X → X, Measurable Q ∧ (Set.range Q).Finite ∧
      (∀ x, Q x ∈ Y) ∧ ∀ x ∈ Y, dist x (Q x) < ε := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨s, hsY, hsfin, hscover⟩ := hY.finite_cover_balls hε
  obtain ⟨Q, hQ, hQr, hQdist⟩ :=
    exists_measurable_ball_selector hsfin.toFinset y₀ ε
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · exact (Finset.finite_toSet (insert y₀ hsfin.toFinset)).subset
      (by rintro z ⟨x, rfl⟩; exact Finset.mem_insert.mpr (hQr x))
  · intro x
    rcases hQr x with h | h
    · simpa [h] using hy₀
    · exact hsY (hsfin.mem_toFinset.mp h)
  · intro x hx
    apply hQdist
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hscover hx)
    exact ⟨y, hsfin.mem_toFinset.mpr hy, hxy⟩

/-- A single sequence of finite-valued Borel maps approximates the identity
uniformly on a compact set, with a specified reciprocal error rate. -/
theorem IsCompact.exists_finite_quantizer_sequence
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Set X} (hY : IsCompact Y) (hne : Y.Nonempty) :
    ∃ Q : ℕ → X → X,
      (∀ n, Measurable (Q n)) ∧
      (∀ n, (Set.range (Q n)).Finite) ∧
      (∀ n x, Q n x ∈ Y) ∧
      (∀ n x, x ∈ Y → dist x (Q n x) < 1 / ((n : ℝ) + 1)) ∧
      TendstoUniformlyOn Q id Filter.atTop Y := by
  have hpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose Q hQ hfin hmem hdist using
    fun n => Problem358.IsCompact.exists_measurable_finite_quantizer hY hne (hpos n)
  refine ⟨Q, hQ, hfin, hmem, hdist, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      Filter.atTop (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht (Iio_mem_nhds hε)] with n hn x hx
  exact (hdist n x hx).trans hn

/-- Continuous test integrals are stable under compact-valued uniform
quantization, for any finite measure concentrated on the compact set. -/
theorem tendsto_integral_comp_of_compact_quantizers
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Y : Set X} (hY : IsCompact Y) {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Y) {Q : ℕ → X → X}
    (hQ : ∀ n, Measurable (Q n)) (hmem : ∀ n x, Q n x ∈ Y)
    (hlim : TendstoUniformlyOn Q id Filter.atTop Y)
    {φ : X → ℝ} (hφ : Continuous φ) :
    Filter.Tendsto (fun n => ∫ x, φ (Q n x) ∂μ) Filter.atTop
      (nhds (∫ x, φ x ∂μ)) := by
  obtain ⟨R, hR⟩ := hY.exists_bound_of_continuousOn hφ.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun _ => R)
  · intro n
    exact (hφ.measurable.comp (hQ n)).aestronglyMeasurable
  · exact integrable_const R
  · intro n
    exact Filter.Eventually.of_forall (fun x => hR _ (hmem n x))
  · filter_upwards [hμ] with x hx
    exact hφ.continuousAt.tendsto.comp (hlim.tendsto_at hx)

end Problem358

end

noncomputable section

open MeasureTheory Set

namespace Problem358

/-- A Borel nearest-point selection on a finite set, with a default point. -/
theorem exists_finite_nearest_selection
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (y₀ : X) (s : Finset X) :
    ∃ q : SimpleFunc X X, (∀ x, q x = y₀ ∨ q x ∈ s) ∧
      ∀ x y, y ∈ s → dist (q x) x ≤ dist y x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨SimpleFunc.const X y₀, ?_, ?_⟩
      · intro x
        exact Or.inl rfl
      · simp
  | @insert a s ha ih =>
      obtain ⟨q, hqmem, hqdist⟩ := ih
      let A : Set X := {x | dist a x ≤ dist (q x) x}
      have hA : MeasurableSet A :=
        measurableSet_le (measurable_const.dist measurable_id)
          (q.measurable.dist measurable_id)
      let r : SimpleFunc X X := SimpleFunc.piecewise A hA (SimpleFunc.const X a) q
      refine ⟨r, ?_, ?_⟩
      · intro x
        by_cases hx : x ∈ A
        · right
          simp [r, SimpleFunc.coe_piecewise, Set.piecewise, hx]
        · rcases hqmem x with h | h
          · left
            simpa [r, SimpleFunc.coe_piecewise, Set.piecewise, hx] using h
          · right
            simpa [r, SimpleFunc.coe_piecewise, Set.piecewise, hx] using
              (Finset.mem_insert_of_mem h : q x ∈ insert a s)
      · intro x y hy
        by_cases hx : x ∈ A
        · have hax : dist a x ≤ dist (q x) x := hx
          simp only [r, SimpleFunc.coe_piecewise, Set.piecewise, hx, ite_true,
            SimpleFunc.const_apply]
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact le_rfl
          · exact hax.trans (hqdist x y hy)
        · have hax : dist (q x) x ≤ dist a x := (lt_of_not_ge hx).le
          simp only [r, SimpleFunc.coe_piecewise, Set.piecewise, hx, ite_false]
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hax
          · exact hqdist x y hy

/-- Compact sets admit finite-range Borel quantizers valued in the same set. -/
theorem exists_compact_quantizer
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Set X} (hY : IsCompact Y) (hne : Y.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : SimpleFunc X X, (∀ x, q x ∈ Y) ∧ ∀ x ∈ Y, dist (q x) x < ε := by
  classical
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨s, hsY, hs, hcover⟩ := hY.finite_cover_balls hε
  obtain ⟨q, hqmem, hqdist⟩ := exists_finite_nearest_selection y₀ hs.toFinset
  refine ⟨q, ?_, ?_⟩
  · intro x
    rcases hqmem x with h | h
    · simpa [h] using hy₀
    · exact hsY (by simpa using h)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact (hqdist x y (by simpa using hy)).trans_lt
      (by simpa [Metric.mem_ball, dist_comm] using hxy)

/-- A pointwise quantization error bounds the cost of its induced transport plan. -/
theorem quantizer_graph_cost_le {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {Y : Set (E d)} (hμ : IsSupported μ Y)
    {ε : ℝ} (hε : 0 ≤ ε) {q : E d → E d} (hq : Measurable q)
    (herr : ∀ x ∈ Y, dist (q x) x ≤ ε) :
    quadraticPlanCost (graphPlan μ q) ≤ ENNReal.ofReal (ε ^ 2) := by
  have hae : ∀ᵐ x ∂μ, x ∈ Y := ae_iff.mpr hμ
  unfold quadraticPlanCost graphPlan
  have hm : Measurable (fun p : E d × E d =>
      ENNReal.ofReal (‖p.1 - p.2‖ ^ 2)) :=
    ((measurable_fst.sub measurable_snd).norm.pow_const 2).ennreal_ofReal
  have hg : Measurable (fun x => (x, q x)) := measurable_id.prodMk hq
  rw [lintegral_map hm hg]
  calc
    _ ≤ ∫⁻ _ : E d, ENNReal.ofReal (ε ^ 2) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hae] with x hx
      apply ENNReal.ofReal_le_ofReal
      apply (sq_le_sq₀ (norm_nonneg _) hε).mpr
      simpa [dist_eq_norm, norm_sub_rev] using herr x hx
    _ = _ := by simp

/-- Pushing a measure through a simple function gives a finitely supported measure. -/
theorem simpleFunc_map_finite_support {d : ℕ} (μ : Measure (E d))
    (q : SimpleFunc (E d) (E d)) :
    (Set.range q).Finite ∧ IsSupported (Measure.map q μ) (Set.range q) := by
  refine ⟨q.finite_range, ?_⟩
  unfold IsSupported
  rw [Measure.map_apply q.measurable q.finite_range.measurableSet.compl]
  have hempty : q ⁻¹' (Set.range q)ᶜ = ∅ := by
    ext x
    simp
  rw [hempty, measure_empty]

/-- Finite supported approximants remain inside the original compact target. -/
theorem exists_finite_target_approximation {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {Y : Set (E d)}
    (hY : IsCompact Y) (hne : Y.Nonempty) (hμ : IsSupported μ Y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : SimpleFunc (E d) (E d),
      (∀ x, q x ∈ Y) ∧
      IsProbabilityMeasure (Measure.map q μ) ∧
      IsSupported (Measure.map q μ) Y ∧
      IsSupported (Measure.map q μ) (Set.range q) ∧
      quadraticPlanCost (graphPlan μ q) ≤ ENNReal.ofReal (ε ^ 2) := by
  obtain ⟨q, hqY, hqerr⟩ := exists_compact_quantizer hY hne hε
  refine ⟨q, hqY, inferInstance, ?_,
    (simpleFunc_map_finite_support μ q).2,
    quantizer_graph_cost_le hμ hε.le q.measurable (fun x hx => (hqerr x hx).le)⟩
  unfold IsSupported
  rw [Measure.map_apply q.measurable hY.measurableSet.compl]
  have hempty : q ⁻¹' Yᶜ = ∅ := by
    ext x
    simp [hqY x]
  rw [hempty, measure_empty]

/-- The problem's transport distance is controlled by a uniform quantization error. -/
theorem wasserstein2_map_le_quantization_error {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {Y : Set (E d)} (hμ : IsSupported μ Y)
    {ε : ℝ} (hε : 0 ≤ ε) {q : E d → E d} (hq : Measurable q)
    (herr : ∀ x ∈ Y, dist (q x) x ≤ ε) :
    wasserstein2 μ (Measure.map q μ) ≤ ε := by
  have hg : Measurable (fun x => (x, q x)) := measurable_id.prodMk hq
  have hπ : IsCoupling μ (Measure.map q μ) (graphPlan μ q) := by
    refine ⟨?_, ?_, ?_⟩
    · unfold graphPlan
      infer_instance
    · unfold graphPlan
      rw [Measure.map_map measurable_fst hg]
      exact Measure.map_id
    · unfold graphPlan
      rw [Measure.map_map measurable_snd hg]
      rfl
  have hc := quantizer_graph_cost_le hμ hε hq herr
  have hfin : quadraticPlanCost (graphPlan μ q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hc
  calc
    wasserstein2 μ (Measure.map q μ) ≤
        Real.sqrt (quadraticPlanCost (graphPlan μ q)).toReal :=
      wasserstein2_le_of_coupling hπ hfin
    _ ≤ Real.sqrt (ENNReal.ofReal (ε ^ 2)).toReal :=
      Real.sqrt_le_sqrt (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc)
    _ = ε := by rw [ENNReal.toReal_ofReal (sq_nonneg ε), Real.sqrt_sq hε]

/-- Every compactly supported probability admits finite supported probabilities arbitrarily
close in the exact transport distance used by the challenge. -/
theorem exists_finite_supported_wasserstein_approximation {d : ℕ}
    {μ : Measure (E d)} [IsProbabilityMeasure μ] {Y : Set (E d)}
    (hY : IsCompact Y) (hne : Y.Nonempty) (hμ : IsSupported μ Y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ν : Measure (E d)) (F : Set (E d)), F.Finite ∧ F ⊆ Y ∧
      IsProbabilityMeasure ν ∧ IsSupported ν F ∧ IsSupported ν Y ∧
      wasserstein2 μ ν ≤ ε := by
  obtain ⟨q, hqY, hqerr⟩ := exists_compact_quantizer hY hne hε
  refine ⟨Measure.map q μ, Set.range q, q.finite_range, ?_,
    inferInstance,
    (simpleFunc_map_finite_support μ q).2, ?_,
    wasserstein2_map_le_quantization_error hμ hε.le q.measurable
      (fun x hx => (hqerr x hx).le)⟩
  · rintro y ⟨x, rfl⟩
    exact hqY x
  · unfold IsSupported
    rw [Measure.map_apply q.measurable hY.measurableSet.compl]
    have hempty : q ⁻¹' Yᶜ = ∅ := by
      ext x
      simp [hqY x]
    rw [hempty, measure_empty]

end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Problem358

/-- Zero-mass sites can be discarded from any finite support without changing the measure. -/
theorem exists_positive_atomic_support {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {F : Set (E d)} (hF : F.Finite)
    (hμ : IsSupported μ F) :
    ∃ S : Finset (E d), S.Nonempty ∧ (S : Set (E d)) ⊆ F ∧
      (∀ x ∈ S, 0 < μ {x}) ∧ (∑ x ∈ S, μ {x}) = 1 ∧
      μ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
  classical
  have hae : ∀ᵐ x ∂μ, x ∈ hF.toFinset := by
    simpa only [hF.mem_toFinset] using (ae_iff.mpr hμ : ∀ᵐ x ∂μ, x ∈ F)
  have hrepr := Measure.ae_mem_finset_iff.mp hae
  let S := hF.toFinset.filter (fun x => μ {x} ≠ 0)
  have hreprS : μ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
    calc
      μ = ∑ x ∈ hF.toFinset, μ {x} • Measure.dirac x := hrepr
      _ = ∑ x ∈ S, μ {x} • Measure.dirac x := by
        dsimp [S]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : μ {x} = 0 <;> simp [h]
  have hsum : (∑ x ∈ S, μ {x}) = 1 := by
    have h := congrArg (fun ν : Measure (E d) => ν Set.univ) hreprS
    simpa using h.symm
  refine ⟨S, ?_, ?_, ?_, hsum, hreprS⟩
  · by_contra h
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hempty] at hsum
  · intro x hx
    exact hF.mem_toFinset.mp (Finset.mem_filter.mp hx).1
  · intro x hx
    exact pos_iff_ne_zero.mpr (Finset.mem_filter.mp hx).2

/-- The finite-support representation can use positive ordinary real weights. -/
theorem exists_positive_real_atomic_support {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {F : Set (E d)} (hF : F.Finite)
    (hμ : IsSupported μ F) :
    ∃ S : Finset (E d), S.Nonempty ∧ (S : Set (E d)) ⊆ F ∧
      (∀ x ∈ S, 0 < (μ {x}).toReal) ∧ (∑ x ∈ S, (μ {x}).toReal) = 1 ∧
      μ = ∑ x ∈ S, ENNReal.ofReal ((μ {x}).toReal) • Measure.dirac x := by
  obtain ⟨S, hS, hsub, hpos, hsum, hrepr⟩ := exists_positive_atomic_support hF hμ
  refine ⟨S, hS, hsub, ?_, ?_, ?_⟩
  · intro x hx
    exact ENNReal.toReal_pos (ne_of_gt (hpos x hx)) (measure_singleton_lt_top.ne)
  · rw [← ENNReal.toReal_sum (fun x hx => measure_singleton_lt_top.ne), hsum]
    simp
  · simpa only [ENNReal.ofReal_toReal measure_singleton_lt_top.ne] using hrepr

/-- A finite supported probability has a presentation by distinct sites and strictly
positive real weights, indexed by a nonempty finite ordinal. -/
theorem exists_positive_finite_atomic_presentation {d : ℕ} {μ : Measure (E d)}
    [IsProbabilityMeasure μ] {F : Set (E d)} (hF : F.Finite)
    (hμ : IsSupported μ F) :
    ∃ n : ℕ, 0 < n ∧ ∃ (y : Fin n → E d) (w : Fin n → ℝ),
      Function.Injective y ∧ (∀ i, y i ∈ F) ∧ (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧ μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (y i) := by
  classical
  obtain ⟨S, hS, hsub, hpos, hsum, hrepr⟩ := exists_positive_real_atomic_support hF hμ
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hn : 0 < Fintype.card S := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨x, hx⟩ := hS
    exact ⟨⟨x, hx⟩⟩
  refine ⟨Fintype.card S, hn, (fun i => (e i).val),
    (fun i => (μ {(e i).val}).toReal), Subtype.val_injective.comp e.injective,
    (fun i => hsub (e i).property), (fun i => hpos _ (e i).property), ?_, ?_⟩
  · calc
      _ = ∑ x : S, (μ {x.val}).toReal := e.sum_comp _
      _ = ∑ x ∈ S, (μ {x}).toReal := Finset.sum_coe_sort S (fun x : E d => (μ {x}).toReal)
      _ = 1 := hsum
  · calc
      μ = ∑ x ∈ S, ENNReal.ofReal ((μ {x}).toReal) • Measure.dirac x := hrepr
      _ = ∑ x : S, ENNReal.ofReal ((μ {x.val}).toReal) • Measure.dirac x.val :=
        (Finset.sum_coe_sort S (fun x : E d => ENNReal.ofReal ((μ {x}).toReal) • Measure.dirac x)).symm
      _ = _ := (e.sum_comp _).symm

/-- Compact probabilities can be approximated by positive finite atomic families without
changing the allowed target set. -/
theorem exists_positive_atomic_wasserstein_approximation {d : ℕ}
    {μ : Measure (E d)} [IsProbabilityMeasure μ] {Y : Set (E d)}
    (hY : IsCompact Y) (hne : Y.Nonempty) (hμ : IsSupported μ Y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ (y : Fin n → E d) (w : Fin n → ℝ),
      Function.Injective y ∧ (∀ i, y i ∈ Y) ∧ (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧
      wasserstein2 μ (∑ i, ENNReal.ofReal (w i) • Measure.dirac (y i)) ≤ ε := by
  obtain ⟨ν, F, hF, hsub, hprob, hsupp, _, herr⟩ :=
    exists_finite_supported_wasserstein_approximation hY hne hμ hε
  let : IsProbabilityMeasure ν := hprob
  obtain ⟨n, hn, y, w, hy, hyF, hw, hsum, hrepr⟩ :=
    exists_positive_finite_atomic_presentation hF hsupp
  refine ⟨n, hn, y, w, hy, (fun i => hsub (hyF i)), hw, hsum, ?_⟩
  simpa only [← hrepr] using herr

end Problem358

end

end OAI
