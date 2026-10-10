import OAI.Probability.FKMaps.Model

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal

namespace FKCRT

lemma interval_image_bddBelow {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : BddBelow (e '' Set.uIcc s t) :=
  (isCompact_uIcc.image he).bddBelow

lemma interval_inf_le_left {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : sInf (e '' Set.uIcc s t) ≤ e s :=
  csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e left_mem_uIcc)

lemma interval_inf_le_right {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : sInf (e '' Set.uIcc s t) ≤ e t :=
  csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e right_mem_uIcc)

lemma excursionDist_self (e : unitInterval → ℝ) (s : unitInterval) :
    excursionDist e s s = 0 := by
  simp [excursionDist, two_mul]

lemma excursionDist_comm (e : unitInterval → ℝ) (s t : unitInterval) :
    excursionDist e s t = excursionDist e t s := by
  simp only [excursionDist, uIcc_comm t s]
  ring

lemma excursionDist_nonneg {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) : 0 ≤ excursionDist e s t := by
  have h1 := interval_inf_le_left he s t
  have h2 := interval_inf_le_right he s t
  dsimp [excursionDist, two_mul]
  linarith

lemma interval_inf_ge_min {e : unitInterval → ℝ} (he : Continuous e)
    (s t u : unitInterval) :
    min (sInf (e '' Set.uIcc s t)) (sInf (e '' Set.uIcc t u)) ≤
      sInf (e '' Set.uIcc s u) := by
  apply le_csInf (nonempty_uIcc.image e)
  rintro _ ⟨v, hv, rfl⟩
  rcases uIcc_subset_uIcc_union_uIcc hv with h | h
  · exact (min_le_left _ _).trans
      (csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e h))
  · exact (min_le_right _ _).trans
      (csInf_le (interval_image_bddBelow he t u) (mem_image_of_mem e h))

lemma excursionDist_triangle {e : unitInterval → ℝ} (he : Continuous e)
    (s t u : unitInterval) :
    excursionDist e s u ≤ excursionDist e s t + excursionDist e t u := by
  have h1 := interval_inf_le_right he s t
  have h2 := interval_inf_le_left he t u
  have h3 := interval_inf_ge_min he s t u
  dsimp [excursionDist, two_mul]
  rcases le_total (sInf (e '' Set.uIcc s t)) (sInf (e '' Set.uIcc t u)) with h | h
  · rw [min_eq_left h] at h3
    linarith
  · rw [min_eq_right h] at h3
    linarith

lemma excursionDist_eq_of_zero_left {e : unitInterval → ℝ} (he : Continuous e)
    {s t : unitInterval} (hst : excursionDist e s t = 0) (u : unitInterval) :
    excursionDist e s u = excursionDist e t u := by
  have h1 := excursionDist_triangle he s t u
  have h2 := excursionDist_triangle he t s u
  rw [excursionDist_comm e t s, hst] at h2
  rw [hst] at h1
  linarith

lemma excursionDist_zero_of_eqvGen {e : unitInterval → ℝ} (he : Continuous e)
    {s t : unitInterval}
    (hst : Relation.EqvGen (fun s t => excursionDist e s t = 0) s t) :
    excursionDist e s t = 0 := by
  induction hst with
  | rel s t h => exact h
  | refl s => exact excursionDist_self e s
  | symm s t _ h => simpa only [excursionDist_comm e t s] using h
  | trans s t u _ _ h1 h2 =>
      have h3 := excursionDist_triangle he s t u
      have h4 := excursionDist_nonneg he s u
      rw [h1, h2] at h3
      linarith


lemma treeProjection_surjective (e : unitInterval → ℝ) :
    Function.Surjective (treeProjection e) := Quotient.mk_surjective

lemma excursionDist_out {e : unitInterval → ℝ} (he : Continuous e)
    (s t : unitInterval) :
    excursionDist e (treeProjection e s).out (treeProjection e t).out =
      excursionDist e s t := by
  unfold treeProjection
  rw [excursionDist_eq_of_zero_left he
    (excursionDist_zero_of_eqvGen he (Quotient.mk_out (s := Relation.EqvGen.setoid (fun s t => excursionDist e s t = 0)) s))]
  rw [excursionDist_comm e s, excursionDist_eq_of_zero_left he
    (excursionDist_zero_of_eqvGen he (Quotient.mk_out (s := Relation.EqvGen.setoid (fun s t => excursionDist e s t = 0)) t)), excursionDist_comm]

/-- The excursion quotient, with the genuine induced metric. -/
@[instance_reducible]
def excursionTreeMetric {e : unitInterval → ℝ} (he : Continuous e) :
    MetricSpace (ExcursionTree e) where
  dist x y := excursionDist e x.out y.out
  dist_self x := excursionDist_self e x.out
  dist_comm x y := excursionDist_comm e x.out y.out
  dist_triangle x y z := excursionDist_triangle he x.out y.out z.out
  eq_of_dist_eq_zero {x y} h := by
    rw [← x.out_eq, ← y.out_eq]
    exact Quotient.sound (Relation.EqvGen.rel _ _ h)

lemma unitInterval_dist_le_of_mem_uIcc {r s t : unitInterval} (hr : r ∈ uIcc s t) :
    dist r s ≤ dist t s := by
  change |(r : ℝ) - (s : ℝ)| ≤ |(t : ℝ) - (s : ℝ)|
  rcases le_total s t with h | h
  · rw [uIcc_of_le h] at hr
    have h1 : (s : ℝ) ≤ (r : ℝ) := hr.1
    have h2 : (r : ℝ) ≤ (t : ℝ) := hr.2
    rw [abs_of_nonneg (sub_nonneg.mpr h1),
      abs_of_nonneg (sub_nonneg.mpr (h1.trans h2))]
    linarith
  · rw [uIcc_of_ge h] at hr
    have h1 : (t : ℝ) ≤ (r : ℝ) := hr.1
    have h2 : (r : ℝ) ≤ (s : ℝ) := hr.2
    rw [abs_of_nonpos (sub_nonpos.mpr h2),
      abs_of_nonpos (sub_nonpos.mpr (h1.trans h2))]
    linarith

lemma treeProjection_continuous {e : unitInterval → ℝ} (he : Continuous e) :
    @Continuous _ _ inferInstance
      (excursionTreeMetric he).toUniformSpace.toTopologicalSpace (treeProjection e) := by
  let : MetricSpace (ExcursionTree e) := excursionTreeMetric he
  apply Metric.continuous_iff.mpr
  intro s ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp he s (ε / 4) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  change excursionDist e (treeProjection e t).out (treeProjection e s).out < ε
  rw [excursionDist_out he]
  have h1 : e t < e s + ε / 4 := by
    have := (abs_lt.mp (h t ht)).2
    linarith
  have h2 : e s - ε / 4 ≤ sInf (e '' uIcc t s) := by
    apply le_csInf (nonempty_uIcc.image e)
    rintro _ ⟨r, hr, rfl⟩
    rw [uIcc_comm] at hr
    have hd : dist r s < δ := (unitInterval_dist_le_of_mem_uIcc hr).trans_lt ht
    have := (abs_lt.mp (h r hd)).1
    linarith
  dsimp [excursionDist]
  linarith


lemma excursionTree_topology {e : unitInterval → ℝ} (he : Continuous e) :
    (excursionTreeMetric he).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.coinduced (treeProjection e) inferInstance := by
  let m : MetricSpace (ExcursionTree e) := excursionTreeMetric he
  let t : TopologicalSpace (ExcursionTree e) := m.toUniformSpace.toTopologicalSpace
  have hc : Continuous (treeProjection e) := treeProjection_continuous he
  exact (hc.isClosedMap.isQuotientMap hc (treeProjection_surjective e)).isCoinducing.eq_coinduced

lemma excursionTree_compact {e : unitInterval → ℝ} (he : Continuous e) :
    @CompactSpace (ExcursionTree e) (excursionTreeMetric he).toUniformSpace.toTopologicalSpace := by
  let m : MetricSpace (ExcursionTree e) := excursionTreeMetric he
  let t : TopologicalSpace (ExcursionTree e) := m.toUniformSpace.toTopologicalSpace
  have hc : Continuous (treeProjection e) := treeProjection_continuous he
  apply isCompact_univ_iff.mp
  have h := isCompact_univ.image hc
  rwa [image_univ, (treeProjection_surjective e).range_eq] at h

lemma unitInterval_volume_univ : (volume : Measure unitInterval) univ = 1 := by
  rw [volume_set_coe_def, comap_subtype_coe_apply measurableSet_Icc,
    Set.image_univ, Subtype.range_coe]
  rw [Real.volume_Icc]
  norm_num


lemma treeSpace_mass_univ (e : unitInterval → ℝ) :
    (treeSpace e).mass univ = 1 := by
  let t : TopologicalSpace (ExcursionTree e) :=
    TopologicalSpace.coinduced (treeProjection e) inferInstance
  let ms : MeasurableSpace (ExcursionTree e) := borel _
  let bs : BorelSpace (ExcursionTree e) := ⟨rfl⟩
  have hc : Continuous (treeProjection e) := continuous_iff_coinduced_le.mpr le_rfl
  change (Measure.map (treeProjection e) (volume : Measure unitInterval)) univ = 1
  rw [Measure.map_apply hc.measurable MeasurableSet.univ, preimage_univ,
    unitInterval_volume_univ]

/-- A continuous excursion codes a compact metric probability space. No
positivity or endpoint hypotheses are required for this validity statement. -/
lemma treeSpace_valid {e : unitInterval → ℝ} (he : Continuous e) : (treeSpace e).Valid := by
  refine ⟨excursionTreeMetric he, ?_⟩
  refine ⟨fun _ _ => rfl, excursionTree_compact he, ?_, treeSpace_mass_univ e⟩
  change @borel _ (TopologicalSpace.coinduced (treeProjection e) inferInstance) =
    @borel _ (excursionTreeMetric he).toUniformSpace.toTopologicalSpace
  rw [excursionTree_topology he]


lemma interval_inf_sub_le {e f : unitInterval → ℝ}
    (he : Continuous e) (s t : unitInterval) {ε : ℝ}
    (h : ∀ r, e r - f r ≤ ε) :
    sInf (e '' uIcc s t) - sInf (f '' uIcc s t) ≤ ε := by
  have hi : sInf (e '' uIcc s t) - ε ≤ sInf (f '' uIcc s t) := by
    apply le_csInf (nonempty_uIcc.image f)
    rintro _ ⟨r, hr, rfl⟩
    have h1 := csInf_le (interval_image_bddBelow he s t) (mem_image_of_mem e hr)
    have h2 := h r
    linarith
  linarith

lemma interval_inf_abs_sub_le {e f : unitInterval → ℝ}
    (he : Continuous e) (hf : Continuous f) (s t : unitInterval) {ε : ℝ}
    (h : ∀ r, |e r - f r| ≤ ε) :
    |sInf (e '' uIcc s t) - sInf (f '' uIcc s t)| ≤ ε := by
  apply abs_le.mpr
  constructor
  · have hi := interval_inf_sub_le (f := e) hf s t (ε := ε)
      (fun r => by have := (abs_le.mp (h r)).1; linarith)
    linarith
  · exact interval_inf_sub_le he s t (fun r => (abs_le.mp (h r)).2)

/-- Deterministic four-times-sup-norm distortion bound for excursion coding. -/
lemma excursionDist_abs_sub_le {e f : unitInterval → ℝ}
    (he : Continuous e) (hf : Continuous f) (s t : unitInterval) {ε : ℝ}
    (h : ∀ r, |e r - f r| ≤ ε) :
    |excursionDist e s t - excursionDist f s t| ≤ 4 * ε := by
  have hs := abs_le.mp (h s)
  have ht := abs_le.mp (h t)
  have hi := abs_le.mp (interval_inf_abs_sub_le he hf s t h)
  apply abs_le.mpr
  dsimp [excursionDist]
  constructor <;> linarith


lemma levyProkhorovEDist_map_le_of_dist {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y] [PseudoMetricSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure Z) {f g : Z → Y}
    (hf : Measurable f) (hg : Measurable g) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ z, dist (f z) (g z) ≤ ε) :
    levyProkhorovEDist (μ.map f) (μ.map g) ≤ ENNReal.ofReal ε := by
  apply levyProkhorovEDist_le_of_forall
  intro r B hr hrt hB
  have hεr : ε < r.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hε hrt.ne).mp hr
  have hBg : MeasurableSet (Metric.thickening r.toReal B) :=
    Metric.isOpen_thickening.measurableSet
  constructor
  · apply le_trans _ le_self_add
    rw [Measure.map_apply hf hB, Measure.map_apply hg hBg]
    apply measure_mono
    intro z hz
    exact Metric.mem_thickening_iff.mpr ⟨f z, hz,
      (by rw [dist_comm]; exact (hfg z).trans_lt hεr)⟩
  · apply le_trans _ le_self_add
    rw [Measure.map_apply hg hB, Measure.map_apply hf hBg]
    apply measure_mono
    intro z hz
    exact Metric.mem_thickening_iff.mpr ⟨g z, hz, (hfg z).trans_lt hεr⟩

/-- A common coding with distortion at most `2ε` and a common mass gives
GHP distance at most `ε`. The metric-quotient gluing is supplied by Mathlib. -/
lemma ghpEDist_le_of_coding {X Y : MetricMeasureData}
    (hX : X.Valid) (hY : Y.Valid) {Z : Type} [Nonempty Z] [MeasurableSpace Z]
    (μ : Measure Z) (f : Z → X.Carrier) (g : Z → Y.Carrier)
    (hf : @Measurable _ _ inferInstance X.measurableSpace f)
    (hg : @Measurable _ _ inferInstance Y.measurableSpace g)
    (hsf : Function.Surjective f) (hsg : Function.Surjective g)
    (hmf : @Measure.map _ _ inferInstance X.measurableSpace f μ = X.mass)
    (hmg : @Measure.map _ _ inferInstance Y.measurableSpace g μ = Y.mass)
    {ε : ℝ} (hε : 0 < ε)
    (hfg : ∀ s t, |X.distance (f s) (f t) - Y.distance (g s) (g t)| ≤ 2 * ε) :
    ghpEDist X Y ≤ ENNReal.ofReal ε := by
  obtain ⟨mX, hdX, _, hbX, _⟩ := hX
  obtain ⟨mY, hdY, _, hbY, _⟩ := hY
  let : MetricSpace X.Carrier := mX
  let : MetricSpace Y.Carrier := mY
  let : MeasurableSpace X.Carrier := X.measurableSpace
  let : MeasurableSpace Y.Carrier := Y.measurableSpace
  let : BorelSpace X.Carrier := ⟨hbX⟩
  let : BorelSpace Y.Carrier := ⟨hbY⟩
  have hfg' : ∀ s t, |dist (f s) (f t) - dist (g s) (g t)| ≤ 2 * ε := by
    simpa only [hdX, hdY] using hfg
  let m := Metric.glueMetricApprox f g ε hε hfg'
  have hm : Amalgamates X Y m.toPseudoMetricSpace := ⟨hdX, hdY⟩
  apply (iInf_le (fun m : {m : PseudoMetricSpace (X.Carrier ⊕ Y.Carrier) //
      Amalgamates X Y m} => ambientCost X Y m.val) ⟨m.toPseudoMetricSpace, hm⟩).trans
  let : MetricSpace (X.Carrier ⊕ Y.Carrier) := m
  let : MeasurableSpace (X.Carrier ⊕ Y.Carrier) := borel _
  let : BorelSpace (X.Carrier ⊕ Y.Carrier) := ⟨rfl⟩
  have hclose : ∀ z, dist (Sum.inl (f z) : X.Carrier ⊕ Y.Carrier) (Sum.inr (g z)) = ε :=
    Metric.glueDist_glued_points f g ε
  have hml : Measurable (Sum.inl : X.Carrier → X.Carrier ⊕ Y.Carrier) :=
    continuous_inl.measurable
  have hmr : Measurable (Sum.inr : Y.Carrier → X.Carrier ⊕ Y.Carrier) :=
    continuous_inr.measurable
  apply max_le
  · apply Metric.hausdorffEDist_le_of_mem_edist
    · rintro _ ⟨x, rfl⟩
      obtain ⟨z, rfl⟩ := hsf x
      refine ⟨Sum.inr (g z), mem_range_self _, ?_⟩
      rw [edist_dist, hclose]
    · rintro _ ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := hsg y
      refine ⟨Sum.inl (f z), mem_range_self _, ?_⟩
      rw [edist_comm, edist_dist, hclose]
  · change levyProkhorovEDist (X.mass.map Sum.inl) (Y.mass.map Sum.inr) ≤ _
    rw [← hmf, ← hmg, Measure.map_map hml hf, Measure.map_map hmr hg]
    apply levyProkhorovEDist_map_le_of_dist μ (hml.comp hf) (hmr.comp hg) hε.le
    exact fun z => (hclose z).le


lemma graph_connected {n : ℕ} (M : RootedMap n) : (graph M univ).Connected :=
  M.out.property.2.2.1

@[instance_reducible]
def mapMetric {n : ℕ} {scale : ℝ} (hscale : 0 < scale) (M : RootedMap n) :
    MetricSpace (Vertex M) where
  dist v w := scale * ((graph M univ).dist v w : ℝ)
  dist_self v := by simp
  dist_comm v w := by rw [SimpleGraph.dist_comm]
  dist_triangle v w z := by
    have h := (graph_connected M).dist_triangle (u := v) (v := w) (w := z)
    have h' : ((graph M univ).dist v z : ℝ) ≤
        ((graph M univ).dist v w : ℝ) + ((graph M univ).dist w z : ℝ) := by exact_mod_cast h
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h' hscale.le
  eq_of_dist_eq_zero {v w} h := by
    have hdist : (graph M univ).dist v w = 0 := by
      exact_mod_cast (mul_eq_zero.mp h).resolve_left hscale.ne'
    exact (graph_connected M).dist_eq_zero_iff.mp hdist

lemma degreeMass_univ {n : ℕ} (M : RootedMap n) : degreeMass M univ = 1 := by
  simp only [degreeMass, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [show (↑(2 * (n + 1)) : ℝ) * (1 / (2 * (n + 1) : ℝ)) = 1 by
    push_cast
    field_simp]
  simp

lemma mapSpace_valid {n : ℕ} {scale : ℝ} (hscale : 0 < scale) (M : RootedMap n) :
    (mapSpace scale M).Valid := by
  let m := mapMetric hscale M
  let : MetricSpace (Vertex M) := m
  let : TopologicalSpace (Vertex M) := m.toUniformSpace.toTopologicalSpace
  have hc : @CompactSpace (Vertex M) m.toUniformSpace.toTopologicalSpace :=
    @Finite.compactSpace (Vertex M) m.toUniformSpace.toTopologicalSpace inferInstance
  refine ⟨m, fun _ _ => rfl, hc, ?_, degreeMass_univ M⟩
  change ⊤ = @borel (Vertex M) m.toUniformSpace.toTopologicalSpace
  exact borel_eq_top_of_discrete.symm

lemma fkWeight_pos {n : ℕ} {q : ℝ} (hq : 0 < q) (M : RootedMap n)
    (A : Finset (Edge M)) : 0 < fkWeight q M A := Real.rpow_pos_of_pos hq _

lemma partition_nonneg {q : ℝ} (hq : 0 < q) (n : ℕ) : 0 ≤ partition q n :=
  Finset.sum_nonneg (fun M _ => Finset.sum_nonneg (fun A _ => (fkWeight_pos hq M A).le))


lemma treeProjection_measurable (e : unitInterval → ℝ) :
    @Measurable _ _ inferInstance (treeSpace e).measurableSpace (treeProjection e) := by
  let t : TopologicalSpace (ExcursionTree e) :=
    TopologicalSpace.coinduced (treeProjection e) inferInstance
  let ms : MeasurableSpace (ExcursionTree e) := borel _
  let bs : BorelSpace (ExcursionTree e) := ⟨rfl⟩
  have hc : Continuous (treeProjection e) := continuous_iff_coinduced_le.mpr le_rfl
  exact hc.measurable

/-- The excursion-to-measured-tree map preserves the exact uniform-time mass. -/
lemma ghpEDist_treeSpace_le {e f : unitInterval → ℝ}
    (he : Continuous e) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t, |e t - f t| ≤ ε) :
    ghpEDist (treeSpace e) (treeSpace f) ≤ ENNReal.ofReal (2 * ε) := by
  apply ghpEDist_le_of_coding (treeSpace_valid he) (treeSpace_valid hf) volume
    (treeProjection e) (treeProjection f) (treeProjection_measurable e)
    (treeProjection_measurable f) (treeProjection_surjective e)
    (treeProjection_surjective f) rfl rfl (by positivity)
  intro s t
  change |excursionDist e (treeProjection e s).out (treeProjection e t).out -
    excursionDist f (treeProjection f s).out (treeProjection f t).out| ≤ _
  rw [excursionDist_out he, excursionDist_out hf]
  convert excursionDist_abs_sub_le he hf s t h using 1; ring

lemma IsGHPTest.continuous_treeSpace {F : MetricMeasureData → ℝ} (hF : IsGHPTest F) :
    Continuous (fun e : C(unitInterval, ℝ) => F (treeSpace e)) := by
  apply Metric.continuous_iff.mpr
  intro e ε hε
  obtain ⟨δ, hδ, hh⟩ := hF.2 (treeSpace e) (treeSpace_valid e.continuous) ε hε
  refine ⟨δ / 4, by positivity, ?_⟩
  intro f hfe
  rw [Real.dist_eq]
  apply hh (treeSpace f) (treeSpace_valid f.continuous)
  apply lt_of_le_of_lt (ghpEDist_treeSpace_le e.continuous f.continuous
    (show 0 < δ / 4 by positivity) ?_) ?_
  · intro t
    have hpoint := ContinuousMap.dist_apply_le_dist (f := f) (g := e) t
    rw [Real.dist_eq, abs_sub_comm] at hpoint
    exact hpoint.trans hfe.le
  · apply (ENNReal.ofReal_lt_ofReal_iff hδ).mpr
    linarith

lemma continuous_standardExcursion {Ω : Type}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : ∀ i, Continuous (B i · ω)) : Continuous (standardExcursion B ω) := by
  unfold standardExcursion
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _
  apply Continuous.pow
  apply Continuous.sub
  · apply (hB i).comp
    exact continuous_subtype_val.subtype_mk _
  · exact continuous_subtype_val.mul continuous_const

lemma standardExcursion_nonneg {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ)
    (ω : Ω) (t : unitInterval) : 0 ≤ standardExcursion B ω t := Real.sqrt_nonneg _

lemma standardExcursion_one {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ)
    (ω : Ω) : standardExcursion B ω 1 = 0 := by
  change Real.sqrt (∑ i : Fin 3, (B i 1 ω - (1 : ℝ) * B i 1 ω) ^ 2) = 0
  simp

lemma standardExcursion_zero {Ω : Type} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hB : ∀ i, B i 0 ω = 0) : standardExcursion B ω 0 = 0 := by
  change Real.sqrt (∑ i : Fin 3, (B i 0 ω - (0 : ℝ) * B i 1 ω) ^ 2) = 0
  simp [hB]

lemma standardExcursion_ae_continuous {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, Continuous (standardExcursion B ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => (hB i).cont)] with ω hω
  exact continuous_standardExcursion hω

lemma standardExcursion_ae_zero {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, standardExcursion B ω 0 = 0 := by
  filter_upwards [ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)] with ω hω
  exact standardExcursion_zero hω

lemma standardExcursion_treeSpace_ae_valid {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, (treeSpace (standardExcursion B ω)).Valid :=
  (standardExcursion_ae_continuous hB).mono (fun _ he => treeSpace_valid he)


local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

/-- A continuous-path version of the standard excursion; the fallback occurs
only on a null set under the standing Brownian hypotheses. -/
def standardExcursionPath {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    C(unitInterval, ℝ) := ContinuousMap.mkD (standardExcursion B ω) 0

lemma standardExcursionPath_ae_eq {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, (standardExcursionPath B ω : unitInterval → ℝ) = standardExcursion B ω := by
  filter_upwards [standardExcursion_ae_continuous hB] with ω hω
  funext t
  exact ContinuousMap.mkD_apply_of_continuous hω

lemma standardExcursion_eval_aemeasurable {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) (t : unitInterval) :
    AEMeasurable (fun ω => standardExcursion B ω t) P := by
  unfold standardExcursion
  apply AEMeasurable.sqrt
  apply Finset.aemeasurable_fun_sum
  intro i _
  exact ((hB i).aemeasurable ⟨(t : ℝ), t.property.1⟩).sub
    (((hB i).aemeasurable 1).const_mul (t : ℝ)) |>.pow_const 2

/-- Evaluation on a countable dense set recovers the Borel structure of the
uniform topology. This avoids any unproved stochastic-process measurability. -/
lemma continuousMap_dense_eval_measurableEmbedding :
    MeasurableEmbedding (fun f : C(unitInterval, ℝ) =>
      fun n : ℕ => f (TopologicalSpace.denseSeq unitInterval n)) := by
  apply Continuous.measurableEmbedding
  · apply continuous_pi
    intro n
    fun_prop
  · intro f g hfg
    apply ContinuousMap.ext
    have hh := (TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
      f.continuous g.continuous hfg
    exact congrFun hh

lemma standardExcursionPath_aemeasurable {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) :
    AEMeasurable (standardExcursionPath B) P := by
  apply continuousMap_dense_eval_measurableEmbedding.aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro n
  apply (standardExcursion_eval_aemeasurable hB _).congr
  filter_upwards [standardExcursionPath_ae_eq hB] with ω hω
  exact (congrFun hω _).symm

lemma IsGHPTest.brownian_integrable {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsBrownianReal (B i) P) {F : MetricMeasureData → ℝ}
    (hF : IsGHPTest F) : Integrable (fun ω => F (treeSpace (standardExcursion B ω))) P := by
  have hm : AEMeasurable (fun ω => F (treeSpace (standardExcursion B ω))) P := by
    apply (hF.continuous_treeSpace.measurable.comp_aemeasurable
      (standardExcursionPath_aemeasurable hB)).congr
    filter_upwards [standardExcursionPath_ae_eq hB] with ω hω
    exact congrArg (fun e => F (treeSpace e)) hω
  obtain ⟨C, hC⟩ := hF.1
  apply (integrable_const C).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hC _)

end FKCRT
end

end OAI
