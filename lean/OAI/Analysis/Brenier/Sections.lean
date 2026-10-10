import OAI.Analysis.Brenier.Interfaces

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology

namespace Problem358
namespace AffineSlice

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A vertical affine section of a set in a product vector space. -/
def fiber (K : Set (U × V)) (p : U) : Set V := (fun y => (p, y)) ⁻¹' K

omit [NormedSpace ℝ U] [NormedSpace ℝ V] in
theorem isClosed_fiber {K : Set (U × V)} (hK : IsClosed K) (p : U) :
    IsClosed (fiber K p) := hK.preimage (continuous_const.prodMk continuous_id)

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem fiber_subset_projection (K : Set (U × V)) (p : U) :
    fiber K p ⊆ Prod.snd '' K := fun y hy => ⟨(p, y), hy, rfl⟩

omit [NormedSpace ℝ U] [NormedSpace ℝ V] in
theorem isCompact_fiber {K : Set (U × V)} (hK : IsCompact K) (p : U) :
    IsCompact (fiber K p) :=
  (hK.image continuous_snd).of_isClosed_subset (isClosed_fiber hK.isClosed p)
    (fiber_subset_projection K p)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [IsAddHaarMeasure μ]

/-- Fiber volume is continuous at every prefix whose fiber crosses the interior.
This supplies the density-continuity step of triangular uniform parametrization. -/
theorem continuousAt_fiberMeasure {K : Set (U × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {p : U} (hp : ∃ y : V, (p, y) ∈ interior K) :
    ContinuousAt (fun q => μ (fiber K q)) p := by
  let f : V →ᵃ[ℝ] U × V := (AffineMap.const ℝ V p).prod (AffineMap.id ℝ V)
  have hmeet : (f ⁻¹' interior K).Nonempty := hp
  have hlim : ∀ᵐ y ∂μ,
      Tendsto (fun q : U => K.indicator (fun _ => (1 : ℝ)) (q, y)) (𝓝 p)
        (𝓝 (K.indicator (fun _ => (1 : ℝ)) (p, y))) := by
    apply ae_tendsto_indicator_on_affine_slice μ f hK.isClosed hconv hmeet
      continuousOn_const
    exact ae_of_all μ fun y => by
      simpa [f] using (continuous_id.prodMk (continuous_const :
        Continuous (fun _ : U => y))).tendsto p
  have hevent : ∀ᵐ y ∂μ, ∀ᶠ q in 𝓝 p, y ∈ fiber K q ↔ y ∈ fiber K p := by
    filter_upwards [hlim] with y hy
    apply (tendsto_indicator_const_apply_iff_eventually (𝓝 p) (1 : ℝ) y).mp
    have heq : ∀ q : U, (fiber K q).indicator (fun _ : V => (1 : ℝ)) y =
        K.indicator (fun _ : U × V => (1 : ℝ)) (q, y) := by
      intro q
      exact Set.indicator_comp_right (s := K) (g := fun _ : U × V => (1 : ℝ))
        (x := y) (fun z : V => (q, z))
    simpa only [heq] using hy
  exact tendsto_measure_of_ae_tendsto_indicator (𝓝 p)
    (isClosed_fiber hK.isClosed p).measurableSet
    (fun q => (isClosed_fiber hK.isClosed q).measurableSet)
    (hK.image continuous_snd).measurableSet (hK.image continuous_snd).measure_ne_top
    (Eventually.of_forall (fiber_subset_projection K)) hevent

/-- The same slice-volume continuity in real, rather than extended-real, values. -/
theorem continuousAt_fiberMeasureReal {K : Set (U × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {p : U} (hp : ∃ y : V, (p, y) ∈ interior K) :
    ContinuousAt (fun q => μ.real (fiber K q)) p := by
  have hfin : μ (fiber K p) ≠ ⊤ := (isCompact_fiber hK p).measure_ne_top
  exact ContinuousAt.comp (f := fun q => μ (fiber K q)) (g := ENNReal.toReal)
    (ENNReal.continuousAt_toReal hfin) (continuousAt_fiberMeasure μ hK hconv hp)

omit [NormedSpace ℝ U] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A fiber crossing the interior has positive volume. -/
theorem fiberMeasure_pos {K : Set (U × V)} {p : U}
    (hp : ∃ y : V, (p, y) ∈ interior K) : 0 < μ (fiber K p) := by
  obtain ⟨y, hy⟩ := hp
  apply measure_pos_of_nonempty_interior
  refine ⟨y, ?_⟩
  exact preimage_interior_subset_interior_preimage
    (continuous_const.prodMk continuous_id) hy

omit [NormedSpace ℝ U] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- Positivity survives conversion to real for compact fibers. -/
theorem fiberMeasureReal_pos {K : Set (U × V)} (hK : IsCompact K) {p : U}
    (hp : ∃ y : V, (p, y) ∈ interior K) : 0 < μ.real (fiber K p) := by
  exact ENNReal.toReal_pos (fiberMeasure_pos μ hp).ne' (isCompact_fiber hK p).measure_ne_top

end AffineSlice
end Problem358

end

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem358
namespace SectionMeasure

/-- The fiber of a product set over its first coordinate. -/
def fiber {A B : Type*} (U : Set (A × B)) (a : A) : Set B :=
  {b | (a, b) ∈ U}

/-- A fiber is nonempty exactly when its prefix belongs to the projection. -/
theorem fiber_nonempty_iff {A B : Type*} (U : Set (A × B)) (a : A) :
    (fiber U a).Nonempty ↔ a ∈ Prod.fst '' U := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(a, b), hb, rfl⟩
  · rintro ⟨⟨a', b⟩, hab, ha⟩
    dsimp at ha
    subst a'
    exact ⟨b, hab⟩

/-- Fibers of open sets are open. -/
theorem isOpen_fiber {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {U : Set (A × B)} (hU : IsOpen U) (a : A) : IsOpen (fiber U a) :=
  hU.preimage (continuous_const.prodMk continuous_id)

/-- Prefix domains of open sets are open. -/
theorem isOpen_projection {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {U : Set (A × B)} (hU : IsOpen U) : IsOpen (Prod.fst '' U) :=
  isOpenMap_fst _ hU

/-- Open fibers have positive mass exactly on the prefix domain. -/
theorem fiber_measure_pos_iff {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace B]
    (ν : Measure B) [Measure.IsOpenPosMeasure ν]
    {U : Set (A × B)} (hU : IsOpen U) (a : A) :
    0 < ν (fiber U a) ↔ a ∈ Prod.fst '' U := by
  rw [(isOpen_fiber hU a).measure_pos_iff ν, fiber_nonempty_iff]

/-- A compact ambient envelope bounds every fiber by the same compact projection. -/
theorem fiber_measure_ne_top_of_subset_compact {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace B]
    (ν : Measure B) [IsFiniteMeasureOnCompacts ν]
    {U K : Set (A × B)} (hK : IsCompact K) (hUK : U ⊆ K) (a : A) :
    ν (fiber U a) ≠ ∞ := by
  apply ne_top_of_le_ne_top ((hK.image continuous_snd).measure_ne_top (μ := ν))
  apply measure_mono
  intro b hb
  exact ⟨(a, b), hUK hb, rfl⟩

/-- Conditional section densities are strictly positive and finite on the prefix domain. -/
theorem fiber_measure_toReal_pos {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [MeasurableSpace B]
    (ν : Measure B) [Measure.IsOpenPosMeasure ν] [IsFiniteMeasureOnCompacts ν]
    {U K : Set (A × B)} (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K)
    {a : A} (ha : a ∈ Prod.fst '' U) :
    0 < (ν (fiber U a)).toReal := by
  exact ENNReal.toReal_pos ((fiber_measure_pos_iff ν hU a).2 ha).ne'
    (fiber_measure_ne_top_of_subset_compact ν hK hUK a)

/-- Every fiber of a convex product set is convex. -/
theorem convex_fiber {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module ℝ A] [Module ℝ B] {U : Set (A × B)} (hU : Convex ℝ U) (a : A) :
    Convex ℝ (fiber U a) := by
  intro x hx y hy r s hr hs hrs
  have h := hU hx hy hr hs hrs
  simpa only [fiber, Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hrs, one_smul] using h

/-- Projecting a convex product set preserves convexity. -/
theorem convex_projection {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module ℝ A] [Module ℝ B] {U : Set (A × B)} (hU : Convex ℝ U) :
    Convex ℝ (Prod.fst '' U) :=
  hU.linear_image (LinearMap.fst ℝ A B)

/-- A nonempty bounded open convex subset of the real line is its endpoint interval. -/
theorem eq_Ioo_csInf_csSup_of_open_convex {S : Set ℝ}
    (hS : IsOpen S) (hc : Convex ℝ S) (hne : S.Nonempty)
    (hl : BddBelow S) (hu : BddAbove S) :
    S = Ioo (sInf S) (sSup S) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hx
    have hm : x - ε / 2 ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      have ht : x - ε / 2 - x = -(ε / 2) := by ring
      rw [ht, abs_neg, abs_of_pos (by positivity)]
      linarith)
    have hp : x + ε / 2 ∈ S := hball (by
      rw [Metric.mem_ball, Real.dist_eq]
      have ht : x + ε / 2 - x = ε / 2 := by ring
      rw [ht, abs_of_pos (by positivity)]
      linarith)
    exact ⟨(csInf_le hl hm).trans_lt (by linarith),
      lt_of_lt_of_le (by linarith : x < x + ε / 2) (le_csSup hu hp)⟩
  · exact (show IsConnected S from ⟨hne, Real.convex_iff_isPreconnected.mp hc⟩).Ioo_csInf_csSup_subset hl hu

/-- Nonempty scalar fibers of a bounded open convex set are bounded open intervals. -/
theorem exists_fiber_eq_Ioo {A : Type*} [TopologicalSpace A]
    [AddCommMonoid A] [Module ℝ A]
    {U K : Set (A × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    (hK : IsCompact K) (hUK : U ⊆ K) {a : A} (ha : a ∈ Prod.fst '' U) :
    ∃ l r : ℝ, l < r ∧ fiber U a = Ioo l r := by
  have hne : (fiber U a).Nonempty := (fiber_nonempty_iff U a).2 ha
  have hb : Bornology.IsBounded (fiber U a) :=
    (hK.image continuous_snd).isBounded.subset (by
      intro b hb
      exact ⟨(a, b), hUK hb, rfl⟩)
  have heq := eq_Ioo_csInf_csSup_of_open_convex (isOpen_fiber hU a)
    (convex_fiber hc a) hne hb.bddBelow hb.bddAbove
  refine ⟨sInf (fiber U a), sSup (fiber U a), ?_, heq⟩
  obtain ⟨x, hx⟩ := hne
  rw [heq] at hx
  exact hx.1.trans hx.2

/-- Section volume is a measurable function of its prefix. -/
theorem measurable_fiber_measure {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U) :
    Measurable (fun a => ν (fiber U a)) :=
  measurable_measure_prodMk_left hU

/-- Real-valued section volume is measurable, including the zero extension outside the projection. -/
theorem measurable_fiber_measure_toReal {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] {U : Set (A × B)} (hU : MeasurableSet U) :
    Measurable (fun a => (ν (fiber U a)).toReal) :=
  (measurable_fiber_measure ν hU).ennreal_toReal

/-- Tonelli's recursion for section volumes. -/
theorem lintegral_fiber_measure {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    {U : Set (A × B)} (hU : MeasurableSet U) :
    (∫⁻ a, ν (fiber U a) ∂μ) = (μ.prod ν) U :=
  (Measure.prod_apply hU).symm

/-- Finite section mass gives the real-valued recursion used by conditional densities. -/
theorem integral_fiber_measure_toReal {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    {U : Set (A × B)} (hU : MeasurableSet U) (hfin : (μ.prod ν) U ≠ ∞) :
    (∫ a, (ν (fiber U a)).toReal ∂μ) = ((μ.prod ν) U).toReal := by
  rw [integral_toReal (measurable_fiber_measure ν hU).aemeasurable
    (Measure.ae_measure_lt_top hU hfin)]
  rw [lintegral_fiber_measure μ ν hU]

/-- A positive finite section mass normalizes its conditional section density to one. -/
theorem integral_normalized_fiber_measure {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    {U : Set (A × B)} (hU : MeasurableSet U) (hfin : (μ.prod ν) U ≠ ∞)
    (hpos : 0 < ((μ.prod ν) U).toReal) :
    (∫ a, (ν (fiber U a)).toReal / ((μ.prod ν) U).toReal ∂μ) = 1 := by
  rw [integral_div, integral_fiber_measure_toReal μ ν hU hfin, div_self hpos.ne']

end SectionMeasure
end Problem358

namespace Problem358.SectionMarginal

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite ν]

/-- Integrating a product density over the second coordinate computes its
actual first marginal. -/
theorem map_fst_withDensity (q : A × B → ℝ≥0∞) (hq : Measurable q) :
    Measure.map Prod.fst ((μ.prod ν).withDensity q) =
      μ.withDensity (fun a => ∫⁻ b, q (a, b) ∂ν) := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs,
    withDensity_apply q (hs.preimage measurable_fst),
    withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage measurable_fst),
    lintegral_prod _ ((hq.indicator (hs.preimage measurable_fst)).aemeasurable),
    ← lintegral_indicator hs]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ s <;> simp [ha]

/-- A body restricted from a product measure has section-volume density in its
first marginal. This remains valid for zero and infinite total body measure. -/
theorem map_fst_restrict (U : Set (A × B)) (hU : MeasurableSet U) :
    Measure.map Prod.fst ((μ.prod ν).restrict U) =
      μ.withDensity (fun a => ν {b | (a, b) ∈ U}) := by
  rw [← withDensity_indicator_one hU]
  change Measure.map Prod.fst ((μ.prod ν).withDensity
    (U.indicator (fun _ => (1 : ℝ≥0∞)))) = _
  rw [map_fst_withDensity μ ν _ (measurable_const.indicator hU)]
  congr 1
  funext a
  change (∫⁻ b, ({b | (a, b) ∈ U}.indicator (fun _ => (1 : ℝ≥0∞))) b ∂ν) = _
  have hs : MeasurableSet {b | (a, b) ∈ U} :=
    hU.preimage (measurable_const.prodMk measurable_id)
  rw [lintegral_indicator hs]
  simp

/-- The normalized body law has the common total-volume normalization, rather
than a separate normalization of each prefix. -/
theorem map_fst_normalized_restrict (U : Set (A × B)) (hU : MeasurableSet U) :
    Measure.map Prod.fst (((μ.prod ν) U)⁻¹ • (μ.prod ν).restrict U) =
      ((μ.prod ν) U)⁻¹ • μ.withDensity (fun a => ν {b | (a, b) ∈ U}) := by
  rw [Measure.map_smul _ measurable_fst.aemeasurable, map_fst_restrict μ ν U hU]

/-- Section masses integrate to the total body mass. -/
theorem lintegral_sections (U : Set (A × B)) (hU : MeasurableSet U) :
    (∫⁻ a, ν {b | (a, b) ∈ U} ∂μ) = (μ.prod ν) U :=
  (Measure.prod_apply hU).symm

end Problem358.SectionMarginal

end

section

open MeasureTheory Set
open scoped ENNReal

namespace Problem358.SectionMass

/-- The mass of a vertical section of a set. -/
def mass {X Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (U : Set (X × Y)) (x : X) : ℝ≥0∞ :=
  ν (Prod.mk x ⁻¹' U)

lemma measurable_mass {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] {U : Set (X × Y)} (hU : MeasurableSet U) :
    Measurable (mass ν U) :=
  measurable_measure_prodMk_left hU

lemma measurable_mass_toReal {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] {U : Set (X × Y)} (hU : MeasurableSet U) :
    Measurable (fun x => (mass ν U x).toReal) :=
  (measurable_mass ν hU).ennreal_toReal

lemma positive_iff_mem_projection {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) [Measure.IsOpenPosMeasure ν] {U : Set (X × Y)} (hU : IsOpen U) (x : X) :
    0 < mass ν U x ↔ x ∈ Prod.fst '' U := by
  have hcont : Continuous (Prod.mk x : Y → X × Y) := continuous_const.prodMk continuous_id
  rw [mass, (hU.preimage hcont).measure_pos_iff ν]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩
  · rintro ⟨⟨z, y⟩, hy, hz⟩
    have hzx : z = x := hz
    exact ⟨y, by simpa [hzx] using hy⟩

lemma isOpen_positive_mass {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    (ν : Measure Y) [Measure.IsOpenPosMeasure ν] {U : Set (X × Y)} (hU : IsOpen U) :
    IsOpen {x | 0 < mass ν U x} := by
  have heq : {x | 0 < mass ν U x} = Prod.fst '' U := by
    ext x
    exact positive_iff_mem_projection ν hU x
  rw [heq]
  exact isOpenMap_fst _ hU

/-- Compact ambient sets have compact vertical sections, in arbitrary factors. -/
lemma isCompact_fiber {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    {K : Set (X × Y)} (hK : IsCompact K) (x : X) :
    IsCompact (Prod.mk x ⁻¹' K) := by
  have hs : IsCompact (K ∩ Prod.fst ⁻¹' {x}) :=
    hK.inter_right (isClosed_singleton.preimage continuous_fst)
  have heq : Prod.mk x ⁻¹' K = Prod.snd '' (K ∩ Prod.fst ⁻¹' {x}) := by
    ext y
    constructor
    · intro hy
      exact ⟨(x, y), ⟨hy, rfl⟩, rfl⟩
    · rintro ⟨⟨z, t⟩, ⟨hp, hz⟩, ht⟩
      have hzx : z = x := hz
      have hty : t = y := ht
      simpa [hzx, hty] using hp
  rw [heq]
  exact hs.image continuous_snd

lemma mass_lt_top_of_compact {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [MeasurableSpace Y] (ν : Measure Y) [IsLocallyFiniteMeasure ν]
    {K : Set (X × Y)} (hK : IsCompact K) (x : X) :
    mass ν K x < ∞ :=
  (isCompact_fiber hK x).measure_lt_top

/-- On the projection of the interior of a compact body, its section density is
strictly positive and finite. These are the denominators of conditional densities. -/
lemma interior_mass_pos_lt_top {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [MeasurableSpace Y] (ν : Measure Y)
    [Measure.IsOpenPosMeasure ν] [IsLocallyFiniteMeasure ν]
    {K : Set (X × Y)} (hK : IsCompact K) {x : X}
    (hx : x ∈ Prod.fst '' interior K) :
    0 < mass ν (interior K) x ∧
      mass ν (interior K) x ≤ mass ν K x ∧ mass ν K x < ∞ := by
  refine ⟨(positive_iff_mem_projection ν isOpen_interior x).mpr hx, ?_,
    mass_lt_top_of_compact ν hK x⟩
  exact measure_mono (Set.preimage_mono interior_subset)

/-- The positivity domain of section masses of an open convex set is convex. -/
lemma convex_positive_mass {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
    (ν : Measure Y) [Measure.IsOpenPosMeasure ν]
    {U : Set (X × Y)} (hU : IsOpen U) (hc : Convex ℝ U) :
    Convex ℝ {x | 0 < mass ν U x} := by
  have heq : {x | 0 < mass ν U x} = Prod.fst '' U := by
    ext x
    exact positive_iff_mem_projection ν hU x
  rw [heq]
  exact hc.linear_image (LinearMap.fst ℝ X Y)

/-- Successive section masses satisfy the exact Tonelli recursion. -/
lemma mass_prod {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (ρ : Measure Z) [SFinite ρ]
    {U : Set (X × (Y × Z))} (hU : MeasurableSet U) (x : X) :
    mass (ν.prod ρ) U x =
      ∫⁻ y, ρ {z | (x, (y, z)) ∈ U} ∂ν := by
  exact Measure.prod_apply (hU.preimage measurable_prodMk_left)

lemma interior_mass_toReal_pos {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    [MeasurableSpace Y] (ν : Measure Y)
    [Measure.IsOpenPosMeasure ν] [IsLocallyFiniteMeasure ν]
    {K : Set (X × Y)} (hK : IsCompact K) {x : X}
    (hx : x ∈ Prod.fst '' interior K) :
    0 < (mass ν (interior K) x).toReal := by
  obtain ⟨hpos, hle, hfin⟩ := interior_mass_pos_lt_top ν hK hx
  exact ENNReal.toReal_pos hpos.ne' (ne_of_lt (lt_of_le_of_lt hle hfin))

end Problem358.SectionMass

end

noncomputable section
open Set MeasureTheory

namespace Problem358.SectionMeasure

/-- The lower endpoint of a nonempty open scalar fiber is upper semicontinuous
in its prefix. No convexity is needed for this regularity statement. -/
theorem upperSemicontinuous_fiber_inf {A : Type*} [TopologicalSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddBelow (fiber U a)) :
    UpperSemicontinuous (fun a : Prod.fst '' U => sInf (fiber U a.val)) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro r
  have hopen : IsOpen (Prod.fst '' (U ∩ Prod.snd ⁻¹' Iio r)) :=
    isOpen_projection (hU.inter (isOpen_Iio.preimage continuous_snd))
  have heq : (fun a : Prod.fst '' U => sInf (fiber U a.val)) ⁻¹' Iio r =
      Subtype.val ⁻¹' (Prod.fst '' (U ∩ Prod.snd ⁻¹' Iio r)) := by
    ext a
    change sInf (fiber U a.val) < r ↔ a.val ∈ Prod.fst '' (U ∩ Prod.snd ⁻¹' Iio r)
    rw [csInf_lt_iff (hb a.val a.property) ((fiber_nonempty_iff U a.val).2 a.property)]
    constructor
    · rintro ⟨t, ht, htr⟩
      exact ⟨(a.val, t), ⟨ht, htr⟩, rfl⟩
    · rintro ⟨⟨a', t⟩, ⟨ht, htr⟩, ha⟩
      dsimp at ha
      subst a'
      exact ⟨t, ht, htr⟩
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- The upper endpoint is lower semicontinuous on the valid-prefix domain. -/
theorem lowerSemicontinuous_fiber_sup {A : Type*} [TopologicalSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddAbove (fiber U a)) :
    LowerSemicontinuous (fun a : Prod.fst '' U => sSup (fiber U a.val)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  have hopen : IsOpen (Prod.fst '' (U ∩ Prod.snd ⁻¹' Ioi r)) :=
    isOpen_projection (hU.inter (isOpen_Ioi.preimage continuous_snd))
  have heq : (fun a : Prod.fst '' U => sSup (fiber U a.val)) ⁻¹' Ioi r =
      Subtype.val ⁻¹' (Prod.fst '' (U ∩ Prod.snd ⁻¹' Ioi r)) := by
    ext a
    change r < sSup (fiber U a.val) ↔ a.val ∈ Prod.fst '' (U ∩ Prod.snd ⁻¹' Ioi r)
    rw [lt_csSup_iff (hb a.val a.property) ((fiber_nonempty_iff U a.val).2 a.property)]
    constructor
    · rintro ⟨t, ht, hrt⟩
      exact ⟨(a.val, t), ⟨ht, hrt⟩, rfl⟩
    · rintro ⟨⟨a', t⟩, ⟨ht, hrt⟩, ha⟩
      dsimp at ha
      subst a'
      exact ⟨t, ht, hrt⟩
  rw [heq]
  exact hopen.preimage continuous_subtype_val

/-- Lower scalar-section endpoints are Borel functions of their valid prefix. -/
theorem measurable_fiber_inf {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddBelow (fiber U a)) :
    Measurable (fun a : Prod.fst '' U => sInf (fiber U a.val)) :=
  (upperSemicontinuous_fiber_inf hU hb).measurable

/-- Upper scalar-section endpoints are Borel functions of their valid prefix. -/
theorem measurable_fiber_sup {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    {U : Set (A × ℝ)} (hU : IsOpen U)
    (hb : ∀ a ∈ Prod.fst '' U, BddAbove (fiber U a)) :
    Measurable (fun a : Prod.fst '' U => sSup (fiber U a.val)) :=
  (lowerSemicontinuous_fiber_sup hU hb).measurable

/-- A bounded open convex region has a measurably varying interval description
of all of its nonempty scalar sections. -/
theorem exists_measurable_fiber_endpoints {A : Type*} [TopologicalSpace A]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    [AddCommMonoid A] [Module ℝ A]
    {U K : Set (A × ℝ)} (hU : IsOpen U) (hc : Convex ℝ U)
    (hK : IsCompact K) (hUK : U ⊆ K) :
    ∃ l r : (Prod.fst '' U) → ℝ, Measurable l ∧ Measurable r ∧
      ∀ a, l a < r a ∧ fiber U a.val = Ioo (l a) (r a) := by
  have hb : ∀ a : A, Bornology.IsBounded (fiber U a) := by
    intro a
    apply (hK.image continuous_snd).isBounded.subset
    intro t ht
    exact ⟨(a, t), hUK ht, rfl⟩
  refine ⟨(fun a => sInf (fiber U a.val)), (fun a => sSup (fiber U a.val)),
    measurable_fiber_inf hU (fun a _ => (hb a).bddBelow),
    measurable_fiber_sup hU (fun a _ => (hb a).bddAbove), ?_⟩
  intro a
  have hne := (fiber_nonempty_iff U a.val).2 a.property
  have heq := eq_Ioo_csInf_csSup_of_open_convex (isOpen_fiber hU a.val)
    (convex_fiber hc a.val) hne (hb a.val).bddBelow (hb a.val).bddAbove
  refine ⟨?_, heq⟩
  obtain ⟨t, ht⟩ := hne
  rw [heq] at ht
  exact ht.1.trans ht.2

/-- The scalar projection of each remaining multidimensional section has
measurable interval endpoints. This is the support interval for conditional quantiles. -/
theorem exists_measurable_projected_fiber_endpoints {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [OpensMeasurableSpace A]
    [AddCommMonoid A] [Module ℝ A] [AddCommMonoid B] [Module ℝ B]
    {U K : Set ((A × ℝ) × B)} (hU : IsOpen U) (hc : Convex ℝ U)
    (hK : IsCompact K) (hUK : U ⊆ K) :
    ∃ l r : (Prod.fst '' (Prod.fst '' U)) → ℝ,
      Measurable l ∧ Measurable r ∧ ∀ a,
        l a < r a ∧ {t | ∃ b, ((a.val, t), b) ∈ U} = Ioo (l a) (r a) := by
  obtain ⟨l, r, hl, hr, hinterval⟩ := exists_measurable_fiber_endpoints
    (isOpen_projection hU) (convex_projection hc)
    (hK.image continuous_fst) (Set.image_mono hUK)
  refine ⟨l, r, hl, hr, ?_⟩
  intro a
  refine ⟨(hinterval a).1, ?_⟩
  rw [← (hinterval a).2]
  ext t
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨((a.val,t),b), hb, rfl⟩
  · rintro ⟨⟨p,b⟩, hb, hp⟩
    dsimp at hp
    subst p
    exact ⟨b,hb⟩

end Problem358.SectionMeasure

end

end OAI
