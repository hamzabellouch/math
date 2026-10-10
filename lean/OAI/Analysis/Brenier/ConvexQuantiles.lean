import OAI.Analysis.Brenier.ConvexDensity
import OAI.Analysis.Brenier.Quantiles

namespace OAI

noncomputable section

open Set MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

namespace Problem358
namespace AffineSlice

/-- Normalized restrictions of a jointly measurable family form a kernel.
No normalization assertion is made at zero or infinite mass. -/
def normalizedBodyKernel {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ν : Measure B) [SFinite ν] (K : A → Set B)
    (hK : MeasurableSet {p : A × B | p.2 ∈ K p.1}) : Kernel A B where
  toFun a := (ν (K a))⁻¹ • ν.restrict (K a)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hmass : Measurable (fun a => ν (K a)) :=
      measurable_measure_prodMk_left hK
    have hinter : Measurable (fun a => ν (s ∩ K a)) :=
      measurable_measure_prodMk_left ((hs.preimage measurable_snd).inter hK)
    simp only [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact (measurable_inv.comp hmass).mul hinter

theorem normalizedBodyKernel_apply {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (ν : Measure B) [SFinite ν]
    (K : A → Set B) (hK : MeasurableSet {p : A × B | p.2 ∈ K p.1}) (a : A) :
    normalizedBodyKernel ν K hK a = (ν (K a))⁻¹ • ν.restrict (K a) := rfl

theorem normalizedBodyKernel_isMarkov {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (ν : Measure B) [SFinite ν]
    (K : A → Set B) (hK : MeasurableSet {p : A × B | p.2 ∈ K p.1})
    (hzero : ∀ a, ν (K a) ≠ 0) (htop : ∀ a, ν (K a) ≠ ∞) :
    IsMarkovKernel (normalizedBodyKernel ν K hK) := by
  constructor
  intro a
  constructor
  change ((ν (K a))⁻¹ • ν.restrict (K a)) univ = 1
  simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (hzero a) (htop a)

/-- Jointly measurable exact scalar quantiles for a measurable family of
compact convex bodies. Support endpoints need not be chosen measurably.
The derivative and law use the actual section volumes of each body. -/
theorem exists_measurable_scalar_quantile_family_of_convex_body
    {A V : Type*} [MeasurableSpace A]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsAddHaarMeasure μ]
    (K : A → Set (ℝ × V))
    (hfamily : MeasurableSet {p : A × (ℝ × V) | p.2 ∈ K p.1})
    (hcompact : ∀ a, IsCompact (K a))
    (hconvex : ∀ a, Convex ℝ (K a))
    (hinterior : ∀ a, (interior (K a)).Nonempty) :
    ∃ Q : A × ℝ → ℝ, Measurable Q ∧
      (∀ a s, s ∈ Ioo (0 : ℝ) 1 → Q (a, s) ∈ Prod.fst '' interior (K a)) ∧
      (∀ a s, s ∈ Ioo (0 : ℝ) 1 → HasDerivAt (fun t => Q (a, t))
        ((volume.prod μ).real (K a) / μ.real (fiber (K a) (Q (a, s)))) s) ∧
      ∀ a, Measure.map (fun t => Q (a, t)) (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst
          (((volume.prod μ) (K a))⁻¹ • (volume.prod μ).restrict (K a)) := by
  classical
  choose D hden hinterval using fun a =>
    exists_positiveIntervalDensity_of_convex_body μ (hcompact a) (hconvex a) (hinterior a)
  let κ : Kernel A (ℝ × V) := normalizedBodyKernel (volume.prod μ) K hfamily
  have : IsMarkovKernel κ := normalizedBodyKernel_isMarkov (volume.prod μ) K hfamily
    (fun a => (measure_pos_of_nonempty_interior (volume.prod μ) (hinterior a)).ne')
    (fun a => (hcompact a).measure_ne_top)
  have heq : ∀ a, κ.fst a = (D a).densityMeasure := by
    intro a
    exact (densityMeasure_eq_scalar_marginal μ (hcompact a) (hconvex a)
      (hinterior a) (D a) (hden a) (hinterval a)).symm
  obtain ⟨Q, hQ, hlaw, hmatch, hderiv⟩ :=
    PositiveIntervalDensity.exists_measurable_density_kernel_quantiles D κ.fst heq
  refine ⟨Q, hQ, ?_, ?_, ?_⟩
  · intro a s hs
    rw [hmatch a s hs, ← hinterval a]
    exact (D a).quantileReal_mem_interior hs
  · intro a s hs
    have hd := hderiv a s hs
    rw [hden a, inv_div] at hd
    exact hd
  · intro a
    exact hlaw a

end AffineSlice
end Problem358

end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal Topology

namespace Problem358.AffineSlice

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Taking a prefix section preserves convexity. -/
theorem convex_fiber {K : Set (U × V)} (hK : Convex ℝ K) (p : U) :
    Convex ℝ (fiber K p) :=
  hK.affine_preimage ((AffineMap.const ℝ V p).prod (AffineMap.id ℝ V))

/-- At valid prefixes, interior and section commute exactly. -/
theorem interior_fiber_eq {K : Set (U × V)} (hK : Convex ℝ K)
    {p : U} (hp : ∃ v : V, (p, v) ∈ interior K) :
    interior (fiber K p) = fiber (interior K) p := by
  exact interior_affine_preimage_eq
    ((AffineMap.const ℝ V p).prod (AffineMap.id ℝ V))
    (continuous_const.prodMk continuous_id) hK hp

/-- A valid prefix section remains a full-dimensional compact convex body. -/
theorem prefix_section_body {K : Set (U × V)} (hK : IsCompact K)
    (hconv : Convex ℝ K) {p : U} (hp : ∃ v : V, (p, v) ∈ interior K) :
    IsCompact (fiber K p) ∧ Convex ℝ (fiber K p) ∧
      (interior (fiber K p)).Nonempty := by
  refine ⟨isCompact_fiber hK p, convex_fiber hconv p, ?_⟩
  rw [interior_fiber_eq hconv hp]
  exact hp

/-- Membership in the next scalar projection means precisely that the extended
prefix admits an interior completion. -/
theorem mem_projection_interior_fiber_iff {K : Set (U × (ℝ × V))}
    (hconv : Convex ℝ K) {p : U} (hp : ∃ z : ℝ × V, (p, z) ∈ interior K)
    (t : ℝ) :
    t ∈ Prod.fst '' interior (fiber K p) ↔ ∃ v : V, (p, (t, v)) ∈ interior K := by
  rw [interior_fiber_eq hconv hp]
  constructor
  · rintro ⟨⟨u, v⟩, huv, hu⟩
    dsimp at hu
    subst u
    exact ⟨v, huv⟩
  · rintro ⟨v, hv⟩
    exact ⟨(t, v), hv, rfl⟩

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Every valid prefix supplies an actual positive scalar density, with its
support equal to the valid next-prefix interval. No geometric premise remains. -/
theorem exists_positiveIntervalDensity_of_prefix
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (U × (ℝ × V))} (hK : IsCompact K) (hconv : Convex ℝ K)
    {p : U} (hp : ∃ z : ℝ × V, (p, z) ∈ interior K) :
    ∃ D : PositiveIntervalDensity,
      D.density = (fun t => μ.real (fiber (fiber K p) t) /
        (volume.prod μ).real (fiber K p)) ∧
      (∀ t : ℝ, t ∈ Ioo D.lower D.upper ↔ ∃ v : V, (p, (t, v)) ∈ interior K) ∧
      D.densityMeasure = Measure.map Prod.fst
        (((volume.prod μ) (fiber K p))⁻¹ • (volume.prod μ).restrict (fiber K p)) := by
  obtain ⟨hcompact, hconvex, hne⟩ := prefix_section_body hK hconv hp
  obtain ⟨D, hden, hI⟩ := exists_positiveIntervalDensity_of_convex_body μ hcompact hconvex hne
  refine ⟨D, hden, ?_, densityMeasure_eq_scalar_marginal μ hcompact hconvex hne D hden hI⟩
  intro t
  rw [hI]
  exact mem_projection_interior_fiber_iff hconv hp t

/-- Quantile recursion preserves valid prefixes and has the exact sectional law
and telescoping inverse-density derivative. -/
theorem exists_scalar_quantile_of_prefix
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (U × (ℝ × V))} (hK : IsCompact K) (hconv : Convex ℝ K)
    {p : U} (hp : ∃ z : ℝ × V, (p, z) ∈ interior K) :
    ∃ Q : ℝ → ℝ, Continuous Q ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ∃ v : V, (p, (Q s, v)) ∈ interior K) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Q
        ((volume.prod μ).real (fiber K p) / μ.real (fiber (fiber K p) (Q s))) s) ∧
      Measure.map Q (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst
          (((volume.prod μ) (fiber K p))⁻¹ • (volume.prod μ).restrict (fiber K p)) := by
  obtain ⟨hcompact, hconvex, hne⟩ := prefix_section_body hK hconv hp
  obtain ⟨Q, hc, hs, hd, hmap⟩ := exists_scalar_quantile_of_convex_body μ hcompact hconvex hne
  refine ⟨Q, hc, ?_, hd, hmap⟩
  intro s hmem
  exact (mem_projection_interior_fiber_iff hconv hp (Q s)).mp (hs s hmem)

end Problem358.AffineSlice

end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal

namespace Problem358.ConvexTriangularSampler

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]

/-- Prefixes whose remaining section meets the interior of the body. -/
def valid (K : Set (U × (ℝ × V))) : Set U := Prod.fst '' interior K

/-- The remaining compact body after fixing a valid prefix. -/
def sectionBody (K : Set (U × (ℝ × V))) (x : U) : Set (ℝ × V) :=
  AffineSlice.fiber K x

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma isOpen_valid (K : Set (U × (ℝ × V))) : IsOpen (valid K) :=
  isOpenMap_fst _ isOpen_interior

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma isCompact_sectionBody {K : Set (U × (ℝ × V))} (hK : IsCompact K) (x : U) :
    IsCompact (sectionBody K x) := AffineSlice.isCompact_fiber hK x

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma convex_sectionBody {K : Set (U × (ℝ × V))} (hK : Convex ℝ K) (x : U) :
    Convex ℝ (sectionBody K x) := by
  exact hK.affine_preimage ((AffineMap.const ℝ (ℝ × V) x).prod (AffineMap.id ℝ (ℝ × V)))

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma sectionBody_interior_nonempty {K : Set (U × (ℝ × V))} (x : valid K) :
    (interior (sectionBody K x)).Nonempty := by
  obtain ⟨⟨y, z⟩, hyz, hy⟩ := x.property
  have hyx : y = (x : U) := hy
  refine ⟨z, preimage_interior_subset_interior_preimage
    (continuous_const.prodMk continuous_id) ?_⟩
  change ((x : U), z) ∈ interior K
  simpa only [hyx] using hyz

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma interior_sectionBody {K : Set (U × (ℝ × V))} (hK : Convex ℝ K)
    (x : valid K) :
    interior (sectionBody K x) = (fun z : ℝ × V => ((x : U), z)) ⁻¹' interior K := by
  let f : (ℝ × V) →ᵃ[ℝ] U × (ℝ × V) :=
    (AffineMap.const ℝ (ℝ × V) (x : U)).prod (AffineMap.id ℝ (ℝ × V))
  have hm : (f ⁻¹' interior K).Nonempty := by
    obtain ⟨⟨y, z⟩, hyz, hy⟩ := x.property
    have hyx : y = (x : U) := hy
    refine ⟨z, ?_⟩
    change ((x : U), z) ∈ interior K
    simpa only [hyx] using hyz
  exact interior_affine_preimage_eq f (continuous_const.prodMk continuous_id) hK hm

variable (μ : Measure V) [IsAddHaarMeasure μ]
  {K : Set (U × (ℝ × V))} (hK : IsCompact K) (hc : Convex ℝ K)

/-- The density is chosen only after its concrete geometric existence has been proved. -/
@[irreducible] def conditionalDensity (x : valid K) : PositiveIntervalDensity :=
  (AffineSlice.exists_positiveIntervalDensity_of_convex_body μ
    (isCompact_sectionBody hK x) (convex_sectionBody hc x)
    (sectionBody_interior_nonempty x)).choose

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma conditionalDensity_spec (x : valid K) :
    (conditionalDensity μ hK hc x).density =
      (fun t => μ.real (AffineSlice.fiber (sectionBody K x) t) /
        (volume.prod μ).real (sectionBody K x)) ∧
    Ioo (conditionalDensity μ hK hc x).lower (conditionalDensity μ hK hc x).upper =
      Prod.fst '' interior (sectionBody K x) := by
  unfold conditionalDensity
  exact (AffineSlice.exists_positiveIntervalDensity_of_convex_body μ
    (isCompact_sectionBody hK x) (convex_sectionBody hc x)
    (sectionBody_interior_nonempty x)).choose_spec

/-- Actual conditional inverse-CDF sampling on a valid convex prefix. -/
def conditionalQuantile (x : valid K) : ℝ → ℝ :=
  (conditionalDensity μ hK hc x).quantileReal

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma conditionalQuantile_mem {x : valid K} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃ z : V, ((x : U), (conditionalQuantile μ hK hc x s, z)) ∈ interior K := by
  have hm := (conditionalDensity μ hK hc x).quantileReal_mem_interior hs
  rw [(conditionalDensity_spec μ hK hc x).2] at hm
  obtain ⟨⟨t, z⟩, htz, ht⟩ := hm
  have htq : t = conditionalQuantile μ hK hc x s := ht
  rw [interior_sectionBody hc x] at htz
  exact ⟨z, by simpa only [Set.mem_preimage, htq] using htz⟩

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma conditionalQuantile_hasDerivAt {x : valid K} {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (conditionalQuantile μ hK hc x)
      ((volume.prod μ).real (sectionBody K x) /
        μ.real (AffineSlice.fiber (sectionBody K x) (conditionalQuantile μ hK hc x s))) s := by
  have h := (conditionalDensity μ hK hc x).quantileReal_hasDerivAt hs
  rw [(conditionalDensity_spec μ hK hc x).1, inv_div] at h
  exact h

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma map_conditionalQuantile (x : valid K) :
    Measure.map (conditionalQuantile μ hK hc x) (volume.restrict (Ioo (0 : ℝ) 1)) =
      Measure.map Prod.fst (((volume.prod μ) (sectionBody K x))⁻¹ •
        (volume.prod μ).restrict (sectionBody K x)) := by
  rw [conditionalQuantile, (conditionalDensity μ hK hc x).map_quantileReal_uniform]
  exact AffineSlice.densityMeasure_eq_scalar_marginal μ (isCompact_sectionBody hK x)
    (convex_sectionBody hc x) (sectionBody_interior_nonempty x)
    (conditionalDensity μ hK hc x) (conditionalDensity_spec μ hK hc x).1
    (conditionalDensity_spec μ hK hc x).2

/-- The concrete section-density ratio is jointly measurable even at invalid prefixes. -/
def sectionDensity (K : Set (U × (ℝ × V))) (μ : Measure V) (x : U) (t : ℝ) : ℝ :=
  μ.real (AffineSlice.fiber (sectionBody K x) t) /
    (volume.prod μ).real (sectionBody K x)

omit [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [BorelSpace U] [BorelSpace V] in
lemma measurable_sectionDensity (hKm : MeasurableSet K) :
    Measurable (fun z : U × ℝ => sectionDensity K μ z.1 z.2) := by
  let K' : Set ((U × ℝ) × V) :=
    (fun z : (U × ℝ) × V => (z.1.1, (z.1.2, z.2))) ⁻¹' K
  have hK' : MeasurableSet K' := hKm.preimage (by fun_prop)
  have hn : Measurable (fun z : U × ℝ => μ (Prod.mk z ⁻¹' K')) :=
    measurable_measure_prodMk_left hK'
  have hd : Measurable (fun x : U => (volume.prod μ) (Prod.mk x ⁻¹' K)) :=
    measurable_measure_prodMk_left hKm
  exact hn.ennreal_toReal.div (hd.ennreal_toReal.comp measurable_fst)

omit [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] in
lemma conditionalDensity_density (x : valid K) :
    (conditionalDensity μ hK hc x).density = sectionDensity K μ x :=
  (conditionalDensity_spec μ hK hc x).1

/-- The open set of valid prefixes extended by one scalar coordinate. -/
def scalarDomain (K : Set (U × (ℝ × V))) : Set (U × ℝ) :=
  Prod.map id Prod.fst '' interior K

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma isOpen_scalarDomain (K : Set (U × (ℝ × V))) : IsOpen (scalarDomain K) :=
  (IsOpenMap.id.prodMap isOpenMap_fst) _ isOpen_interior

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma mem_scalarDomain {x : U} {t : ℝ} :
    (x,t) ∈ scalarDomain K ↔ ∃ z : V, (x,(t,z)) ∈ interior K := by
  constructor
  · rintro ⟨⟨y,u,z⟩, hy, heq⟩
    have heq' : (y,u) = (x,t) := heq
    obtain ⟨hyx,hut⟩ := Prod.mk.inj heq'
    exact ⟨z, by simpa only [hyx,hut] using hy⟩
  · rintro ⟨z,hz⟩
    exact ⟨(x,t,z),hz,rfl⟩

omit [NormedSpace ℝ U] [NormedSpace ℝ V]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma projection_scalarDomain : Prod.fst '' scalarDomain K = valid K := by
  ext x
  constructor
  · rintro ⟨⟨y,t⟩, hyt, hy⟩
    have hyx : y = x := hy
    obtain ⟨z,hz⟩ := mem_scalarDomain.mp hyt
    exact ⟨(y,t,z),hz,hyx⟩
  · rintro ⟨⟨y,t,z⟩, hy, hyx⟩
    exact ⟨(y,t), mem_scalarDomain.mpr ⟨z,hy⟩,hyx⟩

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V] in
lemma fiber_scalarDomain (hc : Convex ℝ K) (x : valid K) :
    SectionMeasure.fiber (scalarDomain K) x = Prod.fst '' interior (sectionBody K x) := by
  ext t
  change ((x : U),t) ∈ scalarDomain K ↔ _
  rw [mem_scalarDomain, interior_sectionBody hc x]
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨(t,z),hz,rfl⟩
  · rintro ⟨⟨u,z⟩, huz, hu⟩
    have hut : u = t := hu
    exact ⟨z, by simpa only [Set.mem_preimage, hut] using huz⟩

omit [FiniteDimensional ℝ U] in
/-- A compact convex body has a globally jointly measurable conditional scalar sampler.
Its law, derivative and interior support are all derived from the body itself. -/
theorem exists_measurable_conditional_quantile (hK : IsCompact K) (hc : Convex ℝ K) :
    ∃ Q : U × ℝ → ℝ, Measurable Q ∧
      (∀ x ∈ valid K, Measure.map (fun s => Q (x,s))
        (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst (((volume.prod μ) (sectionBody K x))⁻¹ •
          (volume.prod μ).restrict (sectionBody K x))) ∧
      (∀ x ∈ valid K, ∀ s ∈ Ioo (0 : ℝ) 1,
        ∃ z : V, (x,(Q (x,s),z)) ∈ interior K) ∧
      (∀ x ∈ valid K, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (x,t))
          ((volume.prod μ).real (sectionBody K x) /
            μ.real (AffineSlice.fiber (sectionBody K x) (Q (x,s)))) s) ∧
      (∀ x ∈ valid K, StrictMonoOn (fun s => Q (x,s)) (Icc (0 : ℝ) 1)) := by
  have hex : ∀ a : Prod.fst '' scalarDomain K, ∃ D : PositiveIntervalDensity,
      D.density = (fun t => sectionDensity K μ a.val t) ∧
      Ioo D.lower D.upper = SectionMeasure.fiber (scalarDomain K) a.val := by
    intro a
    have ha : a.val ∈ valid K :=
      (Set.ext_iff.mp (projection_scalarDomain (K := K)) a.val).mp a.property
    let x : valid K := ⟨a.val,ha⟩
    refine ⟨conditionalDensity μ hK hc x, conditionalDensity_density μ hK hc x, ?_⟩
    rw [(conditionalDensity_spec μ hK hc x).2, fiber_scalarDomain hc x]
  obtain ⟨Q,hQ,hlaw,hmem,hderiv,hstrict,_⟩ :=
    PositiveIntervalDensity.exists_quantiles_of_open_fiber_densities
      (isOpen_scalarDomain K) (fun z => sectionDensity K μ z.1 z.2)
      (measurable_sectionDensity μ hK.measurableSet) hex
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · intro x hx
    let a : Prod.fst '' scalarDomain K := ⟨x, by rwa [projection_scalarDomain]⟩
    let b : valid K := ⟨x,hx⟩
    rw [hlaw a]
    have hd := AffineSlice.densityMeasure_eq_scalar_marginal μ
      (isCompact_sectionBody hK x) (convex_sectionBody hc x)
      (sectionBody_interior_nonempty b) (conditionalDensity μ hK hc b)
      (conditionalDensity_spec μ hK hc b).1 (conditionalDensity_spec μ hK hc b).2
    rw [PositiveIntervalDensity.densityMeasure,
      (conditionalDensity_spec μ hK hc b).2,
      conditionalDensity_density μ hK hc b, ← fiber_scalarDomain hc b] at hd
    exact hd
  · intro x hx s hs
    let a : Prod.fst '' scalarDomain K := ⟨x, by rwa [projection_scalarDomain]⟩
    exact mem_scalarDomain.mp (hmem a s hs)
  · intro x hx s hs
    let a : Prod.fst '' scalarDomain K := ⟨x, by rwa [projection_scalarDomain]⟩
    simpa only [sectionDensity, inv_div] using hderiv a s hs
  · intro x hx
    exact hstrict ⟨x, by rwa [projection_scalarDomain]⟩

end Problem358.ConvexTriangularSampler

end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal Topology

namespace Problem358.AffineSlice

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Prefixes admitting an interior completion in the body. -/
def interiorPrefix (K : Set (U × V)) : Set U :=
  {p | ∃ v : V, (p, v) ∈ interior K}

variable [MeasurableSpace U] [BorelSpace U]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A compact convex body supplies the jointly measurable conditional quantiles
on every valid prefix, with actual fiber laws and no endpoint measurability premise. -/
theorem exists_measurable_scalar_quantile_family_of_prefix
    (μ : Measure V) [IsAddHaarMeasure μ]
    {K : Set (U × (ℝ × V))} (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∃ Q : interiorPrefix K × ℝ → ℝ, Measurable Q ∧
      (∀ (p : interiorPrefix K) s, s ∈ Ioo (0 : ℝ) 1 →
        ∃ v : V, ((p : U), (Q (p, s), v)) ∈ interior K) ∧
      (∀ (p : interiorPrefix K) s, s ∈ Ioo (0 : ℝ) 1 → HasDerivAt (fun t => Q (p, t))
        ((volume.prod μ).real (fiber K (p : U)) /
          μ.real (fiber (fiber K (p : U)) (Q (p, s)))) s) ∧
      ∀ (p : interiorPrefix K), Measure.map (fun t => Q (p, t)) (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst
          (((volume.prod μ) (fiber K (p : U)))⁻¹ •
            (volume.prod μ).restrict (fiber K (p : U))) := by
  have hm : MeasurableSet
      {z : interiorPrefix K × (ℝ × V) | z.2 ∈ fiber K (z.1 : U)} := by
    exact hK.measurableSet.preimage
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hc (p : interiorPrefix K) := prefix_section_body hK hconv p.property
  obtain ⟨Q, hQ, hs, hd, hlaw⟩ :=
    exists_measurable_scalar_quantile_family_of_convex_body μ
      (fun p : interiorPrefix K => fiber K (p : U)) hm
      (fun p => (hc p).1) (fun p => (hc p).2.1) (fun p => (hc p).2.2)
  refine ⟨Q, hQ, ?_, hd, hlaw⟩
  intro p s hmem
  exact (mem_projection_interior_fiber_iff hconv p.property (Q (p, s))).mp
    (hs p s hmem)

end Problem358.AffineSlice

end

end OAI
