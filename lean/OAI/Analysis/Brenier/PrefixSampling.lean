import OAI.Analysis.Brenier.ConvexQuantiles
import OAI.Analysis.Brenier.NormalizedSections
import OAI.Analysis.Brenier.PrefixSections
import OAI.Analysis.Brenier.TriangularDomination

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace Problem358.FinitePrefix

/-- The same body in prefix/next-coordinate/remainder coordinates. -/
def stepBody {d n : ℕ} (K : Set (Coordinates d)) (h : n < d) :
    Set (Coordinates n × (ℝ × Coordinates (d-(n+1)))) :=
  tripleSplit h ⁻¹' K

lemma interior_stepBody {d n : ℕ} (K : Set (Coordinates d)) (h : n < d) :
    interior (stepBody K h) = tripleSplit h ⁻¹' interior K :=
  ((tripleSplit h).toHomeomorph.preimage_interior K).symm

@[simp] lemma headBlock_tripleSplit_prefix {d n : ℕ} (h : n < d)
    (a : Coordinates n) (t : ℝ) (b : Coordinates (d-(n+1))) :
    headBlock h.le (tripleSplit h (a,t,b)) = a := by
  ext i
  exact tripleSplit_left h a t b i

lemma valid_stepBody {d n : ℕ} (K : Set (Coordinates d)) (h : n < d) :
    ConvexTriangularSampler.valid (stepBody K h) = prefixDomain K h.le := by
  ext a
  constructor
  · rintro ⟨⟨a',t,b⟩,hp,ha⟩
    have haa : a' = a := ha
    subst a'
    rw [interior_stepBody] at hp
    exact ⟨tripleSplit h (a,t,b),hp,headBlock_tripleSplit_prefix h a t b⟩
  · rintro ⟨x,hx,ha⟩
    obtain ⟨⟨a',t,b⟩,rfl⟩ := (tripleSplit h).surjective x
    have haa : a' = a := (headBlock_tripleSplit_prefix h a' t b).symm.trans ha
    subst a'
    refine ⟨(a,t,b),?_,rfl⟩
    rw [interior_stepBody]
    exact hx

/-- Each actual finite prefix admits a globally measurable next-coordinate quantile.
The conditional law is the precise normalized remaining-body scalar marginal. -/
theorem exists_prefix_quantile {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d) :
    ∃ Q : Coordinates n × ℝ → ℝ, Measurable Q ∧
      (∀ a ∈ prefixDomain K h.le, Measure.map (fun s => Q (a,s))
        (volume.restrict (Ioo (0 : ℝ) 1)) =
        Measure.map Prod.fst
          (((volume.prod volume) (ConvexTriangularSampler.sectionBody (stepBody K h) a))⁻¹ •
            (volume.prod volume).restrict
              (ConvexTriangularSampler.sectionBody (stepBody K h) a))) ∧
      (∀ a ∈ prefixDomain K h.le, ∀ s ∈ Ioo (0 : ℝ) 1,
        Fin.snoc a (Q (a,s)) ∈ prefixDomain K (Nat.succ_le_of_lt h)) ∧
      (∀ a ∈ prefixDomain K h.le, ∀ s ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (fun t => Q (a,t))
          ((ConvexTriangularSampler.sectionDensity (stepBody K h) volume a (Q (a,s)))⁻¹) s) ∧
      (∀ a ∈ prefixDomain K h.le, ∀ s ∈ Ioo (0 : ℝ) 1,
        0 < (ConvexTriangularSampler.sectionDensity (stepBody K h) volume a (Q (a,s)))⁻¹) := by
  have hk : IsCompact (stepBody K h) :=
    (tripleSplit h).toHomeomorph.isCompact_preimage.mpr hK
  have hcv : Convex ℝ (stepBody K h) := hc.linear_preimage (tripleSplit h).toLinearMap
  obtain ⟨Q,hQ,hlaw,hmem,hderiv,hstrict⟩ :=
    ConvexTriangularSampler.exists_measurable_conditional_quantile
      (volume : Measure (Coordinates (d-(n+1)))) hk hcv
  refine ⟨Q,hQ,?_,?_,?_,?_⟩
  · simpa only [valid_stepBody] using hlaw
  · intro a ha s hs
    rw [← valid_stepBody K h] at ha
    obtain ⟨b,hb⟩ := hmem a ha s hs
    rw [interior_stepBody] at hb
    exact snoc_mem_prefix_image h hb
  · intro a ha s hs
    rw [← valid_stepBody K h] at ha
    simpa only [ConvexTriangularSampler.sectionDensity, inv_div] using hderiv a ha s hs
  · intro a ha s hs
    rw [← valid_stepBody K h] at ha
    obtain ⟨b,hb⟩ := hmem a ha s hs
    have hsec : (Q (a,s),b) ∈ interior
        (ConvexTriangularSampler.sectionBody (stepBody K h) a) :=
      preimage_interior_subset_interior_preimage
        (continuous_const.prodMk continuous_id) hb
    have hparent : 0 < (volume.prod volume).real
        (ConvexTriangularSampler.sectionBody (stepBody K h) a) :=
      ENNReal.toReal_pos (measure_pos_of_nonempty_interior _ ⟨(Q (a,s),b),hsec⟩).ne'
        (ConvexTriangularSampler.isCompact_sectionBody hk a).measure_ne_top
    have hchild : 0 < volume.real
        (AffineSlice.fiber (ConvexTriangularSampler.sectionBody (stepBody K h) a) (Q (a,s))) :=
      AffineSlice.fiberMeasureReal_pos volume
        (ConvexTriangularSampler.isCompact_sectionBody hk a) ⟨b,hsec⟩
    simpa only [ConvexTriangularSampler.sectionDensity, inv_div] using div_pos hparent hchild

/-- The concrete conditional family, extended by zero beyond the ambient dimension. -/
def bodyQuantileFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) : TriangularRecursion.ConditionalFamily :=
  fun n a t => if h : n < d then (exists_prefix_quantile hK hc h).choose (a,t) else 0

lemma bodyQuantileFamily_of_lt {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (t : ℝ) :
    bodyQuantileFamily hK hc n a t = (exists_prefix_quantile hK hc h).choose (a,t) := by
  simp only [bodyQuantileFamily, dite_eq_left h]

lemma measurable_bodyQuantileFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (n : ℕ) :
    Measurable (fun p : Coordinates n × ℝ => bodyQuantileFamily hK hc n p.1 p.2) := by
  by_cases h : n < d
  · simpa only [bodyQuantileFamily, dite_eq_left h] using
      (exists_prefix_quantile hK hc h).choose_spec.1
  · simp only [bodyQuantileFamily, dite_eq_right h]
    exact measurable_const

lemma bodyQuantileFamily_law {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le) :
    Measure.map (bodyQuantileFamily hK hc n a)
      (volume.restrict (Ioo (0 : ℝ) 1)) =
      Measure.map Prod.fst
        (((volume.prod volume) (ConvexTriangularSampler.sectionBody (stepBody K h) a))⁻¹ •
          (volume.prod volume).restrict
            (ConvexTriangularSampler.sectionBody (stepBody K h) a)) := by
  have heq : bodyQuantileFamily hK hc n a =
      fun s => (exists_prefix_quantile hK hc h).choose (a,s) :=
    funext (bodyQuantileFamily_of_lt hK hc h a)
  rw [heq]
  exact (exists_prefix_quantile hK hc h).choose_spec.2.1 a ha

lemma bodyQuantileFamily_mem {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    Fin.snoc a (bodyQuantileFamily hK hc n a s) ∈
      prefixDomain K (Nat.succ_le_of_lt h) := by
  simpa only [bodyQuantileFamily, dite_eq_left h] using
    (exists_prefix_quantile hK hc h).choose_spec.2.2.1 a ha s hs

/-- Jointly measurable actual inverse section-density diagonal derivative. -/
def bodyDerivativeFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) : TriangularRecursion.ConditionalFamily :=
  fun n a t => if h : n < d then
    (ConvexTriangularSampler.sectionDensity (stepBody K h) volume a
      (bodyQuantileFamily hK hc n a t))⁻¹ else 0

lemma measurable_bodyDerivativeFamily {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (n : ℕ) :
    Measurable (fun p : Coordinates n × ℝ => bodyDerivativeFamily hK hc n p.1 p.2) := by
  by_cases h : n < d
  · simp only [bodyDerivativeFamily, dite_eq_left h]
    have hk : MeasurableSet (stepBody K h) :=
      hK.measurableSet.preimage (tripleSplit h).continuous.measurable
    exact ((ConvexTriangularSampler.measurable_sectionDensity volume hk).comp
      (measurable_fst.prodMk (measurable_bodyQuantileFamily hK hc n))).inv
  · simp only [bodyDerivativeFamily, dite_eq_right h]
    exact measurable_const

lemma bodyQuantileFamily_hasDerivAt {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (bodyQuantileFamily hK hc n a) (bodyDerivativeFamily hK hc n a s) s := by
  have heq : bodyQuantileFamily hK hc n a =
      fun t => (exists_prefix_quantile hK hc h).choose (a,t) :=
    funext (bodyQuantileFamily_of_lt hK hc h a)
  rw [heq]
  simpa only [bodyDerivativeFamily, bodyQuantileFamily, dite_eq_left h] using
    (exists_prefix_quantile hK hc h).choose_spec.2.2.2.1 a ha s hs

lemma bodyDerivativeFamily_pos {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (ha : a ∈ prefixDomain K h.le)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    0 < bodyDerivativeFamily hK hc n a s := by
  simpa only [bodyDerivativeFamily, bodyQuantileFamily, dite_eq_left h] using
    (exists_prefix_quantile hK hc h).choose_spec.2.2.2.2 a ha s hs

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory

namespace Problem358.FinitePrefix

/-- The actual recursively sampled prefix stays in the projection of the body's interior. -/
theorem bodySample_mem {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∀ n, ∀ h : n ≤ d, ∀ s : Coordinates n,
      TriangularDensity.InUnitCube s →
        TriangularRecursion.sample (bodyQuantileFamily hK hc) n s ∈ prefixDomain K h := by
  intro n
  induction n with
  | zero =>
    intro h s hs
    exact prefixDomain_zero hne _
  | succ n ih =>
    intro h s hs
    exact bodyQuantileFamily_mem hK hc (by omega)
      (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))
      (ih (by omega) _ hs.init) _ hs.last

/-- The full sampler takes every open unit-cube point into the actual body interior. -/
theorem bodySample_mem_interior {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (s : Coordinates d) (hs : TriangularDensity.InUnitCube s) :
    TriangularRecursion.sample (bodyQuantileFamily hK hc) d s ∈ interior K := by
  simpa only [prefixDomain_full] using bodySample_mem hK hc hne d (le_refl d) s hs

/-- Derivative regularity along each scalar input of the concrete sampler. -/
theorem bodySample_fiber_hasDerivAt {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (h : n < d) (s : Coordinates n) (hs : TriangularDensity.InUnitCube s)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (bodyQuantileFamily hK hc n (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s))
      (bodyDerivativeFamily hK hc n (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s) t) t :=
  bodyQuantileFamily_hasDerivAt hK hc h _ (bodySample_mem hK hc hne n h.le s hs) t ht

lemma bodySample_fiber_derivative_pos {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (h : n < d) (s : Coordinates n) (hs : TriangularDensity.InUnitCube s)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < bodyDerivativeFamily hK hc n
      (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s) t :=
  bodyDerivativeFamily_pos hK hc h _ (bodySample_mem hK hc hne n h.le s hs) t ht

/-- The concrete derivative is exactly the ratio of consecutive prefix volumes. -/
lemma bodyDerivativeFamily_eq_ratio {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (h : n < d)
    (a : Coordinates n) (t : ℝ) :
    bodyDerivativeFamily hK hc n a t =
      volume.real (prefixSection K h.le a) /
        volume.real (prefixSection K (Nat.succ_le_of_lt h)
          (Fin.snoc a (bodyQuantileFamily hK hc n a t))) := by
  simp only [bodyDerivativeFamily, dite_eq_left h, ConvexTriangularSampler.sectionDensity,
    ConvexTriangularSampler.sectionBody, stepBody, inv_div,
    tripleSplit_parentSection_volumeReal, tripleSplit_childSection_volumeReal]

/-- The diagonal derivatives telescope through the actual geometric section volumes. -/
theorem bodySample_diagonalProduct_eq_ratio {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    ∀ n, ∀ h : n ≤ d, ∀ s : Coordinates n, TriangularDensity.InUnitCube s →
      TriangularDensity.diagonalProduct (bodyQuantileFamily hK hc)
        (bodyDerivativeFamily hK hc) n s =
          (volume K).toReal /
            volume.real (prefixSection K h
              (TriangularRecursion.sample (bodyQuantileFamily hK hc) n s)) := by
  have hvol : 0 < (volume K).toReal :=
    ENNReal.toReal_pos (MeasureTheory.Measure.measure_pos_of_nonempty_interior volume hne).ne'
      hK.measure_ne_top
  intro n
  induction n with
  | zero =>
    intro h s hs
    simp only [TriangularDensity.diagonalProduct, TriangularRecursion.sample,
      MeasureTheory.Measure.real, volume_prefixSection_zero]
    exact (div_self hvol.ne').symm
  | succ n ih =>
    intro h s hs
    have hn : n < d := by omega
    have hp := prefixSection_volumeReal_pos hK
      (bodySample_mem hK hc hne n hn.le (Fin.init s) hs.init)
    rw [TriangularDensity.diagonalProduct, ih hn.le _ hs.init,
      bodyDerivativeFamily_eq_ratio hK hc hn]
    change _ = (volume K).toReal /
      volume.real (prefixSection K h
        (Fin.snoc (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))
          (bodyQuantileFamily hK hc n
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))
            (s (Fin.last n)))))
    change 0 < volume.real (prefixSection K hn.le
      (TriangularRecursion.sample (bodyQuantileFamily hK hc) n (Fin.init s))) at hp
    field_simp [hp.ne']

/-- The full Jacobian product is the body's volume, with no seed dependence. -/
theorem bodySample_diagonalProduct_eq_volume {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty)
    (s : Coordinates d) (hs : TriangularDensity.InUnitCube s) :
    TriangularDensity.diagonalProduct (bodyQuantileFamily hK hc)
      (bodyDerivativeFamily hK hc) d s = (volume K).toReal := by
  rw [bodySample_diagonalProduct_eq_ratio hK hc hne d (le_refl d) s hs]
  change _ / (volume (prefixSection K (le_refl d)
    (TriangularRecursion.sample (bodyQuantileFamily hK hc) d s))).toReal = _
  rw [volumeReal_prefixSection_full (bodySample_mem hK hc hne d (le_refl d) s hs), div_one]

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Problem358.FinitePrefix

/-- The actual first-coordinate marginal of normalized volume on the body. -/
def prefixLaw {d n : ℕ} (K : Set (Coordinates d)) (h : n ≤ d) :
    Measure (Coordinates n) :=
  Measure.map (headBlock h) ((volume K)⁻¹ • volume.restrict K)

theorem prefixLaw_density {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n ≤ d) :
    prefixLaw K h = (volume K)⁻¹ •
      volume.withDensity (fun a => volume (prefixSection K h a)) :=
  map_headBlock_normalized_restrict h hK

theorem isProbabilityMeasure_normalizedVolume {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    IsProbabilityMeasure ((volume K)⁻¹ • volume.restrict K) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (measure_pos_of_nonempty_interior volume hi).ne'
    hK.measure_ne_top

theorem isProbabilityMeasure_prefixLaw {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) (h : n ≤ d) :
    IsProbabilityMeasure (prefixLaw K h) := by
  let := isProbabilityMeasure_normalizedVolume hK hi
  exact (Measure.isProbabilityMeasure_map_iff
    (continuous_headBlock h).measurable.aemeasurable).mpr inferInstance

@[simp] theorem prefixLaw_full {d : ℕ} (K : Set (Coordinates d)) :
    prefixLaw K (le_refl d) = (volume K)⁻¹ • volume.restrict K := by
  change Measure.map id _ = _
  exact Measure.map_id

theorem measurableSet_stepBody {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : MeasurableSet (stepBody K h) :=
  hK.preimage (tripleSplit h).continuous.measurable

theorem volume_stepBody {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : volume (stepBody K h) = volume K := by
  exact (measurePreserving_tripleSplit h).measure_preimage hK.nullMeasurableSet

theorem map_tripleSplit_normalized {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) :
    Measure.map (tripleSplit h)
      ((volume K)⁻¹ • volume.restrict (stepBody K h)) =
      (volume K)⁻¹ • volume.restrict K := by
  rw [Measure.map_smul _ (tripleSplit h).continuous.measurable.aemeasurable]
  exact congrArg (fun μ => (volume K)⁻¹ • μ)
    ((measurePreserving_tripleSplit h).restrict_preimage hK).map_eq

theorem prefixLaw_eq_step_fst {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) :
    prefixLaw K h.le = Measure.map Prod.fst
      ((volume K)⁻¹ • volume.restrict (stepBody K h)) := by
  unfold prefixLaw
  rw [← map_tripleSplit_normalized hK h,
    Measure.map_map (continuous_headBlock h.le).measurable (tripleSplit h).continuous.measurable]
  congr 1
  funext p
  ext i
  exact tripleSplit_left h p.1 p.2.1 p.2.2 i

theorem prefixLaw_succ_eq_step_map {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) :
    prefixLaw K (Nat.succ_le_of_lt h) =
      Measure.map (fun p : Coordinates n × (ℝ × Coordinates (d-(n+1))) =>
        Fin.snoc p.1 p.2.1)
        ((volume K)⁻¹ • volume.restrict (stepBody K h)) := by
  unfold prefixLaw
  rw [← map_tripleSplit_normalized hK h,
    Measure.map_map (continuous_headBlock (Nat.succ_le_of_lt h)).measurable
      (tripleSplit h).continuous.measurable]
  congr 1
  funext p
  exact headBlock_tripleSplit h p.1 p.2.1 p.2.2

/-- The next-coordinate conditional law, completed by a point on null prefixes. -/
def prefixKernel {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : Kernel (Coordinates n) ℝ :=
  (NormalizedSections.completedSectionKernel (volume.prod volume)
    (NormalizedSections.measurable_setDensity (measurableSet_stepBody hK h))
    (0, 0)).map Prod.fst

theorem isMarkovKernel_prefixKernel {d n : ℕ} {K : Set (Coordinates d)}
    (hK : MeasurableSet K) (h : n < d) : IsMarkovKernel (prefixKernel hK h) := by
  let := NormalizedSections.isMarkovKernel_completedSectionKernel
    (volume.prod volume)
    (NormalizedSections.measurable_setDensity (measurableSet_stepBody hK h)) (0, 0)
  exact Kernel.IsMarkovKernel.map _ measurable_fst

theorem prefixKernel_apply_valid {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (h : n < d)
    {a : Coordinates n} (ha : a ∈ prefixDomain K h.le) :
    prefixKernel hK.measurableSet h a = Measure.map Prod.fst
      (((volume.prod volume) (ConvexTriangularSampler.sectionBody (stepBody K h) a))⁻¹ •
        (volume.prod volume).restrict
          (ConvexTriangularSampler.sectionBody (stepBody K h) a)) := by
  classical
  have hm := measurableSet_stepBody hK.measurableSet h
  have hcompact : IsCompact (stepBody K h) :=
    (tripleSplit h).toHomeomorph.isCompact_preimage.mpr hK
  have hvalid : a ∈ ConvexTriangularSampler.valid (stepBody K h) := by
    rwa [valid_stepBody]
  have hgood : a ∈ NormalizedSections.goodSections (volume.prod volume)
      (NormalizedSections.setDensity (stepBody K h)) := by
    change _ ≠ 0 ∧ _ ≠ ∞
    rw [NormalizedSections.sectionMass_setDensity _ hm]
    exact ⟨(measure_pos_of_nonempty_interior _
      (ConvexTriangularSampler.sectionBody_interior_nonempty ⟨a, hvalid⟩)).ne',
      (ConvexTriangularSampler.isCompact_sectionBody hcompact a).measure_ne_top⟩
  rw [prefixKernel, Kernel.map_apply _ measurable_fst,
    NormalizedSections.completedSectionKernel, Kernel.piecewise_apply, ite_eq_left hgood,
    NormalizedSections.sectionKernel_apply _
      (NormalizedSections.measurable_setDensity hm),
    NormalizedSections.sectionLaw_setDensity _ hm]
  rfl

theorem prefixLaw_compProd_prefixKernel {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) (h : n < d) :
    (prefixLaw K h.le).compProd (prefixKernel hK.measurableSet h) =
      Measure.map (Prod.map id Prod.fst)
        ((volume K)⁻¹ • volume.restrict (stepBody K h)) := by
  let := isProbabilityMeasure_prefixLaw hK hi h.le
  have hm := measurableSet_stepBody hK.measurableSet h
  let := NormalizedSections.isMarkovKernel_completedSectionKernel
    (volume.prod volume) (NormalizedSections.measurable_setDensity hm) (0, 0)
  have hvol : (volume.prod (volume.prod volume)) (stepBody K h) = volume K :=
    volume_stepBody hK.measurableSet h
  have hρ : prefixLaw K h.le = (volume K)⁻¹ •
      volume.withDensity (NormalizedSections.sectionMass (volume.prod volume)
        (NormalizedSections.setDensity (stepBody K h))) := by
    rw [prefixLaw_eq_step_fst hK.measurableSet h,
      Measure.map_smul _ measurable_fst.aemeasurable]
    congr 1
    rw [volume_eq_prod, volume_eq_prod,
      SectionMarginal.map_fst_restrict volume (volume.prod volume) _ hm]
    congr 1
    funext a
    exact (NormalizedSections.sectionMass_setDensity _ hm a).symm
  rw [prefixKernel, Measure.compProd_map measurable_fst, hρ]
  congr 1
  have hd := NormalizedSections.compProd_uniformSetSections volume
    (volume.prod volume) hm (0, 0) (hvol ▸ hK.measure_ne_top)
  simpa only [hvol, volume_eq_prod] using hd

/-- Genuine one-step disintegration of the geometric prefix laws. -/
theorem prefixLaw_succ {d n : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) (h : n < d) :
    prefixLaw K (Nat.succ_le_of_lt h) =
      Measure.map (fun p : Coordinates n × ℝ => Fin.snoc p.1 p.2)
        ((prefixLaw K h.le).compProd (prefixKernel hK.measurableSet h)) := by
  rw [prefixLaw_compProd_prefixKernel hK hi h,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact prefixLaw_succ_eq_step_map hK.measurableSet h

end Problem358.FinitePrefix

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Problem358.FinitePrefix

open TriangularRecursion

/-- The midpoint of the two actual convex-body samplers has the sharp geometric
volume domination. All scalar differentiability, prefix support, measurability,
and terminal Jacobian identities are consequences of the two bodies. -/
theorem bodyMidpoint_smul_map_le_volume
    {d : ℕ} {K L : Set (Coordinates d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hiK : (interior K).Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hiL : (interior L).Nonempty) :
    ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
      Measure.map (midpoint (bodyQuantileFamily hK hcK) (bodyQuantileFamily hL hcL) d)
        (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (volume : Measure (Coordinates d)) := by
  simpa only [volume_pi] using
    midpoint_smul_map_le_of_diagonalProducts
      (bodyQuantileFamily hK hcK) (bodyQuantileFamily hL hcL)
      (bodyDerivativeFamily hK hcK) (bodyDerivativeFamily hL hcL)
      d (volume K).toReal (volume L).toReal
      (fun n _ => measurable_bodyQuantileFamily hK hcK n)
      (fun n _ => measurable_bodyQuantileFamily hL hcL n)
      (fun n _ => measurable_bodyDerivativeFamily hK hcK n)
      (fun n _ => measurable_bodyDerivativeFamily hL hcL n)
      (fun n _ => measurable_sample _ (measurable_bodyQuantileFamily hK hcK) n)
      (fun n _ => measurable_sample _ (measurable_bodyQuantileFamily hL hcL) n)
      (fun _ hn s hs t ht => bodySample_fiber_hasDerivAt hK hcK hiK hn s hs t ht)
      (fun _ hn s hs t ht => bodySample_fiber_hasDerivAt hL hcL hiL hn s hs t ht)
      (fun _ hn s hs t ht => bodySample_fiber_derivative_pos hK hcK hiK hn s hs t ht)
      (fun _ hn s hs t ht => bodySample_fiber_derivative_pos hL hcL hiL hn s hs t ht)
      (bodySample_diagonalProduct_eq_volume hK hcK hiK)
      (bodySample_diagonalProduct_eq_volume hL hcL hiL)

/-- Positive volume is sufficient for the geometric body hypotheses; no
chosen interior point is required in this form of the domination theorem. -/
theorem bodyMidpoint_smul_map_le_volume_of_pos
    {d : ℕ} {K L : Set (Coordinates d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hvK : 0 < volume K)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hvL : 0 < volume L) :
    ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
      Measure.map (midpoint (bodyQuantileFamily hK hcK) (bodyQuantileFamily hL hcL) d)
        (Measure.pi fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)) ≤
      (volume : Measure (Coordinates d)) := by
  have hinterior {S : Set (Coordinates d)} (hS : IsCompact S) (hcS : Convex ℝ S)
      (hvS : 0 < volume S) : (interior S).Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    have hzero := hcS.addHaar_frontier volume
    rw [frontier, hS.isClosed.closure_eq, hempty, Set.sdiff_empty] at hzero
    exact hvS.ne' hzero
  exact bodyMidpoint_smul_map_le_volume hK hcK (hinterior hK hcK hvK)
    hL hcL (hinterior hL hcL hvL)

end Problem358.FinitePrefix

end

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace Problem358.FinitePrefix

/-- Every stage of the actual convex-body quantile construction has the
corresponding geometric prefix marginal. -/
theorem map_bodyQuantile_sample_prefix {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∀ n (h : n ≤ d),
      Measure.map (TriangularRecursion.sample (bodyQuantileFamily hK hc) n)
        (Measure.pi (fun _ : Fin n => volume.restrict (Ioo (0 : ℝ) 1))) =
          prefixLaw K h := by
  intro n
  induction n with
  | zero =>
      intro h
      change Measure.map id _ = _
      rw [Measure.map_id, prefixLaw_density hK.measurableSet h,
        normalized_initial_prefix_law
          (measure_pos_of_nonempty_interior volume hi).ne' hK.measure_ne_top]
      rw [Measure.pi_of_empty, volume_pi_eq_dirac]
  | succ n ih =>
      intro h
      have hn : n < d := h
      have hbase := ih hn.le
      let := isProbabilityMeasure_prefixLaw hK hi hn.le
      let := isMarkovKernel_prefixKernel hK.measurableSet hn
      have hF := TriangularRecursion.measurable_sample (bodyQuantileFamily hK hc)
        (measurable_bodyQuantileFamily hK hc) n
      have hG : Measurable (fun p : Coordinates n × ℝ =>
          bodyQuantileFamily hK hc n
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n p.1) p.2) := by
        exact (measurable_bodyQuantileFamily hK hc n).comp
          ((hF.comp measurable_fst).prodMk measurable_snd)
      have hgood := ae_sample_mem_prefixDomain hc hn.le hF.aemeasurable hbase
      have hfiber : ∀ᵐ a ∂Measure.pi
          (fun _ : Fin n => volume.restrict (Ioo (0 : ℝ) 1)),
          Measure.map (bodyQuantileFamily hK hc n
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n a))
              (volume.restrict (Ioo (0 : ℝ) 1)) =
          prefixKernel hK.measurableSet hn
            (TriangularRecursion.sample (bodyQuantileFamily hK hc) n a) := by
        filter_upwards [hgood] with a ha
        exact (bodyQuantileFamily_law hK hc hn _ ha).trans
          (prefixKernel_apply_valid hK hn ha).symm
      rw [prefixLaw_succ hK hi hn]
      exact TriangularSampling.map_snoc_pi_eq n (volume.restrict (Ioo (0 : ℝ) 1))
        (prefixLaw K hn.le) (prefixKernel hK.measurableSet hn)
        (TriangularRecursion.sample (bodyQuantileFamily hK hc) n)
        (fun p => bodyQuantileFamily hK hc n
          (TriangularRecursion.sample (bodyQuantileFamily hK hc) n p.1) p.2)
        hF hG hbase hfiber

/-- The concrete, globally measurable triangular quantile sampler has exactly
the uniform probability law of the convex body. -/
theorem map_bodyQuantile_sample {d : ℕ} {K : Set (Coordinates d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    Measure.map (TriangularRecursion.sample (bodyQuantileFamily hK hc) d)
      (Measure.pi (fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1))) =
        (volume K)⁻¹ • volume.restrict K := by
  simpa only [prefixLaw_full] using map_bodyQuantile_sample_prefix hK hc hi d le_rfl

end Problem358.FinitePrefix

end

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Problem358

/-- A convex body of positive volume has a nonempty interior. -/
lemma convex_interior_nonempty_of_volume_pos {d : ℕ} {K : Set (E d)}
    (hc : Convex ℝ K) (hvol : 0 < volume K) : (interior K).Nonempty := by
  by_contra h
  have he : interior K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hv := MidpointCoordinates.volume_interior hc
  rw [he, measure_empty] at hv
  exact hvol.ne' hv.symm

/-- All body hypotheses survive the canonical volume-preserving Euclidean coordinate map. -/
lemma coordinate_body_geometry {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hne : (interior K).Nonempty) :
    IsCompact ((WithLp.toLp 2) ⁻¹' K) ∧
      Convex ℝ ((WithLp.toLp 2) ⁻¹' K) ∧
      (interior ((WithLp.toLp 2) ⁻¹' K)).Nonempty := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he : (e : (Fin d → ℝ) → E d) = WithLp.toLp 2 := rfl
  rw [← he]
  refine ⟨e.toHomeomorph.isCompact_preimage.mpr hK, hc.linear_preimage e.toLinearMap, ?_⟩
  change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
  rw [← e.toHomeomorph.preimage_interior]
  exact hne.preimage e.surjective

/-- Every pair of compact convex bodies admits a uniform coupling whose midpoint
law is dominated by volume with the geometric-mean volume factor. -/
theorem exists_convexBody_midpoint_coupling {d : ℕ} {K L : Set (E d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hiK : (interior K).Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hiL : (interior L).Nonempty) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
        Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume := by
  obtain ⟨hK', hcK', hiK'⟩ := coordinate_body_geometry hK hcK hiK
  obtain ⟨hL', hcL', hiL'⟩ := coordinate_body_geometry hL hcL hiL
  let Q := FinitePrefix.bodyQuantileFamily hK' hcK'
  let R := FinitePrefix.bodyQuantileFamily hL' hcL'
  let : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
    simp [Real.volume_Ioo]⟩
  have hdom := FinitePrefix.bodyMidpoint_smul_map_le_volume hK' hcK' hiK' hL' hcL' hiL'
  rw [MidpointCoordinates.volume_preimage_toLp hK.measurableSet,
    MidpointCoordinates.volume_preimage_toLp hL.measurableSet] at hdom
  apply MidpointCoordinates.exists_midpoint_coupling_of_coordinate_samplers
    (ρ := Measure.pi (fun _ : Fin d => volume.restrict (Ioo (0 : ℝ) 1)))
    hK.measurableSet hL.measurableSet
    (TriangularRecursion.sample Q d) (TriangularRecursion.sample R d)
    (TriangularRecursion.measurable_sample Q (FinitePrefix.measurable_bodyQuantileFamily hK' hcK') d)
    (TriangularRecursion.measurable_sample R (FinitePrefix.measurable_bodyQuantileFamily hL' hcL') d)
    (FinitePrefix.map_bodyQuantile_sample hK' hcK' hiK')
    (FinitePrefix.map_bodyQuantile_sample hL' hcL' hiL')
  convert hdom using 1
  congr 2
  funext s i
  simp [TriangularRecursion.midpoint, Q, R, div_eq_mul_inv, mul_comm]

/-- Positive volume suffices, including in dimension zero. -/
theorem exists_convexBody_midpoint_coupling_of_pos {d : ℕ} {K L : Set (E d)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hvK : 0 < volume K)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hvL : 0 < volume L) :
    ∃ π : Measure (E d × E d), IsCoupling (uniformMeasure K) (uniformMeasure L) π ∧
      ENNReal.ofReal (Real.sqrt ((volume K).toReal * (volume L).toReal)) •
        Measure.map (fun p : E d × E d => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ volume :=
  exists_convexBody_midpoint_coupling hK hcK
    (convex_interior_nonempty_of_volume_pos hcK hvK) hL hcL
    (convex_interior_nonempty_of_volume_pos hcL hvL)

end Problem358

end

end OAI
