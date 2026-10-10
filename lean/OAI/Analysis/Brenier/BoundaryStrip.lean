import Mathlib

namespace OAI

section

open MeasureTheory Set
open scoped ENNReal

namespace Problem358

/-- The right boundary strip of a compact real interval has length at most
its translation distance, even when the interval is shorter than that distance. -/
theorem volume_convex_boundary_strip_le
    {I : Set ℝ} (hI : IsCompact I) (hc : Convex ℝ I)
    {h : ℝ} (hh : 0 ≤ h) :
    volume {t | t ∈ I ∧ t + h ∉ I} ≤ ENNReal.ofReal h := by
  by_cases hne : I.Nonempty
  · have hsup : sSup I ∈ I := hI.sSup_mem hne
    have hsub : {t | t ∈ I ∧ t + h ∉ I} ⊆ Ioc (sSup I - h) (sSup I) := by
      intro t ht
      have htle : t ≤ sSup I := le_csSup hI.bddAbove ht.1
      refine ⟨?_, htle⟩
      by_contra hnot
      have hshift : t + h ≤ sSup I := by linarith
      have hinside : t + h ∈ I :=
        hc.ordConnected.out ht.1 hsup ⟨by linarith, hshift⟩
      exact ht.2 hinside
    calc
      volume {t | t ∈ I ∧ t + h ∉ I} ≤ volume (Ioc (sSup I - h) (sSup I)) :=
        measure_mono hsub
      _ = ENNReal.ofReal h := by rw [Real.volume_Ioc]; congr 1; ring
  · have hzero : I = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hzero]

/-- Fubini converts the one-dimensional strip estimate into a product estimate.
The hypotheses describe exactly the interval fibers needed by coordinate slicing. -/
theorem prod_measure_boundary_strip_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {K : Set (X × ℝ)} (hK : MeasurableSet K)
    (hproj : MeasurableSet (Prod.fst '' K))
    (hcompact : ∀ x, IsCompact {t : ℝ | (x, t) ∈ K})
    (hconvex : ∀ x, Convex ℝ {t : ℝ | (x, t) ∈ K})
    {h : ℝ} (hh : 0 ≤ h) :
    (μ.prod volume) {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K} ≤
      ENNReal.ofReal h * μ (Prod.fst '' K) := by
  have hshift : Measurable (fun p : X × ℝ => (p.1, p.2 + h)) :=
    measurable_fst.prodMk (measurable_snd.add_const h)
  have hstrip : MeasurableSet {p : X × ℝ | p ∈ K ∧ (p.1, p.2 + h) ∉ K} :=
    hK.inter (hK.preimage hshift).compl
  rw [Measure.prod_apply hstrip]
  calc
    (∫⁻ x, volume (Prod.mk x ⁻¹' {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K}) ∂μ) ≤
        ∫⁻ x, (Prod.fst '' K).indicator (fun _ => ENNReal.ofReal h) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ Prod.fst '' K
      · rw [Set.indicator_of_mem hx]
        exact volume_convex_boundary_strip_le (hcompact x) (hconvex x) hh
      · rw [Set.indicator_of_notMem hx]
        have hempty : Prod.mk x ⁻¹' {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hx ⟨(x, t), ht.1, rfl⟩
        simp [hempty]
    _ = ENNReal.ofReal h * μ (Prod.fst '' K) := lintegral_indicator_const hproj _

/-- A vertical fiber of a compact set is compact. -/
theorem isCompact_vertical_fiber
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set (X × ℝ)} (hK : IsCompact K) (x : X) :
    IsCompact {t : ℝ | (x, t) ∈ K} := by
  have hslice : IsCompact (K ∩ Prod.fst ⁻¹' {x}) :=
    hK.inter_right (isClosed_singleton.preimage continuous_fst)
  have heq : {t : ℝ | (x, t) ∈ K} = Prod.snd '' (K ∩ Prod.fst ⁻¹' {x}) := by
    ext t
    constructor
    · intro ht
      exact ⟨(x, t), ⟨ht, rfl⟩, rfl⟩
    · rintro ⟨⟨y, s⟩, ⟨hp, hy⟩, hs⟩
      have hyx : y = x := hy
      have hst : s = t := hs
      simpa [hyx, hst] using hp
  rw [heq]
  exact hslice.image continuous_snd

/-- The vertical boundary strip of a compact convex body has product measure
at most its width times the measure of the transverse projection. -/
theorem compact_convex_prod_boundary_strip_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) {K : Set (X × ℝ)}
    (hK : IsCompact K) (hc : Convex ℝ K) {h : ℝ} (hh : 0 ≤ h) :
    (μ.prod volume) {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K} ≤
      ENNReal.ofReal h * μ (Prod.fst '' K) := by
  apply prod_measure_boundary_strip_le μ hK.measurableSet
    (hK.image continuous_fst).measurableSet
    (isCompact_vertical_fiber hK)
  · intro x a ha b hb s t hs ht hst
    have hmem := hc ha hb hs ht hst
    change (x, s • a + t • b) ∈ K
    simpa only [Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hst, one_smul] using hmem
  · exact hh

/-- Any uniformly bounded integrand has an `O(h)` integral on the excluded strip. -/
theorem norm_integral_compact_convex_boundary_strip_le
    {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure X) {K : Set (X × ℝ)}
    (hK : IsCompact K) (hc : Convex ℝ K)
    (hproj : μ (Prod.fst '' K) ≠ ∞)
    {h C : ℝ} (hh : 0 ≤ h) (hC : 0 ≤ C)
    {f : X × ℝ → G} (hf : ∀ p ∈ K, ‖f p‖ ≤ C) :
    ‖∫ p in {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K}, f p ∂(μ.prod volume)‖ ≤
      C * h * μ.real (Prod.fst '' K) := by
  have hbound := compact_convex_prod_boundary_strip_le μ hK hc hh
  have hfinite : ENNReal.ofReal h * μ (Prod.fst '' K) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hproj
  have hsfinite : (μ.prod volume) {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K} < ∞ :=
    lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hfinite)
  have hreal : (μ.prod volume).real {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K} ≤
      h * μ.real (Prod.fst '' K) := by
    have hh' := ENNReal.toReal_mono hfinite hbound
    simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hh] using hh'
  calc
    ‖∫ p in {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K}, f p ∂(μ.prod volume)‖ ≤
        C * (μ.prod volume).real {p | p ∈ K ∧ (p.1, p.2 + h) ∉ K} :=
      norm_setIntegral_le_of_norm_le_const hsfinite (fun p hp => hf p hp.1)
    _ ≤ C * (h * μ.real (Prod.fst '' K)) := mul_le_mul_of_nonneg_left hreal hC
    _ = C * h * μ.real (Prod.fst '' K) := by ring

/-- The strip estimate transports through any measure-preserving linear coordinate
split. This separates geometric slicing from the choice of Euclidean coordinates. -/
theorem boundary_strip_le_of_coordinate_split
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (e : V ≃L[ℝ] (X × ℝ)) (η : Measure V) (μ : Measure X)
    (hpres : MeasurePreserving e η (μ.prod volume))
    {v : V} (hv : e v = (0, 1))
    {K : Set V} (hK : IsCompact K) (hc : Convex ℝ K)
    {h : ℝ} (hh : 0 ≤ h) :
    η {x | x ∈ K ∧ x + h • v ∉ K} ≤
      ENNReal.ofReal h * μ (Prod.fst '' (e '' K)) := by
  have himage : IsCompact (e '' K) := hK.image e.continuous
  have hconvex : Convex ℝ (e '' K) := hc.linear_image e.toLinearMap
  have heqshift (x : V) : e (x + h • v) = ((e x).1, (e x).2 + h) := by
    rw [map_add, map_smul, hv]
    ext <;> simp
  have hpreimage : e ⁻¹' {p | p ∈ e '' K ∧ (p.1, p.2 + h) ∉ e '' K} =
      {x | x ∈ K ∧ x + h • v ∉ K} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← heqshift x,
      Set.mem_image, e.injective.eq_iff, exists_eq_right]
  have hm : MeasurableSet {p : X × ℝ | p ∈ e '' K ∧ (p.1, p.2 + h) ∉ e '' K} :=
    himage.measurableSet.inter
      (himage.measurableSet.preimage
        (measurable_fst.prodMk (measurable_snd.add_const h))).compl
  rw [← hpreimage, hpres.measure_preimage hm.nullMeasurableSet]
  exact compact_convex_prod_boundary_strip_le μ himage hconvex hh

end Problem358

end

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace Problem358

section Geometry
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Contracting toward a point gives a translated core in a convex set. -/
theorem convex_contraction_add_mem {K : Set V} (hK : Convex ℝ K)
    {p e x : V} (hx : x ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • p + t • e ∈ K := by
  have h := hK hx hpe (sub_nonneg.mpr ht1) ht0 (by ring)
  simpa only [smul_add, add_assoc] using h

/-- The contracted image is in the forward translation core. -/
theorem convex_contraction_subset_shift_core {K : Set V} (hK : Convex ℝ K)
    {p e : V} (hp : p ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun x => (1 - t) • x + t • p) '' K ⊆
      {x | x ∈ K ∧ x + t • e ∈ K} := by
  rintro x ⟨z, hz, rfl⟩
  exact ⟨hK hz hp (sub_nonneg.mpr ht1) ht0 (by ring),
    convex_contraction_add_mem hK hz hpe ht0 ht1⟩
end Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  (μ : Measure V) [IsAddHaarMeasure μ]

/-- The Haar measure of an affine contraction, in real-valued form. -/
theorem measureReal_contraction_image (K : Set V) (p : V) {t : ℝ}
    (ht1 : t ≤ 1) :
    μ.real ((fun x => (1 - t) • x + t • p) '' K) =
      (1 - t) ^ Module.finrank ℝ V * μ.real K := by
  have hset : (fun x => (1 - t) • x + t • p) '' K =
      (fun x => x + t • p) '' ((1 - t) • K) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(1 - t) • z, ⟨z, hz, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
  rw [hset, Set.image_add_right, measureReal_def, measure_preimage_add_right,
    addHaar_smul_of_nonneg μ (sub_nonneg.mpr ht1), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (sub_nonneg.mpr ht1) _)]
  rfl

/-- A geometric boundary strip is controlled by the volume lost under contraction. -/
theorem measureReal_convex_shift_strip_le {K : Set V} (hKc : IsCompact K)
    (hK : Convex ℝ K) {p e : V} (hp : p ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {x | x ∈ K ∧ x + t • e ∉ K} ≤
      (1 - (1 - t) ^ Module.finrank ℝ V) * μ.real K := by
  let H := (fun x => (1 - t) • x + t • p) '' K
  have hHc : IsCompact H := hKc.image (by fun_prop)
  have hH : H ⊆ {x | x ∈ K ∧ x + t • e ∈ K} :=
    convex_contraction_subset_shift_core hK hp hpe ht0 ht1
  have hHK : H ⊆ K := fun x hx => (hH hx).1
  have hsub : {x | x ∈ K ∧ x + t • e ∉ K} ⊆ K \ H := by
    intro x hx
    exact ⟨hx.1, fun h => hx.2 (hH h).2⟩
  calc
    μ.real {x | x ∈ K ∧ x + t • e ∉ K} ≤ μ.real (K \ H) :=
      measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hKc.measure_lt_top.ne)
    _ = μ.real K - μ.real H := measureReal_sdiff hHK hHc.measurableSet hKc.measure_lt_top.ne
    _ = (1 - (1 - t) ^ Module.finrank ℝ V) * μ.real K := by
      rw [show μ.real H = (1 - t) ^ Module.finrank ℝ V * μ.real K from
        measureReal_contraction_image μ K p ht1]
      ring

/-- Bernoulli gives a dimension-linear bound for the boundary strip. -/
theorem measureReal_convex_shift_strip_le_linear {K : Set V} (hKc : IsCompact K)
    (hK : Convex ℝ K) {p e : V} (hp : p ∈ K) (hpe : p + e ∈ K)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ.real {x | x ∈ K ∧ x + t • e ∉ K} ≤
      Module.finrank ℝ V * t * μ.real K := by
  apply (measureReal_convex_shift_strip_le μ hKc hK hp hpe ht0 ht1).trans
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith)
    (Module.finrank ℝ V)
  have hpow : 1 - (1 - t) ^ Module.finrank ℝ V ≤ Module.finrank ℝ V * t := by
    simpa only [sub_eq_add_neg] using (by linarith :
      1 - (1 + -t) ^ Module.finrank ℝ V ≤ Module.finrank ℝ V * t)
  exact mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg

/-- Interior-ball specialization of the boundary estimate for small translations. -/
theorem measureReal_convex_shift_strip_le_of_closedBall {K : Set V}
    (hKc : IsCompact K) (hK : Convex ℝ K) {p : V} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall p r ⊆ K) {v : V} (hv : ‖v‖ ≤ 1)
    {h : ℝ} (hh0 : 0 ≤ h) (hhr : h ≤ r) :
    μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤
      Module.finrank ℝ V * (h / r) * μ.real K := by
  have hp : p ∈ K := hball (Metric.mem_closedBall_self hr.le)
  have hpe : p + r • v ∈ K := by
    apply hball
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have ht0 : 0 ≤ h / r := div_nonneg hh0 hr.le
  have ht1 : h / r ≤ 1 := (div_le_one hr).mpr hhr
  have hshift : (h / r) • (r • v) = h • v := by
    rw [smul_smul, div_mul_cancel₀ _ hr.ne']
  simpa only [hshift] using
    measureReal_convex_shift_strip_le_linear μ hKc hK hp hpe ht0 ht1

/-- A single linear constant controls every translation length, not only small ones. -/
theorem measureReal_convex_shift_strip_le_all {K : Set V}
    (hKc : IsCompact K) (hK : Convex ℝ K) {p : V} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall p r ⊆ K) {v : V} (hv : ‖v‖ ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) :
    μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤
      (max (Module.finrank ℝ V : ℝ) 1 * μ.real K / r) * h := by
  have hvol : 0 ≤ μ.real K := measureReal_nonneg
  have herr : 0 ≤ h / r := div_nonneg hh hr.le
  by_cases hhr : h ≤ r
  · calc
      μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤
          Module.finrank ℝ V * (h / r) * μ.real K :=
        measureReal_convex_shift_strip_le_of_closedBall μ hKc hK hr hball hv hh hhr
      _ ≤ max (Module.finrank ℝ V : ℝ) 1 * (h / r) * μ.real K :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) herr) hvol
      _ = _ := by ring
  · have hrh : 1 ≤ h / r := (one_le_div hr).mpr (le_of_not_ge hhr)
    have hmax : 1 ≤ max (Module.finrank ℝ V : ℝ) 1 := le_max_right _ _
    have hfactor : 1 ≤ max (Module.finrank ℝ V : ℝ) 1 * (h / r) := by
      nlinarith
    calc
      μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤ μ.real K :=
        measureReal_mono (fun _ hx => hx.1) hKc.measure_lt_top.ne
      _ ≤ (max (Module.finrank ℝ V : ℝ) 1 * (h / r)) * μ.real K := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hvol
      _ = _ := by ring

/-- Every compact convex body has a uniform linear boundary-strip constant. -/
theorem exists_convex_boundary_strip_constant {K : Set V}
    (hKc : IsCompact K) (hK : Convex ℝ K) (hKi : (interior K).Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : V), ‖v‖ ≤ 1 → ∀ h : ℝ, 0 ≤ h →
      μ.real {x | x ∈ K ∧ x + h • v ∉ K} ≤ C * h := by
  obtain ⟨p, hp⟩ := hKi
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (mem_interior_iff_mem_nhds.mp hp)
  refine ⟨max (Module.finrank ℝ V : ℝ) 1 * μ.real K / r, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (le_trans (by norm_num) (le_max_right _ _))
      measureReal_nonneg) hr.le
  · intro v hv h hh
    exact measureReal_convex_shift_strip_le_all μ hKc hK hr hball hv hh

end Problem358

end

end OAI
