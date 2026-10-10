import OAI.Geometry.SurfaceImmersion.Primitive.CircularFlatBump
import OAI.Geometry.Immersion.ClosedSurface.ChartTransition
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas
import OAI.Geometry.SurfaceImmersion.Correction.ManifoldFreeIncrement

namespace OAI

/-! A finite smoothing atlas whose positive loci are actual coordinate disks.
The cutoffs are flat circular functions, not arbitrary subordinate bumps. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

def circularCoordinateRegion (p : M) (r : ℝ) : Set SmallModes.Base :=
  {x | circularRadiusSquared (coordinateChart p p) x ≤ r^2}

def circularCoordinateDisk (p : M) (r : ℝ) : Set M :=
  (coordinateChart p).source ∩
    (coordinateChart p) ⁻¹' {x | circularRadiusSquared (coordinateChart p p) x < r^2}

def circularDiskClosure (p : M) (r : ℝ) : Set M :=
  (coordinateChart p).symm '' circularCoordinateRegion p r

def circularManifoldBump (p : M) (r : ℝ) : M → ℝ :=
  (coordinateChart p).source.indicator
    (fun x => circularFlatBump (coordinateChart p p) r (coordinateChart p x))

lemma circularCoordinateRegion_compact (p : M) (r : ℝ) :
    IsCompact (circularCoordinateRegion p r) := by
  apply (isCompact_closedBall (coordinateChart p p) |r|).of_isClosed_subset
    (isClosed_le (circularRadiusSquared_smooth _).continuous continuous_const)
  intro x hx
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact circularRadiusSquared_le_norm hx

lemma circularManifoldBump_nonneg (p x : M) (r : ℝ) :
    0 ≤ circularManifoldBump p r x := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · rw [circularManifoldBump,indicator_of_mem hx]
    exact circularFlatBump_nonneg _ _ _
  · rw [circularManifoldBump,indicator_of_notMem hx]

lemma circularManifoldBump_pos_iff (p x : M) (r : ℝ) :
    0 < circularManifoldBump p r x ↔ x ∈ circularCoordinateDisk p r := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · simp only [circularManifoldBump,indicator_of_mem hx,circularCoordinateDisk,
      mem_inter_iff,hx,true_and,mem_preimage,Set.mem_ofPred_eq,circularFlatBump_pos_iff]
  · simp only [circularManifoldBump,indicator_of_notMem hx,circularCoordinateDisk,
      mem_inter_iff,hx,false_and,lt_self_iff_false]

variable [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_open (p : M) (r : ℝ) :
    IsOpen (circularCoordinateDisk p r) := by
  exact (coordinateChart p).continuousOn.isOpen_inter_preimage
    (coordinateChart p).open_source
    (isOpen_lt (circularRadiusSquared_smooth _).continuous continuous_const)

omit [IsManifold planeModel ∞ M] in
lemma mem_circularCoordinateDisk (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ circularCoordinateDisk p r := by
  refine ⟨?_,?_⟩
  · rw [coordinateChart_source]
    exact mem_chart_source Plane p
  · change circularRadiusSquared (coordinateChart p p) (coordinateChart p p) < r^2
    simpa only [circularRadiusSquared,sub_self,zero_pow (by decide : 2 ≠ 0),zero_add] using
      sq_pos_of_pos hr

variable [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_compact (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularDiskClosure p r) :=
  (circularCoordinateRegion_compact p r).image_of_continuousOn
    ((coordinateChart p).continuousOn_symm.mono hregion)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_source (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularDiskClosure p r ⊆ (coordinateChart p).source := by
  rintro x ⟨y,hy,rfl⟩
  exact (coordinateChart p).map_target (hregion hy)

lemma circularManifoldBump_smooth_support (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (circularManifoldBump p r) ∧
      tsupport (circularManifoldBump p r) ⊆ circularDiskClosure p r := by
  apply contMDiff_indicator_of_support (coordinateChart p).open_source
    (circularDiskClosure_compact p r hregion).isClosed
    (circularDiskClosure_source p r hregion)
    ((circularFlatBump_smooth _ r).contMDiff.comp_contMDiffOn (coordinateChart_smoothOn p))
  intro x hx hnot
  apply (circularFlatBump_zero_iff _ r _).mpr
  by_contra hlt
  apply hnot
  refine ⟨coordinateChart p x,?_,(coordinateChart p).left_inv hx⟩
  exact (not_le.mp hlt).le

omit [IsManifold planeModel ∞ M] [T2Space M] in
/-- The disks can be chosen inside any given neighborhood of their centers. -/
lemma exists_circularCoordinateDisk_subordinate (p : M) {V : Set M}
    (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ r : ℝ, 0 < r ∧
      circularCoordinateRegion p r ⊆ (coordinateChart p).target ∧
      circularDiskClosure p r ⊆ V := by
  let e := coordinateChart p
  have hpS : p ∈ e.source := by rw [coordinateChart_source]; exact mem_chart_source Plane p
  have hU : IsOpen (e.target ∩ e.symm ⁻¹' V) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hV
  have hc : e p ∈ e.target ∩ e.symm ⁻¹' V :=
    ⟨e.map_source hpS,by simpa only [mem_preimage,e.left_inv hpS] using hpV⟩
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hU (e p) hc
  have hsmall : ∀ x ∈ circularCoordinateRegion p (eps/2),
      x ∈ e.target ∩ e.symm ⁻¹' V := by
    intro x hx
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    have hb := circularRadiusSquared_le_norm hx
    rw [abs_of_pos (half_pos heps)] at hb
    exact hb.trans_lt (by linarith)
  refine ⟨eps/2,half_pos heps,fun x hx => (hsmall x hx).1,?_⟩
  rintro x ⟨y,hy,rfl⟩
  exact (hsmall y hy).2

variable [CompactSpace M]

/-- A finite collection of actual circular coordinate disks covers the
surface. Its flat cutoffs are smooth and subordinate to the given cover. -/
theorem exists_finite_circular_cutoffs (V : M → Set M)
    (hV : ∀ p, IsOpen (V p)) (hpV : ∀ p, p ∈ V p) :
    ∃ (t : Finset M) (r : t → ℝ),
      (∀ i : t, 0 < r i) ∧
      (∀ i : t, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target) ∧
      (∀ i : t, circularDiskClosure (i : M) (r i) ⊆ V i) ∧
      (∀ x : M, ∃ i : t, x ∈ circularCoordinateDisk (i : M) (r i)) ∧
      (∀ i : t, ContMDiff planeModel 𝓘(ℝ) ∞ (circularManifoldBump (i : M) (r i))) ∧
      (∀ i : t, tsupport (circularManifoldBump (i : M) (r i)) ⊆ V i) := by
  classical
  choose r hr ht hv using fun p => exists_circularCoordinateDisk_subordinate p (hV p) (hpV p)
  have hc : (univ : Set M) ⊆ ⋃ p, circularCoordinateDisk p (r p) := by
    intro p _
    exact mem_iUnion.mpr ⟨p,mem_circularCoordinateDisk p (hr p)⟩
  obtain ⟨t,hcover⟩ := isCompact_univ.elim_finite_subcover
    (fun p => circularCoordinateDisk p (r p))
    (fun p => circularCoordinateDisk_open p (r p)) hc
  refine ⟨t,fun i => r i,fun i => hr i,fun i => ht i,fun i => hv i,?_,?_,?_⟩
  · intro x
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨⟨i,hi⟩,hxi⟩
  · intro i
    exact (circularManifoldBump_smooth_support (i : M) (r i) (ht i)).1
  · intro i
    exact (circularManifoldBump_smooth_support (i : M) (r i) (ht i)).2.trans (hv i)

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
theorem normalize_finite_positive_cutoffs {ι : Type*} [Fintype ι]
    (f : ι → M → ℝ) (hf : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (f i))
    (hnon : ∀ i x, 0 ≤ f i x) (hcover : ∀ x, ∃ i, 0 < f i x) :
    ∃ w : ι → M → ℝ,
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (w i)) ∧
      (∀ i x, 0 ≤ w i x) ∧ (∀ i x, 0 < w i x ↔ 0 < f i x) ∧
      (∀ i, tsupport (w i) = tsupport (f i)) ∧
      ∀ x, ∑ i, (w i x)^2 = 1 := by
  classical
  let sigma : M → ℝ := fun x => ∑ i, (f i x)^2
  have hpos (x : M) : 0 < sigma x := by
    obtain ⟨i,hi⟩ := hcover x
    exact (sq_pos_of_pos hi).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (f j x)) (Finset.mem_univ i))
  have hsigma : ContMDiff planeModel 𝓘(ℝ) ∞ sigma :=
    contMDiff_finsetSum (fun i _ => (hf i).pow 2)
  have hsqrt : ContMDiff planeModel 𝓘(ℝ) ∞ (fun x => Real.sqrt (sigma x)) := by
    intro x
    exact (Real.contDiffAt_sqrt (hpos x).ne').contMDiffAt.comp x (hsigma x)
  let w : ι → M → ℝ := fun i x => f i x / Real.sqrt (sigma x)
  have hwpos (i : ι) (x : M) : 0 < w i x ↔ 0 < f i x :=
    div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (hpos x))
  refine ⟨w,fun i => (hf i).div₀ hsqrt (fun x => (Real.sqrt_pos.mpr (hpos x)).ne'),
    fun i x => div_nonneg (hnon i x) (Real.sqrt_nonneg _),hwpos,?_,?_⟩
  · intro i
    change closure (Function.support (w i)) = closure (Function.support (f i))
    congr 1
    ext x
    change w i x ≠ 0 ↔ f i x ≠ 0
    change f i x / Real.sqrt (sigma x) ≠ 0 ↔ f i x ≠ 0
    rw [div_ne_zero_iff]
    exact and_iff_left (Real.sqrt_pos.mpr (hpos x)).ne'
  · intro x
    calc
      ∑ i, (w i x)^2 = (∑ i, (f i x)^2) / (Real.sqrt (sigma x))^2 := by
        simp only [w,div_pow,Finset.sum_div]
      _ = sigma x / sigma x := by rw [Real.sq_sqrt (hpos x).le]
      _ = 1 := div_self (hpos x).ne'

/-- A finite atlas with circular positive loci. Outer cutoffs are identically
one near their supports, and all data stay inside the prescribed neighborhoods. -/
theorem exists_circular_smoothingAtlas (V : M → Set M)
    (hV : ∀ p, IsOpen (V p)) (hpV : ∀ p, p ∈ V p) :
    ∃ (A : SmoothingAtlas M) (r : A.centers → ℝ),
      (∀ i : A.centers, 0 < r i) ∧
      (∀ i : A.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target) ∧
      (∀ i : A.centers, circularDiskClosure (i : M) (r i) ⊆ V i) ∧
      (∀ i x, 0 ≤ A.weight i x) ∧
      (∀ i x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) (r i)) ∧
      (∀ i, tsupport (A.weight i) ⊆ V i) ∧
      ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1) := by
  classical
  obtain ⟨t,r,hr,hregion,hinside,hcover,hsmooth,hsupport⟩ :=
    exists_finite_circular_cutoffs V hV hpV
  let f : t → M → ℝ := fun i => circularManifoldBump (i : M) (r i)
  obtain ⟨w,hw,hwnon,hwpos,hwsupport,hpart⟩ := normalize_finite_positive_cutoffs f hsmooth
    (fun i x => circularManifoldBump_nonneg (i : M) x (r i)) (fun x => by
      obtain ⟨i,hi⟩ := hcover x
      exact ⟨i,(circularManifoldBump_pos_iff (i : M) x (r i)).mpr hi⟩)
  have hwchart (i : t) : tsupport (w i) ⊆ (chart (i : M)).source := by
    rw [hwsupport i]
    intro x hx
    have hxC := (circularManifoldBump_smooth_support (i : M) (r i) (hregion i)).2 hx
    have hxS := circularDiskClosure_source (i : M) (r i) (hregion i) hxC
    simpa only [coordinateChart_source,chart_source] using hxS
  have hwV (i : t) : tsupport (w i) ⊆ V i := by
    rw [hwsupport i]
    exact hsupport i
  have hout : ∀ i : t, ∃ chi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ chi ∧
      tsupport chi ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (w i), chi =ᶠ[𝓝 x] (fun _ => 1) := by
    intro i
    have hc : IsCompact (tsupport (w i)) := (isClosed_tsupport _).isCompact
    obtain ⟨B,hB,hKB,hBc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hwchart i))
    obtain ⟨O,hO,hKO,hOc⟩ := hc.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hKB)
    obtain ⟨chi,hchi,_,hchis,hchione⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hB isClosed_closure hOc
    refine ⟨chi,hchi,?_,?_⟩
    · change closure (Function.support chi) ⊆ _
      rw [hchis]
      exact hBc
    · intro x hx
      filter_upwards [hO.mem_nhds (hKO hx)] with y hy
      exact (hchione y).mp (subset_closure hy)
  choose chi hchi hchis hchione using hout
  let A : SmoothingAtlas M :=
    ⟨t,w,chi,hw,hwchart,hchi,hchis,fun i x hx => (hchione i x hx).eq_of_nhds,hpart⟩
  refine ⟨A,r,hr,hregion,hinside,hwnon,?_,hwV,hchione⟩
  intro i x
  exact (hwpos i x).trans (circularManifoldBump_pos_iff (i : M) x (r i))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
