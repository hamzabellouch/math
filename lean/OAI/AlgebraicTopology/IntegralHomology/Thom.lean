import OAI.AlgebraicTopology.IntegralHomology.HyperplaneLocal
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

noncomputable section

namespace Kaplansky

/-! Thom spaces of line stages, disk collapse, quotient maps, and homology. -/

section
open Bundle Topology Set OnePoint

/-- Hausdorffness of a genuine bundle total space, using separation in the
base or in a common local trivialization. -/
theorem bundleTotal_t2Space {B V : Type*} [TopologicalSpace B] [T2Space B]
    [TopologicalSpace V] [T2Space V] (E : B → Type*)
    [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace V E)] [FiberBundle V E] :
    T2Space (TotalSpace V E) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro z w hzw
  by_cases hb : z.proj = w.proj
  · let e := trivializationAt V E z.proj
    have hz : z ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt V E z.proj)
    have hw : w ∈ e.source := e.mem_source.mpr (hb ▸ mem_baseSet_trivializationAt V E z.proj)
    have hne : e z ≠ e w := fun h => hzw (e.toOpenPartialHomeomorph.injOn hz hw h)
    exact (e.continuousAt hz).tendsto.disjoint (disjoint_nhds_nhds.mpr hne)
      (e.continuousAt hw).tendsto
  · exact (FiberBundle.continuous_proj V E).continuousAt.tendsto.disjoint
      (disjoint_nhds_nhds.mpr hb) (FiberBundle.continuous_proj V E).continuousAt.tendsto

open ComplexGrassmann
variable {ι : Type} [Fintype ι] {K : ι → ℕ}

instance lineStageTotal_t2Space (a : LineStage K) : T2Space (TotalSpace a.Model a.Fiber) :=
  bundleTotal_t2Space a.Fiber

instance lineStageTotal_locallyCompactSpace (a : LineStage K) :
    LocallyCompactSpace (TotalSpace a.Model a.Fiber) :=
  ChartedSpace.locallyCompactSpace (ProjectiveProduct K × a.Model) _

/-- The one-point total space used by the homology construction is a
compact Hausdorff space for the actual finite line bundle sum. -/
instance lineStageThom_t2Space (a : LineStage K) :
    T2Space (OnePoint (TotalSpace a.Model a.Fiber)) := inferInstance

omit [Fintype ι] in
theorem lineStage_chart_norm (a : LineStage K)
    (c : ∀ s : a.Slot, productLineChartIndex K (a.label s))
    (y : ProjectiveProduct K) (hy : y ∈ (smoothLineSumCore K a.label).baseSet c)
    (v : a.Fiber y) :
    ‖(((smoothLineSumCore K a.label).localTriv c) ⟨y,v⟩).2‖ = ‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  exact congrArg (fun z : ℂ => Real.sqrt z.re)
    (finiteLineSum_chart_inner _ (fun s => productLineCore_unitary K (a.label s)) c y hy v v)

omit [Fintype ι] in
/-- Closed bounded disk bundles over the compact projective base are compact.
This uses a finite cover by actual unitary trivializations. -/
theorem isCompact_lineStage_disk (a : LineStage K) (r : ℝ) :
    IsCompact {z : TotalSpace a.Model a.Fiber | ‖z.2‖ ≤ r} := by
  classical
  let c := (smoothLineSumCore K a.label).indexAt
  let e := fun y => (smoothLineSumCore K a.label).localTriv (c y)
  have hc (y : ProjectiveProduct K) : y ∈ (e y).baseSet :=
    (smoothLineSumCore K a.label).mem_baseSet_at y
  choose S hSc hSn hSe using fun y => exists_compact_subset (e y).open_baseSet (hc y)
  obtain ⟨u, hu⟩ := CompactSpace.elim_nhds_subcover S
    (fun y => mem_interior_iff_mem_nhds.mp (hSn y))
  let D := fun y => (e y).toOpenPartialHomeomorph.symm ''
    (S y ×ˢ Metric.closedBall (0 : a.Model) r)
  have hD (y) : IsCompact (D y) := by
    apply ((hSc y).prod (isCompact_closedBall (0 : a.Model) r)).image_of_continuousOn
    apply (e y).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro z hz
    exact (e y).mem_target.mpr (hSe y hz.1)
  apply (u.isCompact_biUnion (fun y _ => hD y)).of_isClosed_subset
  · exact isClosed_le (continuous_lineStage_totalNorm a) continuous_const
  · intro z hz
    have hb : z.proj ∈ ⋃ y ∈ u, S y := by rw [hu]; trivial
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hb
    apply mem_iUnion₂.mpr ⟨y,hy,?_⟩
    have hs : z ∈ (e y).source := (e y).mem_source.mpr (hSe y hzy)
    refine ⟨e y z, ⟨?_, ?_⟩, (e y).toOpenPartialHomeomorph.left_inv hs⟩
    · simpa only [(e y).coe_fst hs] using hzy
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (lineStage_chart_norm a (c y) z.proj (hSe y hzy) z.2).trans_le hz

end

section
open Bundle Topology Set OnePoint Filter
open ComplexGrassmann
variable {ι : Type} [Fintype ι] {K : ι → ℕ} (a : LineStage K)

abbrev LineStageClosedDisk := {z : TotalSpace a.Model a.Fiber // ‖z.2‖ ≤ 1}

instance lineStageClosedDisk_compact : CompactSpace (LineStageClosedDisk a) :=
  isCompact_iff_compactSpace.mp (isCompact_lineStage_disk a 1)

/-- Radial collapse of the entire unit sphere bundle to the point at infinity. -/
def lineStageDiskCollapse (z : LineStageClosedDisk a) : OnePoint (TotalSpace a.Model a.Fiber) :=
  if ‖z.val.2‖ = 1 then ∞ else
    (TotalSpace.mk' a.Model z.val.proj
      ((((Real.sqrt (1 - ‖z.val.2‖ ^ 2))⁻¹ : ℝ) : ℂ) • z.val.2) : OnePoint (TotalSpace a.Model a.Fiber))

omit [Fintype ι]

theorem lineStageDiskCollapse_boundary {z : LineStageClosedDisk a} (hz : ‖z.val.2‖ = 1) :
    lineStageDiskCollapse a z = ∞ := by simp [lineStageDiskCollapse, hz]

theorem lineStageDiskCollapse_continuousAt_boundary (z : LineStageClosedDisk a)
    (hz : ‖z.val.2‖ = 1) : ContinuousAt (lineStageDiskCollapse a) z := by
  classical
  let U : Set (LineStageClosedDisk a) := {w | ‖w.val.2‖ ≠ 1}
  have hn : Continuous (fun w : LineStageClosedDisk a => ‖w.val.2‖) :=
    (continuous_lineStage_totalNorm a).comp continuous_subtype_val
  have hrad : Continuous (fun w : LineStageClosedDisk a => Real.sqrt (1 - ‖w.val.2‖ ^ 2)) :=
    (continuous_const.sub (hn.pow 2)).sqrt
  have hsmall : Tendsto (fun w : LineStageClosedDisk a => Real.sqrt (1 - ‖w.val.2‖ ^ 2))
      (𝓝[U] z) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [ContinuousWithinAt, hz] using
        (hrad.continuousAt (x := z)).continuousWithinAt (s := U)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      apply Real.sqrt_pos.mpr
      have hlt : ‖w.val.2‖ < 1 := lt_of_le_of_ne w.property hw
      nlinarith [norm_nonneg w.val.2]
  have hnorm : Tendsto (fun w : LineStageClosedDisk a => ‖w.val.2‖) (𝓝[U] z) (𝓝 (1 : ℝ)) := by
    simpa [ContinuousWithinAt, hz] using hn.continuousAt (x := z) |>.continuousWithinAt (s := U)
  have hlarge := (tendsto_inv_nhdsGT_zero.comp hsmall).atTop_mul_pos zero_lt_one hnorm
  have hescape : Tendsto (fun w : LineStageClosedDisk a =>
      (TotalSpace.mk' a.Model w.val.proj
        ((((Real.sqrt (1 - ‖w.val.2‖ ^ 2))⁻¹ : ℝ) : ℂ) • w.val.2) : OnePoint (TotalSpace a.Model a.Fiber)))
      (𝓝[U] z) (𝓝 ∞) := by
    apply tendsto_onePoint_of_measure _ (continuous_lineStage_totalNorm a)
    convert hlarge using 1
    ext w
    simp only [Function.comp_apply]
    have hsmul := norm_smul (β := EuclideanSpace ℂ a.Slot)
      ((((Real.sqrt (1 - ‖w.val.2‖ ^ 2))⁻¹ : ℝ) : ℂ)) w.val.2
    erw [hsmul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    rfl
  rw [ContinuousAt, lineStageDiskCollapse_boundary a hz, ← nhdsWithin_univ]
  apply Filter.Tendsto.if_nhdsWithin
  · exact tendsto_const_nhds
  · simpa only [univ_inter] using hescape

theorem continuous_lineStageDiskCollapse : Continuous (lineStageDiskCollapse a) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : ‖z.val.2‖ = 1
  · exact lineStageDiskCollapse_continuousAt_boundary a z hz
  · have hn : Continuous (fun w : LineStageClosedDisk a => ‖w.val.2‖) :=
      (continuous_lineStage_totalNorm a).comp continuous_subtype_val
    have hsqrt : Real.sqrt (1 - ‖z.val.2‖ ^ 2) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      have hlt : ‖z.val.2‖ < 1 := lt_of_le_of_ne z.property hz
      nlinarith [norm_nonneg z.val.2]
    have hc : ContinuousAt (fun w : LineStageClosedDisk a =>
        (((Real.sqrt (1 - ‖w.val.2‖ ^ 2))⁻¹ : ℝ) : ℂ)) z :=
      Complex.continuous_ofReal.continuousAt.comp
        (((continuous_const.sub (hn.pow 2)).sqrt.continuousAt).inv₀ hsqrt)
    have hv : ContinuousAt (fun w : LineStageClosedDisk a =>
        TotalSpace.mk' a.Model w.val.proj
          ((((Real.sqrt (1 - ‖w.val.2‖ ^ 2))⁻¹ : ℝ) : ℂ) • w.val.2)) z := by
      rw [FiberBundle.continuousAt_totalSpace]
      have hb : Continuous (fun w : LineStageClosedDisk a => w.val.proj) := (FiberBundle.continuous_proj a.Model a.Fiber).comp continuous_subtype_val
      refine ⟨hb.continuousAt, ?_⟩
      have hw := (FiberBundle.continuousAt_totalSpace a.Model _ (x₀ := z)).mp
        continuous_subtype_val.continuousAt |>.2
      apply (hc.smul hw).congr_of_eventuallyEq
      let e := trivializationAt a.Model a.Fiber z.val.proj
      have he := hb.continuousAt (x := z) (e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt a.Model a.Fiber z.val.proj))
      filter_upwards [he] with w hw
      exact (e.linear ℂ hw).map_smul _ _
    apply (OnePoint.continuous_coe.continuousAt.comp hv).congr_of_eventuallyEq
    filter_upwards [hn.continuousAt (x := z) (isClosed_singleton.isOpen_compl.mem_nhds hz)] with w hw
    exact ite_eq_right hw

/-- An actual vector has a canonical interior preimage under radial collapse. -/
def lineStageDiskInterior (z : TotalSpace a.Model a.Fiber) : LineStageClosedDisk a :=
  ⟨⟨z.proj, (Homeomorph.unitBall z.2).val⟩,
    (mem_ball_zero_iff.mp (Homeomorph.unitBall z.2).property).le⟩

theorem lineStageDiskCollapse_interior (z : TotalSpace a.Model a.Fiber) :
    lineStageDiskCollapse a (lineStageDiskInterior a z) = z := by
  classical
  have hn := mem_ball_zero_iff.mp (Homeomorph.unitBall z.2).property
  rw [lineStageDiskCollapse, ite_eq_right (show ‖(lineStageDiskInterior a z).val.2‖ ≠ 1 from ne_of_lt hn)]
  apply congrArg (fun w : TotalSpace a.Model a.Fiber => (w : OnePoint (TotalSpace a.Model a.Fiber)))
  apply congrArg (TotalSpace.mk' a.Model z.proj)
  dsimp only [lineStageDiskInterior]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm.trans
    ((Homeomorph.unitBall (E := a.Fiber z.proj)).symm_apply_apply z.2)

/-- Only sphere-bundle vectors collapse to infinity. -/
theorem lineStageDiskCollapse_eq_infty_iff (z : LineStageClosedDisk a) :
    lineStageDiskCollapse a z = ∞ ↔ ‖z.val.2‖ = 1 := by
  classical
  simp [lineStageDiskCollapse]

end

section
open Bundle Topology Set OnePoint
open ComplexGrassmann
variable {ι : Type} {K : ι → ℕ} (a : LineStage K)

theorem lineStageDiskInterior_expand (z : LineStageClosedDisk a) (hz : ‖z.val.2‖ ≠ 1) :
    lineStageDiskInterior a (TotalSpace.mk' a.Model z.val.proj
      ((((Real.sqrt (1 - ‖z.val.2‖ ^ 2))⁻¹ : ℝ) : ℂ) • z.val.2)) = z := by
  apply Subtype.ext
  apply congrArg (TotalSpace.mk' a.Model z.val.proj)
  have hlt : ‖z.val.2‖ < 1 := lt_of_le_of_ne z.property hz
  have h := congrArg (fun v : Metric.ball (0 : a.Fiber z.val.proj) 1 => v.val)
    ((Homeomorph.unitBall (E := a.Fiber z.val.proj)).apply_symm_apply
      ⟨z.val.2, mem_ball_zero_iff.mpr hlt⟩)
  exact (congrArg (fun v : a.Fiber z.val.proj => (Homeomorph.unitBall v).val)
    (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm).trans h

/-- Exact quotient relation: collapse the sphere bundle and identify no
distinct interior disk vectors. -/
theorem lineStageDiskCollapse_eq_iff (z w : LineStageClosedDisk a) :
    lineStageDiskCollapse a z = lineStageDiskCollapse a w ↔
      z = w ∨ (‖z.val.2‖ = 1 ∧ ‖w.val.2‖ = 1) := by
  classical
  constructor
  · intro h
    by_cases hz : ‖z.val.2‖ = 1
    · exact Or.inr ⟨hz, (lineStageDiskCollapse_eq_infty_iff a w).mp
        (h.symm.trans (lineStageDiskCollapse_boundary a hz))⟩
    · have hw : ‖w.val.2‖ ≠ 1 := by
        intro hw
        exact hz ((lineStageDiskCollapse_eq_infty_iff a z).mp
          (h.trans (lineStageDiskCollapse_boundary a hw)))
      rw [lineStageDiskCollapse, lineStageDiskCollapse, ite_eq_right hz, ite_eq_right hw] at h
      have he := congrArg (lineStageDiskInterior a) (OnePoint.coe_injective h)
      rw [lineStageDiskInterior_expand a z hz, lineStageDiskInterior_expand a w hw] at he
      exact Or.inl he
  · rintro (rfl | ⟨hz,hw⟩)
    · rfl
    · rw [lineStageDiskCollapse_boundary a hz, lineStageDiskCollapse_boundary a hw]

/-- Positive fiber rank supplies a genuine sphere-bundle point. -/
theorem lineStage_sphere_nonempty [Nonempty a.Slot] :
    ∃ z : LineStageClosedDisk a, ‖z.val.2‖ = 1 := by
  let y := firstCoordinateProduct K
  let : Nontrivial (a.Fiber y) := inferInstanceAs (Nontrivial (EuclideanSpace ℂ a.Slot))
  obtain ⟨v,hv⟩ := exists_norm_eq (E := a.Fiber y) (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨⟨⟨y,v⟩, hv.le⟩,hv⟩

theorem lineStageDiskCollapse_surjective [Nonempty a.Slot] :
    Function.Surjective (lineStageDiskCollapse a) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨w,hw⟩ := lineStage_sphere_nonempty a
    exact ⟨w,lineStageDiskCollapse_boundary a hw⟩
  | coe z => exact ⟨lineStageDiskInterior a z,lineStageDiskCollapse_interior a z⟩

theorem lineStageDiskCollapse_isQuotientMap [Nonempty a.Slot] :
    IsQuotientMap (lineStageDiskCollapse a) :=
  IsQuotientMap.of_surjective_continuous (lineStageDiskCollapse_surjective a)
    (continuous_lineStageDiskCollapse a)

/-- The disk/sphere quotient, with its quotient topology. The exact relation
is given by `lineStageDiskCollapse_eq_iff`. -/
abbrev LineStageThomQuotient := Quotient (Setoid.ker (lineStageDiskCollapse a))

/-- The actual disk/sphere Thom quotient is homeomorphic to the one-point
total space used in the singular homology construction. This assertion is
for positive fiber rank; no characteristic class is assumed. -/
def lineStageThomQuotientHomeomorph [Nonempty a.Slot] :
    LineStageThomQuotient a ≃ₜ OnePoint (TotalSpace a.Model a.Fiber) :=
  @Topology.IsQuotientMap.homeomorph _ _ _ _
    ⟨lineStageDiskCollapse a,continuous_lineStageDiskCollapse a⟩
    (lineStageDiskCollapse_isQuotientMap a)

theorem lineStageThomQuotientHomeomorph_apply [Nonempty a.Slot] (z : LineStageClosedDisk a) :
    lineStageThomQuotientHomeomorph a (Quotient.mk _ z) = lineStageDiskCollapse a z := rfl

/-- The zero-section inclusion is carried to the actual zero-section map,
so the quotient comparison respects the section used by the invariant. -/
theorem lineStageThomQuotientHomeomorph_zero [Nonempty a.Slot] (y : ProjectiveProduct K) :
    lineStageThomQuotientHomeomorph a
      (Quotient.mk _ (⟨TotalSpace.mk' a.Model y 0, by erw [norm_zero]; exact zero_le_one⟩ : LineStageClosedDisk a)) =
        (TotalSpace.mk' a.Model y (0 : a.Fiber y) : OnePoint (TotalSpace a.Model a.Fiber)) := by
  simp only [lineStageThomQuotientHomeomorph_apply, lineStageDiskCollapse]
  change (if ‖(0 : EuclideanSpace ℂ a.Slot)‖ = 1 then ∞ else _) = _
  simp only [norm_zero, zero_ne_one, ↓reduceIte]
  congr 2
  exact smul_zero _

end

open Bundle Topology CategoryTheory OnePoint
section
open ComplexGrassmann
variable {ι : Type} {K : ι → ℕ} (a : LineStage K)

/-- The actual zero section into the disk/sphere quotient. -/
def thomQuotientZeroSection : C(ProjectiveProduct K, LineStageThomQuotient a) where
  toFun y := Quotient.mk _ (⟨TotalSpace.mk' a.Model y 0, by erw [norm_zero]; exact zero_le_one⟩ : LineStageClosedDisk a)
  continuous_toFun := by
    have h : Continuous (fun y => (⟨TotalSpace.mk' a.Model y 0, by erw [norm_zero]; exact zero_le_one⟩ : LineStageClosedDisk a)) := by
      apply Continuous.subtype_mk
      exact Bundle.Trivialization.continuous_zeroSection ℂ (F := a.Model) (E := a.Fiber)
    exact continuous_quotient_mk'.comp h

/-- The integral homology morphism of the genuine Thom zero section.
Its definition supplies no nonvanishing, Thom class, or Chern-class axiom. -/
def thomZeroHomologyMap (n : ℕ) :=
  (integralSingularHomology n).map (TopCat.ofHom (thomQuotientZeroSection a))

def thomQuotientHomologyIso [Nonempty a.Slot] (n : ℕ) :
    (integralSingularHomology n).obj (TopCat.of (LineStageThomQuotient a)) ≅
      (integralSingularHomology n).obj (TopCat.of (OnePoint (TotalSpace a.Model a.Fiber))) :=
  (integralSingularHomology n).mapIso
    (TopCat.isoOfHomeo (lineStageThomQuotientHomeomorph a))

theorem thomZeroHomologyMap_comparison [Nonempty a.Slot] (n : ℕ) :
    thomZeroHomologyMap a n ≫ (thomQuotientHomologyIso a n).hom =
      sectionHomologyMap (fun y => (0 : a.Fiber y)) (Bundle.Trivialization.continuous_zeroSection ℂ (F := a.Model) (E := a.Fiber)) n := by
  change (integralSingularHomology n).map _ ≫ (integralSingularHomology n).map _ = _
  rw [← Functor.map_comp]
  apply congrArg ((integralSingularHomology n).map)
  ext y
  exact lineStageThomQuotientHomeomorph_zero a y

/-- Every continuous section computes the same map from the base into
the homology of the genuine Thom space, under the proved comparison. -/
theorem thomZeroHomologyMap_eq_section [Nonempty a.Slot]
    (s : ∀ y, a.Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' a.Model y (s y))) (n : ℕ) :
    thomZeroHomologyMap a n ≫ (thomQuotientHomologyIso a n).hom = sectionHomologyMap s hs n :=
  (thomZeroHomologyMap_comparison a n).trans
    (@sectionHomologyMap_eq _ a.Model _ _ _ a.Fiber _ _ _
      (smoothLineSumCore K a.label).fiberBundle (smoothLineSumCore K a.label).vectorBundle
      _ s (Bundle.Trivialization.continuous_zeroSection ℂ (F := a.Model) (E := a.Fiber)) hs n)

/-- A nowhere-zero section forces the Thom zero-section map itself to
vanish, using the actual inverse of the homology comparison isomorphism. -/
theorem thomZeroHomologyMap_eq_zero_of_nonvanishing [Nonempty a.Slot]
    (s : ∀ y, a.Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' a.Model y (s y)))
    (hne : ∀ y, s y ≠ 0) {n : ℕ} (hn : n ≠ 0) : thomZeroHomologyMap a n = 0 := by
  have h := thomZeroHomologyMap_eq_section a s hs n
  rw [@sectionHomologyMap_eq_zero _ a.Model _ _ _ a.Fiber _ _ _
    (smoothLineSumCore K a.label).fiberBundle (smoothLineSumCore K a.label).vectorBundle
    s hs (continuous_lineStage_totalNorm a) hne n hn] at h
  have hi := congrArg (fun f => f ≫ (thomQuotientHomologyIso a n).inv) h
  simpa [Category.assoc] using hi

variable [Fintype ι]

/-- Specialization to the exact canonical hyperplane-product section.
This identifies two constructed global maps; it does not compute them. -/
theorem hyperplaneThomHomology_comparison
    [Nonempty (hyperplaneProductStage K).Slot] (n : ℕ) :
    thomZeroHomologyMap (hyperplaneProductStage K) n ≫
      (thomQuotientHomologyIso (hyperplaneProductStage K) n).hom =
        canonicalProductHomologyMap K n :=
  thomZeroHomologyMap_eq_section _ _ (continuous_hyperplaneProductSection K) n

end

end Kaplansky

end

end OAI
