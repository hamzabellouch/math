import OAI.Geometry.ConjugatePoints.Distance
import OAI.Geometry.ConjugatePoints.Convexity
import OAI.Geometry.ConjugatePoints.FundamentalGroup
import OAI.Geometry.ConjugatePoints.NoConjugatePoints

namespace OAI

noncomputable section

/-!
# The universal-cover shear obstruction and the three-manifold existence theorem.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff UpperHalfPlane
namespace ThreeManifold.CompactMetric
open GluedConstruction HyperbolicCore LoopTopology RiemannianCoordinates
lemma lowPoint_clip : height (projection lowPoint) ≤ Real.log 4 := by
  rw [height_projection_high (by norm_num [lowPoint])]
  exact (Real.log_lt_log (by norm_num [lowPoint]) (by norm_num [lowPoint] : lowPoint.im < 4)).le
lemma blockMap_low (i : Bool) (t : ℝ) :
    blockMap i (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle)) =
      inclusion i (pieceFiber lowPoint lowPoint_core t) := by
  change inclusion i (clippedPiece (projection lowPoint,((6*t : ℝ) : GluedConstruction.Circle))) = _
  rw [clippedPiece_fixed _ lowPoint_clip]
  rfl
lemma compact_fiber_periodic (i : Bool) :
    (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 1 =
      (inclusion i ∘ pieceFiber lowPoint lowPoint_core) 0 := by
  apply congrArg (inclusion i)
  apply Prod.ext
  · rfl
  · change ((6*(1:ℝ) : ℝ) : GluedConstruction.Circle) = ((6*(0:ℝ) : ℝ) : GluedConstruction.Circle)
    simp
lemma block_fiber_low_nontrivial (i : Bool) :
    FundamentalGroup.map (blockMap i) (projection lowPoint,0) (pair 1 circleClass) ≠ 1 := by
  obtain ⟨δ,hδ,hhalf,hn⟩ := exists_uniform_compact_noConjugatePoints
  let hd : δ ∈ Ioc (0:ℝ) (1/2) := ⟨hδ,hhalf⟩
  let γ := inclusion i ∘ pieceFiber lowPoint lowPoint_core
  have hg : IsGeodesicOn (realCompactMetric hd) γ univ := compact_fiber_geodesic hd i
  have hper : γ 1 = γ 0 := compact_fiber_periodic i
  let P := closedCurvePath (contMDiffOn_univ.mp hg.1).continuous hper
  have hessential : (Path.Homotopic.Quotient.mk P : FundamentalGroup Manifold (γ 0)) ≠ (1 : FundamentalGroup Manifold (γ 0)) :=
    closedGeodesic_essential (realCompactMetric hd) (hn δ hd le_rfl) hg hper (compact_fiber_velocity hd i)
  have hbase : blockMap i (projection lowPoint,0) = γ 0 := by
    dsimp only [γ,Function.comp_apply]
    simpa only [mul_zero,AddCircle.coe_zero] using blockMap_low i 0
  have he : FundamentalGroup.map (blockMap i) (projection lowPoint,0) (pair 1 circleClass) =
      Path.Homotopic.Quotient.cast (Path.Homotopic.Quotient.mk P) hbase hbase := by
    change Path.Homotopic.Quotient.mk ((((Path.refl (projection lowPoint)).prod circlePath).map (blockMap i).continuous)) =
      Path.Homotopic.Quotient.mk (P.cast hbase hbase)
    congr 1
    apply Path.ext
    funext t
    exact blockMap_low i t
  intro hnull
  apply hessential
  apply (loop_cast_eq_one_iff hbase (Path.Homotopic.Quotient.mk P)).mp
  exact he.symm.trans hnull

theorem fiberClass_ne_one (i : Bool) : fiberClass i ≠ 1 := by
  let : LocallyPathConnectedSpace Surface := ChartedSpace.locallyPathConnectedSpace ℂ Surface
  let : PathConnectedSpace Surface := PathConnectedSpace.of_locallyPathConnectedSpace
  intro hnull
  have hb : FundamentalGroup.map (blockMap i) wholeBase (pair 1 circleClass) = 1 :=
    (mapOfEq_eq_one_iff (blockMap i) (blockMap_base i) (pair 1 circleClass)).mp hnull
  apply block_fiber_low_nontrivial i
  exact (fiber_null_transfer (blockMap i)
    (PathConnectedSpace.somePath (projection lowPoint) baseSurface) circleClass).mpr hb
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

theorem universalMetric_exists_CN (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (a b : E3) :
    let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
    ∃ m : E3, ∀ z, D m z ^2 ≤ (D a z ^2 + D b z ^2)/2 - D a b ^2/4 := by
  let q := exponential g p a
  have hbase : exponential g p a = exponential g q 0 := (exponential_zero g q).symm
  obtain ⟨e,he0,he,hc,hci,hi⟩ := exists_exponential_coordinates g hn a 0 hbase
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  let Q := @dist E3 (universalMetric g hn q).toPseudoMetricSpace.toDist
  have hid (x y : E3) : Q (e x) (e y) = D x y :=
    @Isometry.dist_eq E3 E3 (universalMetric g hn p).toPseudoMetricSpace
      (universalMetric g hn q).toPseudoMetricSpace e hi x y
  refine ⟨e.symm ((1/2:ℝ) • e b),fun z => ?_⟩
  have hh := universalMetric_radial_CN g hn q (e b) (e z)
  change Q ((1/2:ℝ) • e b) (e z) ^2 ≤
    (Q 0 (e z) ^2 + Q (e b) (e z) ^2)/2 - Q 0 (e b) ^2/4 at hh
  rw [← he0,hid,hid,hid] at hh
  change D (e.symm ((1/2:ℝ) • e b)) z ^2 ≤ _
  rw [← hid,e.apply_symm_apply]
  exact hh

def universalCN (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    @NonpositiveMetric.CNMidpoint E3 (universalMetric g hn p) := by
  refine @NonpositiveMetric.CNMidpoint.mk E3 (universalMetric g hn p)
    (fun a b => (universalMetric_exists_CN g hn p a b).choose) ?_
  intro a b z
  exact (universalMetric_exists_CN g hn p a b).choose_spec z
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold MeasureTheory
open scoped ContDiff ENNReal
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma universalMetric_radial_dist_of_le (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) {a b : ℝ} (hab : a ≤ b) :
    @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist (a • v) (b • v) =
      (b-a)*Real.sqrt (g.inner p v v) := by
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  apply le_antisymm
  · let : RiemannianBundle (TangentSpace 𝓘(ℝ,E3) : E3 → Type _) :=
      ⟨(exponentialMetric g hn p).toRiemannianMetric⟩
    have hc : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E3) 1 (fun r : ℝ => r • v) :=
      (contDiff_id.smul contDiff_const).contMDiff
    have hh := riemannianEDist_le_pathELength hc.contMDiffOn rfl rfl hab
    rw [exponentialMetric_radial_length,← ENNReal.ofReal_mul (Real.sqrt_nonneg _),mul_comm] at hh
    change @edist E3 (universalMetric g hn p).toPseudoEMetricSpace.toEDist (a • v) (b • v) ≤ _ at hh
    rw [@edist_dist E3 (universalMetric g hn p).toPseudoMetricSpace] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hab) (Real.sqrt_nonneg _))).mp hh
  · have hh := universalMetric_lower g hn p (a • v) (b • v)
    have hs : Real.sqrt (g.inner p (b • v - a • v) (b • v - a • v)) =
        (b-a)*Real.sqrt (g.inner p v v) := by
      rw [← sub_smul,positive_form_smul,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (sub_nonneg.mpr hab)]
    rwa [hs] at hh

lemma universalMetric_radial_dist (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (a b : ℝ) :
    @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist (a • v) (b • v) =
      |a-b| * Real.sqrt (g.inner p v v) := by
  rcases le_total a b with hab | hba
  · rw [universalMetric_radial_dist_of_le g hn p v hab,abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [@dist_comm E3 (universalMetric g hn p).toPseudoMetricSpace,
      universalMetric_radial_dist_of_le g hn p v hba,abs_of_nonneg (sub_nonneg.mpr hba)]

lemma universalMetric_radial_isometry (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (v : E3) (hv : g.inner p v v = 1) :
    @Isometry ℝ E3 inferInstance (universalMetric g hn p).toPseudoEMetricSpace
      (fun t : ℝ => t • v) := by
  apply @Isometry.of_dist_eq ℝ E3 inferInstance (universalMetric g hn p).toPseudoMetricSpace
  intro a b
  simp only [universalMetric_radial_dist,hv,Real.sqrt_one,mul_one,Real.dist_eq]
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [CompactSpace M] [T2Space M]

lemma universalMetric_segments (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g)
    (p : M) (a b : E3) :
    let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
    ∃ c : ℝ → E3, c 0 = a ∧ c 1 = b ∧ ∀ s t, D (c s) (c t) = |s-t| * D a b := by
  let q := exponential g p a
  have hbase : exponential g p a = exponential g q 0 := (exponential_zero g q).symm
  obtain ⟨e,he0,he,hc,hci,hi⟩ := exists_exponential_coordinates g hn a 0 hbase
  let D := @dist E3 (universalMetric g hn p).toPseudoMetricSpace.toDist
  let Q := @dist E3 (universalMetric g hn q).toPseudoMetricSpace.toDist
  have hid (x y : E3) : Q (e x) (e y) = D x y :=
    @Isometry.dist_eq E3 E3 (universalMetric g hn p).toPseudoMetricSpace
      (universalMetric g hn q).toPseudoMetricSpace e hi x y
  refine ⟨fun t => e.symm (t • e b),?_,?_,?_⟩
  · simp only [zero_smul,← he0,e.symm_apply_apply]
  · simp only [one_smul,e.symm_apply_apply]
  · intro s t
    change D (e.symm (s • e b)) (e.symm (t • e b)) = |s-t| * D a b
    rw [← hid,← hid a b,he0,e.apply_symm_apply,e.apply_symm_apply]
    dsimp only [Q]
    rw [universalMetric_radial_dist g hn q,universalMetric_radial_zero g hn q]

def npcDeckIsometry (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M) :
    UniversalDeck.group (exponential g p) →*
      @IsometryEquiv E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
        (universalMetric g hn p).toPseudoEMetricSpace where
  toFun d := @IsometryEquiv.mk E3 E3 (universalMetric g hn p).toPseudoEMetricSpace
    (universalMetric g hn p).toPseudoEMetricSpace d.val (universalMetric_deck_isometry g hn p d)
  map_one' := by apply DFunLike.ext; intro x; rfl
  map_mul' _ _ := by apply DFunLike.ext; intro x; rfl

theorem npc_deck_shear_impossible [PathConnectedSpace M]
    (g : SmoothMetric M) (hn : NonpositiveSectionalCurvature g) (p : M)
    (f h a b c d : UniversalDeck.group (exponential g p))
    (hf : f ≠ 1) (hh : h ≠ 1)
    (hfh : Commute f h) (hfa : Commute f a) (hfb : Commute f b)
    (hhc : Commute h c) (hhd : Commute h d)
    (hrel : h = a*b*a⁻¹*b⁻¹) (hrel2 : h*f = c*d*c⁻¹*d⁻¹) : False := by
  let : MetricSpace E3 := universalMetric g hn p
  let : PseudoMetricSpace E3 := (universalMetric g hn p).toPseudoMetricSpace
  let : PseudoEMetricSpace E3 := (universalMetric g hn p).toPseudoEMetricSpace
  let : ProperSpace E3 := universalMetric_proper g hn p
  let F := npcDeckIsometry g hn p
  have hfree (k : UniversalDeck.group (exponential g p)) (hk : k ≠ 1) (x : E3) : F k x ≠ x := by
    intro heq
    apply hk
    apply UniversalDeck.deck_ext (npc_exponential_isCoveringMap g hn p) (z := x)
    exact heq
  have hmin (k : UniversalDeck.group (exponential g p)) :
      (NonpositiveMetric.CNMidpoint.minset (F k : E3 → E3)).Nonempty :=
    npc_deck_displacement_minimum g hn p k
  apply (universalCN g hn p).cyclic_shear_obstruction (universalMetric_segments g hn p)
    (F f) (F h) (F a) (F b) (F c) (F d) (hmin f) (hmin h)
    (hfree f hf) (hfree h hh) (hfh.map F) (hfa.map F) (hfb.map F) (hhc.map F) (hhd.map F)
  · simpa only [map_mul,map_inv] using congrArg F hrel
  · simpa only [map_mul,map_inv] using congrArg F hrel2

end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.LoopTopology
variable {X : Type} [TopologicalSpace X]
def groupBasepointEq {x y : X} (h : x = y) : FundamentalGroup X x ≃* FundamentalGroup X y := by
  subst y
  exact MulEquiv.refl _
end ThreeManifold.LoopTopology
namespace ThreeManifold.CompactMetric
open GluedConstruction RiemannianCoordinates LoopTopology

theorem realCompact_noNPC (g : SmoothMetric Manifold) : ¬ NonpositiveSectionalCurvature g := by
  let : LocallyPathConnectedSpace Manifold := ChartedSpace.locallyPathConnectedSpace E3 Manifold
  let : PathConnectedSpace Manifold := PathConnectedSpace.of_locallyPathConnectedSpace
  intro hn
  let hp := npc_exponential_isCoveringMap g hn basePoint
  let e : FundamentalGroup Manifold basePoint ≃* UniversalDeck.group (exponential g basePoint) :=
    ((groupBasepointEq (exponential_zero g basePoint).symm).trans
      (UniversalDeck.fundamentalGroupEquiv hp 0)).trans (MulEquiv.inv' _).symm
  have hne (x : FundamentalGroup Manifold basePoint) (hx : x ≠ 1) : e x ≠ 1 := by
    intro he
    apply hx
    apply e.injective
    exact he.trans e.map_one.symm
  obtain ⟨a,b,c,d,hfh,hfa,hfb,hhc,hhd,hrel,hrel2⟩ := actual_loop_relations
  apply npc_deck_shear_impossible g hn basePoint
    (e (fiberClass false)) (e (fiberClass true)) (e a) (e b) (e c) (e d)
    (hne _ (fiberClass_ne_one false)) (hne _ (fiberClass_ne_one true))
    (hfh.map e.toMonoidHom) (hfa.map e.toMonoidHom) (hfb.map e.toMonoidHom)
    (hhc.map e.toMonoidHom) (hhd.map e.toMonoidHom)
  · simpa only [map_mul,map_inv] using congrArg e hrel
  · simpa only [map_mul,map_inv] using congrArg e hrel2
end ThreeManifold.CompactMetric
end

namespace ThreeManifold
open Set GluedConstruction CompactMetric

theorem main_theorem : MainStatement := by
  obtain ⟨δ,hδ,hhalf,hn⟩ := exists_uniform_compact_noConjugatePoints
  let hd : δ ∈ Ioc (0:ℝ) (1/2) := ⟨hδ,hhalf⟩
  refine ⟨Manifold,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    realCharts,realSmooth,manifold_oriented,⟨realCompactMetric hd,hn δ hd le_rfl⟩,?_⟩
  rintro ⟨g,hg⟩
  exact realCompact_noNPC g hg
end ThreeManifold

end

end OAI
