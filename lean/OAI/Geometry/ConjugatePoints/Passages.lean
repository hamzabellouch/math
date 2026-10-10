import OAI.Geometry.ConjugatePoints.CompactMetric
import OAI.Geometry.ConjugatePoints.Continuation
import OAI.Geometry.ConjugatePoints.Returning

namespace OAI

noncomputable section

/-!
# Passage supports, extension, and compact metric estimates.
-/

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.TwoGluing
variable {X Y : Type} [TopologicalSpace X] (O : TopologicalSpace.Opens X) (e : O ≃ₜ O)
def descend (f : Bool → X → Y) : Space O e → Y :=
  fun p => f (representative O e p).1 (representative O e p).2
lemma descend_inclusion (f : Bool → X → Y)
    (hf : ∀ x : O, f false x.1 = f true (e x).1) (i : Bool) (x : X) :
    descend O e f (inclusion O e i x) = f i x := by
  let p := representative O e (inclusion O e i x)
  have he : inclusion O e p.1 p.2 = inclusion O e i x := representative_spec O e _
  change f p.1 p.2 = f i x
  rcases p with ⟨j,y⟩
  cases j <;> cases i
  · exact congrArg (f false) ((inclusion_openEmbedding O e false).injective he)
  · obtain ⟨hy,hxy⟩ := (inclusion_mixed_eq O e _ _).mp he
    exact (hf ⟨y,hy⟩).trans (congrArg (f true) hxy)
  · obtain ⟨hx,hxy⟩ := (inclusion_mixed_eq O e _ _).mp he.symm
    exact (congrArg (f true) hxy.symm).trans (hf ⟨x,hx⟩).symm
  · exact congrArg (f true) ((inclusion_openEmbedding O e true).injective he)
end ThreeManifold.TwoGluing
namespace ThreeManifold.CompactMetric

section
open MetricConstruction CylinderConstruction GluedConstruction
lemma logCuspMap_change (a b : ℝ) (ha : 1 < a) (hb : 1 < b) (hab : a ≤ b)
    {q : WholePiece} (hq : q ∈ wholeCusp b) :
    logCuspMap a ha q = logCuspMap b hb q := by
  obtain ⟨z,hz,hzq⟩ := hq
  let r := CircleConstruction.sectionMap 6 q.2
  have he : sourceProjection (z,r) = q := Prod.ext hzq (CircleConstruction.section_spec 6 q.2)
  rw [← he,logCusp_projection_apply a ha (z,r) (hab.trans_lt hz),logCusp_projection_apply b hb (z,r) hz]

def piecePosition (δ : ℝ) (i : Bool) : Piece → Cylinder :=
  if i then switch ∘ radial 4 ∘ logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap
  else radial (leftLength δ) ∘ logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap
lemma piecePosition_collar (δ : ℝ) (x : collar) :
    piecePosition δ false x.1 = leftPosition δ x ∧
    piecePosition δ true x.1 = rightPosition x := by
  have he := logCuspMap_change cuspLevel 2 cuspLevel_gt (by norm_num) cuspLevel_lt_two.le
    (q := pieceMap x.1) (show pieceMap x.1 ∈ wholeCusp 2 from x.2)
  constructor <;> dsimp [piecePosition,leftPosition,rightPosition,collarLog] <;> rw [he]
lemma piecePosition_match (δ : ℝ) (x : collar) :
    piecePosition δ false x.1 = piecePosition δ true (gluingMap x).1 := by
  rw [(piecePosition_collar δ x).1,(piecePosition_collar δ (gluingMap x)).2]
  exact (congrFun (position_match δ) x).symm

def neckPosition (δ : ℝ) : GluedConstruction.Manifold → Cylinder :=
  TwoGluing.descend collar gluingMap (piecePosition δ)
lemma neckPosition_inclusion (δ : ℝ) (i : Bool) (x : Piece) :
    neckPosition δ (inclusion i x) = piecePosition δ i x :=
  TwoGluing.descend_inclusion collar gluingMap _ (piecePosition_match δ) i x

def extendedPiece : Set Piece := {x | (1/2:ℝ) < HyperbolicCore.height x.1.1}
lemma extendedPiece_isOpen : IsOpen extendedPiece :=
  isOpen_lt continuous_const ((HyperbolicCore.height_continuous.comp continuous_subtype_val).comp continuous_fst)
lemma collar_subset_extended : (collar : Set Piece) ⊆ extendedPiece := by
  intro x hx
  have hh := (HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ)<2) x.1.1).mp hx
  exact RadialProfile.log_bounds.1.trans hh
lemma extendedPiece_cusp {x : Piece} (hx : x ∈ extendedPiece) : pieceMap x ∈ wholeCusp cuspLevel := by
  apply (HyperbolicCore.mem_cusp_iff_height cuspLevel_gt x.1.1).mpr
  rw [log_cuspLevel]
  change (1/2:ℝ) < HyperbolicCore.height x.1.1 at hx
  linarith

def extendedNeck : Set GluedConstruction.Manifold :=
  inclusion false '' extendedPiece ∪ inclusion true '' extendedPiece
lemma extendedNeck_isOpen : IsOpen extendedNeck :=
  ((TwoGluing.inclusion_openEmbedding collar gluingMap false).isOpenMap _ extendedPiece_isOpen).union
    ((TwoGluing.inclusion_openEmbedding collar gluingMap true).isOpenMap _ extendedPiece_isOpen)
lemma openNeck_subset_extended : openNeck ⊆ extendedNeck := by
  rintro p ⟨x,hx,rfl⟩
  exact Or.inl ⟨x,collar_subset_extended hx,rfl⟩
lemma extendedNeck_representative {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    ∃ i x, x ∈ extendedPiece ∧ inclusion i x = p := by
  rcases hp with ⟨x,hx,rfl⟩|⟨x,hx,rfl⟩
  · exact ⟨false,x,hx,rfl⟩
  · exact ⟨true,x,hx,rfl⟩
lemma neckPosition_germ (δ : ℝ) (i : Bool) {p : GluedConstruction.Manifold}
    (hp : p ∈ (pieceOpenMap i).target) :
    neckPosition δ =ᶠ[𝓝 p] piecePosition δ i ∘ (pieceOpenMap i).symm := by
  filter_upwards [(pieceOpenMap i).open_target.mem_nhds hp] with q hq
  calc neckPosition δ q = neckPosition δ (inclusion i ((pieceOpenMap i).symm q)) :=
        congrArg (neckPosition δ) ((pieceOpenMap i).right_inv hq).symm
    _ = _ := neckPosition_inclusion δ i _
lemma piecePosition_smooth {δ : ℝ} (i : Bool) {x : Piece} (hx : x ∈ extendedPiece) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (piecePosition δ i) x := by
  have hs := (logCuspMap_smoothAt cuspLevel cuspLevel_gt (extendedPiece_cusp hx)).comp x (pieceMap_smooth x)
  cases i
  · exact ((radial_smooth (leftLength δ)) _).comp x hs
  · exact (switch_smooth _).comp x (((radial_smooth 4) _).comp x hs)
lemma neckPosition_smooth (δ : ℝ) {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (neckPosition δ) p := by
  obtain ⟨i,x,hx,rfl⟩ := extendedNeck_representative hp
  have ht : inclusion i x ∈ (pieceOpenMap i).target := (pieceOpenMap i).map_source (mem_univ x)
  have hs : ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (piecePosition δ i) ((pieceOpenMap i).symm (inclusion i x)) := by
    rw [pieceOpenMap_inclusion]
    exact piecePosition_smooth i hx
  exact (hs.comp _ (pieceOpenMap_inverse_smooth i ht)).congr_of_eventuallyEq (neckPosition_germ δ i ht)
end

section
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
lemma pieceMetric_cusp (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
    (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
      pullInner (E := P) g projection x u v =
        u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)
    {x : Piece} (hx : x ∈ extendedPiece) :
    pullInner (E := EP) g (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap) x =
      (pieceMetric (wholeMetric g c hc low)).inner x := by
  rw [pull_composition _ ((pieceMap_smooth x).mdifferentiableAt (by simp))
    ((logCuspMap_smoothAt cuspLevel cuspLevel_gt (extendedPiece_cusp hx)).mdifferentiableAt (by simp)),
    ← cuspMetric_inner g cuspLevel cuspLevel_gt (extendedPiece_cusp hx),
    ← wholeMetric_cusp g c hc low (extendedPiece_cusp hx)]
  rfl
lemma piecePosition_metric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool)
    {x : Piece} (hx : x ∈ extendedPiece) :
    pullInner (E := EP) (neck hδ (period_pos δ)) (piecePosition δ i) x =
      (pieceMetrics hδ i).inner x := by
  have hs := (logCuspMap_smoothAt cuspLevel cuspLevel_gt (extendedPiece_cusp hx)).comp x (pieceMap_smooth x)
  cases i
  · change pullInner (E := EP) (neck hδ (period_pos δ))
      (radial (leftLength δ) ∘ (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap)) x = _
    rw [pull_composition _ (hs.mdifferentiableAt (by simp))
      ((radial_smooth (leftLength δ) _).mdifferentiableAt (by simp))]
    change pullBilin (E := EP) (F := P) ((leftCylinder hδ).inner _)
      (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,P) (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap) x) = _
    exact pieceMetric_cusp _ _ _ (leftCylinder_low hδ) hx
  · change pullInner (E := EP) (neck hδ (period_pos δ))
      (switch ∘ (radial 4 ∘ (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap))) x = _
    rw [pull_composition _ (((radial_smooth 4 _).comp x hs).mdifferentiableAt (by simp))
      ((switch_smooth _).mdifferentiableAt (by simp))]
    change pullInner (E := EP) (switched (neck hδ (period_pos δ)))
      (radial 4 ∘ (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap)) x = _
    rw [pull_composition _ (hs.mdifferentiableAt (by simp))
      ((radial_smooth 4 _).mdifferentiableAt (by simp))]
    change pullInner (E := EP) (rightCylinder hδ) (logCuspMap cuspLevel cuspLevel_gt ∘ pieceMap) x = _
    exact pieceMetric_cusp _ _ _ (rightCylinder_low hδ) hx

lemma neckPosition_metric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    pullInner (E := EP) (neck hδ (period_pos δ)) (neckPosition δ) p = (compactMetric hδ).inner p := by
  obtain ⟨i,x,hx,rfl⟩ := extendedNeck_representative hp
  apply bilin_eq_of_pull_eq (E := EP) (F := EP) x
    ((pieceOpenMap_mdifferentiable i).mfderiv_surjective (mem_univ x))
  have hd := pull_composition (neck hδ (period_pos δ))
    ((inclusion_smooth i x).mdifferentiableAt (by simp))
    ((neckPosition_smooth δ hp).mdifferentiableAt (by simp))
  have he : neckPosition δ ∘ inclusion i = piecePosition δ i := funext (neckPosition_inclusion δ i)
  exact hd.symm.trans ((congrArg (fun f => pullInner (E := EP) (neck hδ (period_pos δ)) f x) he).trans
    ((piecePosition_metric hδ i hx).trans (compactMetric_local hδ i x).symm))

local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

def neckPositionIsometry {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) :
    LocalMetricIsometry (realCompactMetric hδ) (realNeck hδ (period_pos δ)) (neckPosition δ) :=
  Rechart.realIsometry Coordinates3.coordinates coordinates _ _ _ extendedNeck extendedNeck_isOpen
    (fun _ hp => (neckPosition_smooth δ hp).contMDiffWithinAt) (fun _ hp => neckPosition_metric hδ hp)
end

open MetricConstruction CylinderConstruction GluedConstruction
lemma inclusion_mem_neck_iff (i : Bool) (x : Piece) : inclusion i x ∈ openNeck ↔ x ∈ collar := by
  constructor
  · rintro ⟨y,hy,he⟩
    cases i
    · exact (TwoGluing.inclusion_openEmbedding collar gluingMap false).injective he ▸ hy
    · obtain ⟨hy',hxy⟩ := (TwoGluing.inclusion_mixed_eq collar gluingMap y x).mp he
      exact hxy ▸ (gluingMap ⟨y,hy'⟩).2
  · exact inclusion_collar_mem_openNeck i

def interfaceBand : Set Piece := {x | Real.log 2 ≤ HyperbolicCore.height x.1.1 ∧
  HyperbolicCore.height x.1.1 ≤ Real.log 4}
lemma interfaceBand_compact : IsCompact interfaceBand := by
  have hc : IsClosed {x : Piece | Real.log 2 ≤ HyperbolicCore.height x.1.1} :=
    isClosed_le continuous_const ((HyperbolicCore.height_continuous.comp continuous_subtype_val).comp continuous_fst)
  convert halfCore_compact.inter_right hc using 1
  ext x
  simp [interfaceBand,halfCore,and_comm]
lemma interfaceBand_subset_extended : interfaceBand ⊆ extendedPiece :=
  fun _ hx => RadialProfile.log_bounds.1.trans_le hx.1
lemma openNeck_subset_bands : openNeck ⊆
    inclusion false '' interfaceBand ∪ inclusion true '' interfaceBand := by
  rintro p ⟨x,hx,rfl⟩
  rcases halfCore_covers x with hl | ⟨ho,hr⟩
  · exact Or.inl ⟨x,⟨((HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ)<2) x.1.1).mp hx).le,hl⟩,rfl⟩
  · exact Or.inr ⟨(gluingMap ⟨x,ho⟩).1,⟨((HyperbolicCore.mem_cusp_iff_height
      (by norm_num : (1:ℝ)<2) _).mp (gluingMap ⟨x,ho⟩).2).le,hr⟩,
      (TwoGluing.inclusion_transition collar gluingMap ⟨x,ho⟩).symm⟩
lemma closure_openNeck_subset_extended : closure openNeck ⊆ extendedNeck := by
  have hc : IsClosed (inclusion false '' interfaceBand ∪ inclusion true '' interfaceBand) :=
    ((interfaceBand_compact.image (TwoGluing.inclusion_openEmbedding collar gluingMap false).continuous).isClosed).union
      ((interfaceBand_compact.image (TwoGluing.inclusion_openEmbedding collar gluingMap true).continuous).isClosed)
  exact (closure_minimal openNeck_subset_bands hc).trans (by
    rintro p (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)
    · exact Or.inl ⟨x,interfaceBand_subset_extended hx,rfl⟩
    · exact Or.inr ⟨x,interfaceBand_subset_extended hx,rfl⟩)

lemma piecePosition_height (δ : ℝ) (i : Bool) {x : Piece} (hx : x ∈ extendedPiece) :
    (piecePosition δ i x).1 =
      if i then 1 - (HyperbolicCore.height x.1.1 - Real.log 2)/Real.log 4
      else (HyperbolicCore.height x.1.1 - Real.log 2)/Real.log 4 := by
  have hh : (logCuspMap cuspLevel cuspLevel_gt (pieceMap x)).1 = HyperbolicCore.height x.1.1 :=
    wholeCuspLog_height cuspLevel_gt (extendedPiece_cusp hx)
  have hx' : 1/2 ≤ HyperbolicCore.height x.1.1 := le_of_lt hx
  cases i
  · change RadialProfile.coordinate (leftLength δ) (logCuspMap cuspLevel cuspLevel_gt (pieceMap x)).1 = _
    simp only [hh,RadialProfile.coordinate_right hx',Bool.false_eq_true,ite_false]
  · change 1-RadialProfile.coordinate 4 (logCuspMap cuspLevel cuspLevel_gt (pieceMap x)).1 = _
    simp only [hh,RadialProfile.coordinate_right hx',ite_true]
lemma log_eight : Real.log (8:ℝ) = Real.log 2 + Real.log 4 := by
  rw [← Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (4:ℝ)≠0)]
  norm_num
lemma neckPosition_mem_iff (δ : ℝ) {p : GluedConstruction.Manifold} (hp : p ∈ extendedNeck) :
    (neckPosition δ p).1 ∈ Ioo (0:ℝ) 1 ↔ p ∈ openNeck := by
  obtain ⟨i,x,hx,rfl⟩ := extendedNeck_representative hp
  rw [neckPosition_inclusion,piecePosition_height δ i hx,inclusion_mem_neck_iff]
  have hu : HyperbolicCore.height x.1.1 < Real.log 2 + Real.log 4 :=
    lt_of_lt_of_eq x.1.2 log_eight
  have hd : 0 < Real.log 4 := lt_trans (by norm_num) RadialProfile.log_bounds.2.1
  have hh : x ∈ collar ↔ Real.log 2 < HyperbolicCore.height x.1.1 :=
    HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ)<2) x.1.1
  rw [hh]
  cases i <;> simp only [Bool.false_eq_true,ite_false,ite_true,mem_Ioo]
  · constructor
    · intro h
      exact sub_pos.mp ((div_pos_iff_of_pos_right hd).mp h.1)
    · intro h
      exact ⟨div_pos (sub_pos.mpr h) hd,(div_lt_one hd).mpr (by linarith)⟩
  · constructor
    · intro h
      have hh' : 0 < (HyperbolicCore.height x.1.1 - Real.log 2)/Real.log 4 := by linarith
      exact sub_pos.mp ((div_pos_iff_of_pos_right hd).mp hh')
    · intro h
      have h1 := div_pos (sub_pos.mpr h) hd
      have h2 := (div_lt_one hd).mpr (show HyperbolicCore.height x.1.1 - Real.log 2 < Real.log 4 by linarith)
      constructor <;> linarith
end ThreeManifold.CompactMetric

namespace ThreeManifold.CylinderConstruction

section
open QuotientConstruction

lemma lift_smoothAt {f : ℝ → Cylinder} {F : ℝ → P} {s : ℝ}
    (hf : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,P) ∞ f s) (hF : ContinuousAt F s)
    (he : (projection ∘ F) =ᶠ[nhds s] f) : ContDiffAt ℝ ∞ F s := by
  let l := projection_cover.isCoveringMap.isLocalHomeomorph
  let e := l.localInverseAt (F s)
  have hes : f s ∈ e.source := by
    rw [← he.eq_of_nhds]
    exact l.apply_self_mem_localInverseAt_source
  have hsm := (local_inverse_smooth (F s) hes).comp s hf
  apply contMDiffAt_iff_contDiffAt.mp
  apply hsm.congr_of_eventuallyEq
  apply lifts_eventuallyEq l hF hsm.continuousAt
  · change F s = e (f s)
    rw [← he.eq_of_nhds]
    exact l.localInverseAt_apply_self.symm
  · have hne : ∀ᶠ t in nhds s, f t ∈ e.source :=
      hf.continuousAt (e.open_source.mem_nhds hes)
    filter_upwards [he,hne] with t ht ht'
    exact ht.trans (l.apply_localInverseAt_of_mem ht').symm

theorem exists_smooth_lift {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hUn : U.Nonempty) {f : ℝ → Cylinder}
    (hf : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,P) ∞ f U) :
    ∃ F : ℝ → P, ContDiffOn ℝ ∞ F U ∧ ∀ s ∈ U, projection (F s) = f s := by
  classical
  let : ContractibleSpace U := (convex_iff_ordConnected.mpr hUc).contractibleSpace hUn
  let : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  obtain ⟨s,hs⟩ := hUn
  let fU : C(U,Cylinder) := ⟨fun x => f x,continuousOn_iff_continuous_domRestrict.mp hf.continuousOn⟩
  obtain ⟨G,hG,-⟩ := projection_cover.isCoveringMap.existsUnique_continuousMap_lifts
    fU ⟨s,hs⟩ (sectionMap (f s)) (section_spec (f s))
  let F : ℝ → P := fun t => if ht : t ∈ U then G ⟨t,ht⟩ else 0
  have hF : ContinuousOn F U := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert G.continuous using 1
    funext t
    exact dite_eq_left t.2
  have hFe : ∀ t ∈ U, projection (F t) = f t := by
    intro t ht
    dsimp only [F]
    rw [dite_eq_left ht]
    exact congr_fun hG.2 ⟨t,ht⟩
  refine ⟨F,fun t ht => ?_,hFe⟩
  apply (lift_smoothAt (hf.contMDiffAt (hU.mem_nhds ht))
    (hF.continuousAt (hU.mem_nhds ht)) ?_).contDiffWithinAt
  filter_upwards [hU.mem_nhds ht] with x hx
  exact hFe x hx

end

local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates
lemma exists_euclidean_smooth_lift {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hUn : U.Nonempty) {f : ℝ → Cylinder}
    (hf : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ f U) :
    ∃ F : ℝ → E3, ContDiffOn ℝ ∞ F U ∧ ∀ s ∈ U, euclideanProjection (F s) = f s := by
  have hfn : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,P) ∞ f U := by
    intro s hs
    exact (((Rechart.identity_smooth_backward coordinates) (f s)).comp s
      (hf.contMDiffAt (hU.mem_nhds hs))).contMDiffWithinAt
  obtain ⟨F,hF,he⟩ := exists_smooth_lift hU hUc hUn hfn
  refine ⟨coordinates ∘ F,coordinates.contDiff.comp_contDiffOn hF,?_⟩
  intro s hs
  simpa only [euclideanProjection,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using he s hs
end ThreeManifold.CylinderConstruction
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction RiemannianCoordinates Cometric Neck

def normalizedNeck {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric E3 :=
  euclideanMetric (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)
    ((Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩).comp (contDiff_const.sub contDiff_id))
    ((contDiff_const (c := δ^2)).mul χ_smooth)
    (fun t => (Collar.ell_pos δ t).ne') (fun t => (Collar.ell_pos δ (1-t)).ne')

lemma normalizedNeck_apply {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (x u v : E3) :
    (normalizedNeck hδ).inner x u v = u 0*v 0 + (Collar.ell δ (x 0))^2 *
      (u 1-δ^2*χ (x 0)*u 2)*(v 1-δ^2*χ (x 0)*v 2) +
      (Collar.ell δ (1-x 0))^2*u 2*v 2 := by
  unfold normalizedNeck euclideanMetric
  apply triangularMetric_apply

def normalize (δ B : ℝ) : E3 →L[ℝ] E3 :=
  { toFun := fun x => ![x 0,δ^2*B/6*x 1,B/6*x 2]
    map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
    map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring }

def normalizationIsometry {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) :
    LocalMetricIsometry (neckModel hδ hB) (normalizedNeck hδ) (normalize δ B) where
  domain := univ
  isOpen_domain := isOpen_univ
  smooth := (normalize δ B).contDiff.contMDiff.contMDiffOn
  metric := by
    intro x _ u v
    rw [mfderiv_eq_fderiv,(normalize δ B).hasFDerivAt.fderiv]
    change (neckModel hδ hB).inner x (show E3 from u) (show E3 from v) =
      (normalizedNeck hδ).inner (normalize δ B x) (normalize δ B u) (normalize δ B v)
    rw [neckModel_apply,normalizedNeck_apply]
    simp only [normalize,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,radius₁,radius₂]
    ring

lemma ell_sq_eq_inv {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : -1/4 < t) :
    (Collar.ell δ t)^2 = 1 / d₁ δ t := by
  have hd : d₁ δ t ≠ 0 := (Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)).ne'
  exact (eq_div_iff hd).mpr (Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ ht)
lemma normalizedNeck_bilin {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) (u v : E3) :
    (normalizedNeck hδ).inner x u v = Neck.metric (Q δ (x 0)) (splitVector u) (splitVector v) := by
  have ht2 : -1/4 < 1-x 0 := by linarith [hx.2]
  have h1 : d₁ δ (x 0) ≠ 0 := (Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith [hx.1] : -1 ≤ x 0)).ne'
  have h2 : d₂ δ (x 0) ≠ 0 := (Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith [hx.2] : -1 ≤ 1-x 0)).ne'
  rw [normalizedNeck_apply,ell_sq_eq_inv hδ hx.1,ell_sq_eq_inv hδ ht2,
    LocalNeck.Q_formula_of_ne h1 h2]
  simp only [Neck.metric,splitVector,Neck.pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,d₂,d₁,shear]
  ring
lemma normalizedNeck_matrix {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) :
    metricMatrix (normalizedNeck hδ) (OpenPartialHomeomorph.refl E3) x = blockMatrix (Q δ (x 0)) := by
  ext i j
  change (normalizedNeck hδ).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change (normalizedNeck hδ).inner x (basisVector i) (basisVector j) = _
  rw [normalizedNeck_bilin hδ hx]
  fin_cases i <;> fin_cases j <;>
    simp [Neck.metric,splitVector,Neck.pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,basisVector,blockMatrix]
lemma normalizedNeck_matrix_germ {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) :
    metricMatrix (normalizedNeck hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[nhds x]
      fun y => blockMatrix (Q δ (y 0)) := by
  have hx' : x 0 ∈ Ioo (-1/4:ℝ) (5/4) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  filter_upwards [(continuous_apply 0).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx')] with y hy
  exact normalizedNeck_matrix hδ hy
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)
lemma deriv_invertible {p : M} (hp : p ∈ P.domain) : (mfderiv I3 I3 f p).IsInvertible := by
  change (show E3 →L[ℝ] E3 from mfderiv I3 I3 f p).IsInvertible
  refine ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr (P.deriv_injective hp))
    (LinearMap.range_eq_top.mpr (P.deriv_bijective hp).2),?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

def unmapField (_P : LocalMetricIsometry g h f) (γ : ℝ → M)
    (J : ∀ s, TangentSpace I3 ((f ∘ γ) s)) : ∀ s, TangentSpace I3 (γ s) :=
  fun s => (mfderiv I3 I3 f (γ s)).inverse (J s)
lemma map_unmap {γ : ℝ → M} (J : ∀ s, TangentSpace I3 ((f ∘ γ) s))
    {s : ℝ} (hs : γ s ∈ P.domain) : P.mapField γ (P.unmapField γ J) s = J s :=
  (P.deriv_invertible hs).self_apply_inverse _
lemma coordinate_invertible {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {x : E3}
    (hx : x ∈ P.coordinateDomain c d) : (fderiv ℝ (d ∘ f ∘ c.symm) x).IsInvertible := by
  have hs := P.coordinate_surjective hc hd hx
  have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) rfl).mpr hs
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs),ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
lemma unmapField_coordinates {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 ((f ∘ γ) s)) {s : ℝ}
    (hp : γ s ∈ P.domain) (hpc : γ s ∈ c.source) (hpd : f (γ s) ∈ d.source) :
    fieldCoordinates γ (P.unmapField γ J) c s =
      (fderiv ℝ (d ∘ f ∘ c.symm) (c (γ s))).inverse (fieldCoordinates (f ∘ γ) J d s) := by
  have he := P.mapField_coordinates hc hd (P.unmapField γ J) hp hpc hpd
  have hi := P.coordinate_invertible hc hd (P.coordinateDomain_mem hp hpc hpd)
  apply Eq.symm
  apply hi.inverse_apply_eq.mpr
  rw [← he]
  exact congrArg (mfderiv I3 I3 d (f (γ s))) (P.map_unmap J hp).symm
lemma unmapField_smooth {γ : ℝ → M} {J : ∀ s, TangentSpace I3 ((f ∘ γ) s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn (f ∘ γ) J U) : SmoothFieldOn γ (P.unmapField γ J) U := by
  intro c hc s hs
  let d := chartAt E3 (f (γ s))
  have hd := chart_mem_atlas E3 (f (γ s))
  have hsd := mem_chart_source E3 (f (γ s))
  have hp := hγP hs.1
  have hx := P.coordinateDomain_mem hp hs.2 hsd
  have hh := P.coordinate_smoothAt hc hd hx
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  have hb := ((P.coordinate_invertible hc hd hx).contDiffAt_map_inverse.comp (c (γ s))
    (hh.fderiv_right (m := ∞) (by simp))).comp s (curve_coordinates_smoothAt hU hγ hc hs.1 hs.2)
  have he : fieldCoordinates γ (P.unmapField γ J) c =ᶠ[𝓝 s]
      (fun r => (fderiv ℝ (d ∘ f ∘ c.symm) (c (γ r))).inverse (fieldCoordinates (f ∘ γ) J d r)) := by
    filter_upwards [hU.mem_nhds hs.1,
      (hγ.contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hs.2),
      ((P.comp_smooth hU hγ hγP).contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hsd)] with r hr hrc hrd
    exact P.unmapField_coordinates hc hd J (hγP hr) hrc hrd
  exact ((hb.clm_apply (smoothField_coordinatesAt hU (P.comp_smooth hU hγ hγP) hJ hd hs.1 hsd)).congr_of_eventuallyEq he).contDiffWithinAt
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

namespace ThreeManifold.RiemannianCoordinates
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
omit [IsManifold I3 ∞ M] in
lemma fieldCoordinates_germ {γ η : ℝ → M} {J K : ℝ → E3} {s : ℝ}
    (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) (c : OpenPartialHomeomorph M E3) :
    fieldCoordinates γ J c =ᶠ[nhds s] fieldCoordinates η K c := by
  let A : M → E3 →L[ℝ] E3 := fun p => mfderiv I3 I3 c p
  change (fun r => A (γ r) (J r)) =ᶠ[nhds s] (fun r => A (η r) (K r))
  filter_upwards [hc,hJ] with r hr hr'
  rw [hr,hr']
lemma covariantDerivative_curve_germ (g : SmoothMetric M) {γ η : ℝ → M}
    {J K : ℝ → E3} {s : ℝ} (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) :
    covariantDerivative g γ J s = covariantDerivative g η K s := by
  let C : M → OpenPartialHomeomorph M E3 := chartAt E3
  let A : M → E3 →L[ℝ] E3 := fun p => mfderiv I3 I3 (C p).symm ((C p) p)
  change A (γ s) (alongDerivative g (C (γ s)) ((C (γ s)) ∘ γ) (fieldCoordinates γ J (C (γ s))) s) =
    A (η s) (alongDerivative g (C (η s)) ((C (η s)) ∘ η) (fieldCoordinates η K (C (η s))) s)
  rw [hc.eq_of_nhds]
  exact congrArg (A (η s)) (along_congr g _ (hc.fun_comp _) (fieldCoordinates_germ hc hJ _))
lemma curvatureAlong_curve_germ (g : SmoothMetric M) {γ η : ℝ → M}
    {J K : ℝ → E3} {s : ℝ} (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) :
    curvatureAlong g γ J s = curvatureAlong g η K s := by
  let C : M → OpenPartialHomeomorph M E3 := chartAt E3
  let A : M → E3 →L[ℝ] E3 := fun p => mfderiv I3 I3 (C p).symm ((C p) p)
  change A (γ s) (curvatureTerm g (C (γ s)) ((C (γ s)) (γ s))
    (fieldCoordinates γ J (C (γ s)) s) (deriv ((C (γ s)) ∘ γ) s) (deriv ((C (γ s)) ∘ γ) s)) =
    A (η s) (curvatureTerm g (C (η s)) ((C (η s)) (η s))
    (fieldCoordinates η K (C (η s)) s) (deriv ((C (η s)) ∘ η) s) (deriv ((C (η s)) ∘ η) s))
  rw [hc.eq_of_nhds,(fieldCoordinates_germ hc hJ _).eq_of_nhds,(hc.fun_comp (C (η s))).deriv_eq]
lemma indexPairDensity_curve_germ (g : SmoothMetric M) {γ η : ℝ → M}
    {J K : ℝ → E3} {s : ℝ} (hc : γ =ᶠ[nhds s] η) (hJ : J =ᶠ[nhds s] K) :
    indexPairDensity g γ J J s = indexPairDensity g η K K s := by
  let B : M → E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner
  change B (γ s) (covariantDerivative g γ J s) (covariantDerivative g γ J s) -
    B (γ s) (curvatureAlong g γ J s) (J s) =
    B (η s) (covariantDerivative g η K s) (covariantDerivative g η K s) -
    B (η s) (curvatureAlong g η K s) (K s)
  rw [hc.eq_of_nhds,hJ.eq_of_nhds,covariantDerivative_curve_germ g hc hJ,
    curvatureAlong_curve_germ g hc hJ]
lemma smoothField_curve_congrOn {γ η : ℝ → M} {J K : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hc : EqOn γ η U) (hJK : EqOn J K U) (hJ : SmoothFieldOn γ J U) : SmoothFieldOn η K U := by
  intro c hca s hs
  have hsγ : γ s ∈ c.source := by rw [hc hs.1]; exact hs.2
  have hcg : γ =ᶠ[nhds s] η := Filter.eventually_of_mem (hU.mem_nhds hs.1) (fun r hr => hc hr)
  have hfg : J =ᶠ[nhds s] K := Filter.eventually_of_mem (hU.mem_nhds hs.1) (fun r hr => hJK hr)
  exact ((smoothField_coordinatesAt hU hγ hJ hca hs.1 hsγ).congr_of_eventuallyEq
    (fieldCoordinates_germ hcg hfg c).symm).contDiffWithinAt
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

theorem actual_neck_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) (hUc : OrdConnected U) (hUn : U.Nonempty)
    {γ : ℝ → GluedConstruction.Manifold} (hγ : IsGeodesicOn (realCompactMetric hδ) γ U)
    (hγe : MapsTo γ U extendedNeck) {J : ℝ → E3} (hJ : SmoothFieldOn γ J U) :
    ∃ (η V : ℝ → E3), IsGeodesicOn (normalizedNeck hδ) η U ∧ SmoothFieldOn η V U ∧
      (∀ s ∈ U, η s 0 = (neckPosition δ (γ s)).1) ∧
      (∀ s ∈ U, indexPairDensity (normalizedNeck hδ) η V V s =
        indexPairDensity (realCompactMetric hδ) γ J J s) ∧
      (∀ s ∈ U, J s = 0 → V s = 0) := by
  let P := neckPositionIsometry hδ
  let R := neckProjectionIsometry hδ (period_pos δ)
  let T := normalizationIsometry hδ (period_pos δ)
  let β := neckPosition δ ∘ γ
  have hβ := P.geodesic_map hU hγ hγe
  obtain ⟨F,hF,he⟩ := exists_euclidean_smooth_lift hU hUc hUn hβ.1
  have hFm : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ F U := contMDiffOn_iff_contDiffOn.mpr hF
  have hFR : MapsTo F U R.domain := fun _ _ => mem_univ _
  have hFg : IsGeodesicOn (neckModel hδ (period_pos δ)) F U :=
    R.geodesic_reflect hU hFm hFR (geodesic_congrOn _ hU (fun s hs => (he s hs).symm) hβ)
  let K := P.mapField γ J
  have hK : SmoothFieldOn β K U := P.mapField_smooth hU hγ.1 hγe hJ
  have hK' : SmoothFieldOn (euclideanProjection ∘ F) K U :=
    smoothField_curve_congrOn hU hβ.1 (fun s hs => (he s hs).symm) (fun _ _ => rfl) hK
  let W := R.unmapField F K
  have hW : SmoothFieldOn F W U := R.unmapField_smooth hU hFm hFR hK'
  have hFT : MapsTo F U T.domain := fun _ _ => mem_univ _
  refine ⟨normalize δ (period δ) ∘ F,T.mapField F W,T.geodesic_map hU hFg hFT,
    T.mapField_smooth hU hFm hFT hW,?_,?_,?_⟩
  · intro s hs
    exact congrArg Prod.fst (he s hs)
  · intro s hs
    rw [T.indexPairDensity_map hU hFm hFT hW hW hs,
      ← R.indexPairDensity_map hU hFm hFR hW hW hs]
    have hc : (euclideanProjection ∘ F) =ᶠ[nhds s] β :=
      Filter.eventually_of_mem (hU.mem_nhds hs) (fun r hr => he r hr)
    have hf : R.mapField F W =ᶠ[nhds s] K :=
      Filter.eventually_of_mem (hU.mem_nhds hs) (fun r hr => R.map_unmap K (hFR hr))
    rw [indexPairDensity_curve_germ _ hc hf]
    exact P.indexPairDensity_map hU hγ.1 hγe hJ hJ hs
  · intro s _ hs
    have hK0 : K s = 0 := by
      exact (congrArg (mfderiv I3 I3 (neckPosition δ) (γ s)) hs).trans
        ((mfderiv I3 I3 (neckPosition δ) (γ s)).map_zero)
    have hW0 : W s = 0 := by
      exact (congrArg (mfderiv I3 I3 euclideanProjection (F s)).inverse hK0).trans
        ((mfderiv I3 I3 euclideanProjection (F s)).inverse.map_zero)
    exact (congrArg (mfderiv I3 I3 (normalize δ (period δ)) (F s)) hW0).trans
      ((mfderiv I3 I3 (normalize δ (period δ)) (F s)).map_zero)
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.FinitePassage

lemma bounded_open_interval {S : Set ℝ} (hS : IsOpen S) (hc : IsConnected S)
    (hb : BddBelow S) (ha : BddAbove S) :
    S = Ioo (sInf S) (sSup S) := by
  apply Subset.antisymm _ (hc.Ioo_csInf_csSup_subset hb ha)
  intro x hx
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
  have hl : x-ε/2 ∈ S := by
    apply he
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hr : x+ε/2 ∈ S := by
    apply he
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  exact ⟨lt_of_le_of_lt (csInf_le hb hl) (by linarith),
    lt_of_lt_of_le (by linarith) (le_csSup ha hr)⟩

lemma closure_component_boundary {P : Set ℝ} (hP : IsOpen P) {x y : ℝ}
    (hy : y ∈ closure (connectedComponentIn P x))
    (hyn : y ∉ connectedComponentIn P x) : y ∉ P := by
  intro hyp
  have hn : connectedComponentIn P y ∈ nhds y :=
    hP.connectedComponentIn.mem_nhds (mem_connectedComponentIn hyp)
  obtain ⟨z,hzy,hzx⟩ := (mem_closure_iff_nhds.mp hy) _ hn
  have he : connectedComponentIn P x = connectedComponentIn P y :=
    (connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm
  exact hyn (he ▸ mem_connectedComponentIn hyp)

theorem bounded_component {P : Set ℝ} (hP : IsOpen P) {A B x : ℝ}
    (hPB : P ⊆ Ioo A B) (hx : x ∈ P) :
    ∃ a b : ℝ, a < b ∧ A ≤ a ∧ b ≤ B ∧
      connectedComponentIn P x = Ioo a b ∧ a ∉ P ∧ b ∉ P := by
  let S := connectedComponentIn P x
  have hn : S.Nonempty := connectedComponentIn_nonempty_iff.mpr hx
  have hs : S ⊆ Ioo A B := (connectedComponentIn_subset P x).trans hPB
  have hb : BddBelow S := ⟨A,fun y hy => (hs hy).1.le⟩
  have ha : BddAbove S := ⟨B,fun y hy => (hs hy).2.le⟩
  have he : S = Ioo (sInf S) (sSup S) :=
    bounded_open_interval hP.connectedComponentIn (isConnected_connectedComponentIn_iff.mpr hx) hb ha
  have hab : sInf S < sSup S := nonempty_Ioo.mp (he ▸ hn)
  have hcl : closure S = Icc (sInf S) (sSup S) := by
    conv_lhs => rw [he]
    rw [closure_Ioo hab.ne]
  refine ⟨sInf S,sSup S,hab,le_csInf hn (fun y hy => (hs hy).1.le),
    csSup_le hn (fun y hy => (hs hy).2.le),he,?_,?_⟩
  · apply closure_component_boundary hP
    · change sInf S ∈ closure S
      apply hcl.symm.subset
      exact ⟨le_rfl,hab.le⟩
    · change sInf S ∉ S
      intro hi
      have hi' := he.subset hi
      exact (lt_irrefl _) hi'.1
  · apply closure_component_boundary hP
    · change sSup S ∈ closure S
      apply hcl.symm.subset
      exact ⟨hab.le,le_rfl⟩
    · change sSup S ∉ S
      intro hi
      have hi' := he.subset hi
      exact (lt_irrefl _) hi'.2

lemma endpoint_alternative {M : Type*} [TopologicalSpace M] {O : Set M}
    {γ : ℝ → M} {A B a b : ℝ} (hab : a < b) (hAa : A ≤ a) (hbB : b ≤ B)
    (hr : ∀ s ∈ Ioo a b, γ s ∈ O)
    (hc : ContinuousOn γ (Icc A B))
    (ha : a ∉ Ioo A B ∩ γ ⁻¹' O) (hb : b ∉ Ioo A B ∩ γ ⁻¹' O) :
    (a = A ∨ γ a ∈ closure O \ O) ∧ (b = B ∨ γ b ∈ closure O \ O) := by
  have hcore : Icc a b ⊆ Icc A B := Icc_subset_Icc hAa hbB
  have hmem : ∀ s ∈ Icc a b, γ s ∈ closure O := by
    have hsc : ContinuousOn γ (closure (Ioo a b)) := by
      rw [closure_Ioo hab.ne]
      exact hc.mono hcore
    have hh := (show MapsTo γ (Ioo a b) O from hr).closure_of_continuousOn hsc
    rw [closure_Ioo hab.ne] at hh
    exact hh
  constructor
  · by_cases he : a = A
    · exact Or.inl he
    · right
      refine ⟨hmem a ⟨le_rfl,hab.le⟩,fun hao => ha ⟨?_,hao⟩⟩
      exact ⟨lt_of_le_of_ne hAa (Ne.symm he),hab.trans_le hbB⟩
  · by_cases he : b = B
    · exact Or.inl he
    · right
      refine ⟨hmem b ⟨hab.le,le_rfl⟩,fun hbo => hb ⟨?_,hbo⟩⟩
      exact ⟨hAa.trans_lt hab,lt_of_le_of_ne hbB he⟩
end ThreeManifold.FinitePassage
end

section
open Set Filter Topology Bundle Manifold IsManifold
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates
local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

lemma finite_neck_neighborhood {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck) :
    ∃ W : Set ℝ, IsOpen W ∧ OrdConnected W ∧ Icc a b ⊆ W ∧ W ⊆ U ∧
      MapsTo γ W extendedNeck := by
  have hc : MapsTo γ (Icc a b) (closure openNeck) := by
    have hh := (show MapsTo γ (Ioo a b) openNeck from hr).closure_of_continuousOn (by
      rw [closure_Ioo hab.ne]
      exact hγ.1.continuousOn.mono hsub)
    rwa [closure_Ioo hab.ne] at hh
  let P := U ∩ γ ⁻¹' extendedNeck
  have hp : IsOpen P := hγ.1.continuousOn.isOpen_inter_preimage hU extendedNeck_isOpen
  have hcc : Icc a b ⊆ P := fun s hs => ⟨hsub hs,closure_openNeck_subset_extended (hc hs)⟩
  let W := connectedComponentIn P a
  have hW : IsOpen W := hp.connectedComponentIn
  have hcW : IsPreconnected W := isPreconnected_connectedComponentIn
  refine ⟨W,hW,hcW.ordConnected,?_,?_,?_⟩
  · exact isPreconnected_Icc.subset_connectedComponentIn ⟨le_rfl,hab.le⟩ hcc
  · exact (connectedComponentIn_subset P a).trans inter_subset_left
  · exact fun s hs => (connectedComponentIn_subset P a hs).2

lemma finite_neck_height_boundary {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck) :
    (∀ s ∈ Icc a b, (neckPosition δ (γ s)).1 ∈ Icc (0:ℝ) 1) ∧
    (γ a ∉ openNeck → (neckPosition δ (γ a)).1 = 0 ∨ (neckPosition δ (γ a)).1 = 1) ∧
    (γ b ∉ openNeck → (neckPosition δ (γ b)).1 = 0 ∨ (neckPosition δ (γ b)).1 = 1) := by
  obtain ⟨W,hW,_,hcc,hWU,hWe⟩ := finite_neck_neighborhood hδ hU hγ hab hsub hr
  have hpos : MapsTo (fun s => (neckPosition δ (γ s)).1) (Ioo a b) (Ioo (0:ℝ) 1) :=
    fun s hs => (neckPosition_mem_iff δ (hWe (hcc (Ioo_subset_Icc_self hs)))).mpr (hr s hs)
  have hcont : ContinuousOn (fun s => (neckPosition δ (γ s)).1) (closure (Ioo a b)) := by
    rw [closure_Ioo hab.ne]
    intro s hs
    exact ((continuous_fst.continuousAt.comp ((neckPosition_smooth δ
      (hWe (hcc hs))).continuousAt.comp (hγ.1.contMDiffAt (hU.mem_nhds (hsub hs))).continuousAt))).continuousWithinAt
  have hc := hpos.closure_of_continuousOn hcont
  rw [closure_Ioo hab.ne,closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hc
  have he (s : ℝ) (hs : s ∈ Icc a b) (hn : γ s ∉ openNeck) :
      (neckPosition δ (γ s)).1 = 0 ∨ (neckPosition δ (γ s)).1 = 1 := by
    have hn' : (neckPosition δ (γ s)).1 ∉ Ioo (0:ℝ) 1 :=
      fun hh => hn ((neckPosition_mem_iff δ (hWe (hcc hs))).mp hh)
    have hcs := hc hs
    simp only [mem_Ioo,not_and_or,not_lt] at hn'
    rcases hn' with hl | hr
    · exact Or.inl (le_antisymm hl hcs.1)
    · exact Or.inr (le_antisymm hcs.2 hr)
  exact ⟨fun s hs => hc hs,he a ⟨le_rfl,hab.le⟩,he b ⟨hab.le,le_rfl⟩⟩

theorem actual_finite_neck_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ : ℝ → GluedConstruction.Manifold}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) {a b : ℝ} (hab : a < b)
    (hsub : Icc a b ⊆ U) (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck)
    {J : ℝ → E3} (hJ : SmoothFieldOn γ J U) :
    ∃ (W : Set ℝ) (η V : ℝ → E3), IsOpen W ∧ OrdConnected W ∧
      Icc a b ⊆ W ∧ W ⊆ U ∧ IsGeodesicOn (normalizedNeck hδ) η W ∧ SmoothFieldOn η V W ∧
      (∀ s ∈ W, η s 0 = (neckPosition δ (γ s)).1) ∧
      (∀ s ∈ W, indexPairDensity (normalizedNeck hδ) η V V s =
        indexPairDensity (realCompactMetric hδ) γ J J s) ∧ (∀ s ∈ W, J s = 0 → V s = 0) := by
  obtain ⟨W,hW,hWc,hcc,hWU,hWe⟩ := finite_neck_neighborhood hδ hU hγ hab hsub hr
  have hγW : IsGeodesicOn (realCompactMetric hδ) γ W := ⟨hγ.1.mono hWU,fun c hc s hs hsc => hγ.2 c hc s (hWU hs) hsc⟩
  obtain ⟨η,V,hη,hV,hh,hi,hz⟩ := actual_neck_lift hδ hW hWc
    ⟨a,hcc ⟨le_rfl,hab.le⟩⟩ hγW hWe (fun c hc => (hJ c hc).mono (inter_subset_inter_left _ hWU))
  exact ⟨W,η,V,hW,hWc,hcc,hWU,hη,hV,hh,hi,hz⟩
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.PassageDynamics

def reflectEven (c : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := if s ≤ c then f s else f (2*c-s)
def reflectOdd (c : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ := if s ≤ c then f s else -f (2*c-s)

lemma scalar_reflection_germ {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {c : ℝ} (hc : c ∈ U)
    (ht : ∀ s ∈ U, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ U, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0) :
    (fun s => t (2*c-s)) =ᶠ[nhds c] t ∧ (fun s => -v (2*c-s)) =ᶠ[nhds c] v := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hc)
  have hcc : Icc (c-ε/2) (c+ε/2) ⊆ U := by
    intro s hs
    apply hsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hs.1,hs.2]
  have hr := scalar_reflection hF (show c ∈ Ioo (c-ε/2) (c+ε/2) from ⟨by linarith,by linarith⟩)
    (show (c-ε/2)+(c+ε/2)=2*c by ring)
    (fun s hs => ht s (hcc hs)) (fun s hs => hv s (hcc hs)) hvc
  have hn : Ioo (c-ε/2) (c+ε/2) ∈ nhds c := isOpen_Ioo.mem_nhds ⟨by linarith,by linarith⟩
  constructor
  · filter_upwards [hn] with s hs
    exact (hr s (Ioo_subset_Icc_self hs)).1
  · filter_upwards [hn] with s hs
    rw [(hr s (Ioo_subset_Icc_self hs)).2,neg_neg]

lemma reflectEven_germ_center {f : ℝ → ℝ} {c : ℝ}
    (he : (fun s => f (2*c-s)) =ᶠ[nhds c] f) : reflectEven c f =ᶠ[nhds c] f := by
  filter_upwards [he] with s hs
  simp only [reflectEven]
  split_ifs <;> first | rfl | assumption
lemma reflectOdd_germ_center {f : ℝ → ℝ} {c : ℝ}
    (he : (fun s => -f (2*c-s)) =ᶠ[nhds c] f) : reflectOdd c f =ᶠ[nhds c] f := by
  filter_upwards [he] with s hs
  simp only [reflectOdd]
  split_ifs <;> first | rfl | assumption

lemma reflectEven_germ_left (f : ℝ → ℝ) {c s : ℝ} (hs : s < c) :
    reflectEven c f =ᶠ[nhds s] f := by
  filter_upwards [eventually_lt_nhds hs] with r hr
  exact ite_eq_left hr.le
lemma reflectOdd_germ_left (f : ℝ → ℝ) {c s : ℝ} (hs : s < c) :
    reflectOdd c f =ᶠ[nhds s] f := by
  filter_upwards [eventually_lt_nhds hs] with r hr
  exact ite_eq_left hr.le
lemma reflectEven_germ_right (f : ℝ → ℝ) {c s : ℝ} (hs : c < s) :
    reflectEven c f =ᶠ[nhds s] (fun r => f (2*c-r)) := by
  filter_upwards [eventually_gt_nhds hs] with r hr
  exact ite_eq_right (not_le.mpr hr)
lemma reflectOdd_germ_right (f : ℝ → ℝ) {c s : ℝ} (hs : c < s) :
    reflectOdd c f =ᶠ[nhds s] (fun r => -f (2*c-r)) := by
  filter_upwards [eventually_gt_nhds hs] with r hr
  exact ite_eq_right (not_le.mpr hr)

lemma reflected_scalar_equations {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ U)
    (ht : ∀ s ∈ U, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ U, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0) :
    ∀ s ∈ Icc a (2*c-a),
      HasDerivAt (reflectEven c t) (reflectOdd c v s) s ∧
      HasDerivAt (reflectOdd c v) (-F (reflectEven c t s)/2) s := by
  have hcg := scalar_reflection_germ hF hU (hsub ⟨hac.le,le_rfl⟩) ht hv hvc
  intro s hs
  rcases lt_trichotomy s c with hsc | hsc | hcs
  · have hsU := hsub ⟨hs.1,hsc.le⟩
    simp only [reflectOdd,reflectEven,ite_eq_left hsc.le]
    exact ⟨(ht s hsU).congr_of_eventuallyEq (reflectEven_germ_left t hsc),
      (hv s hsU).congr_of_eventuallyEq (reflectOdd_germ_left v hsc)⟩
  · subst s
    simp only [reflectOdd,reflectEven,ite_eq_left le_rfl]
    exact ⟨(ht c (hsub ⟨hac.le,le_rfl⟩)).congr_of_eventuallyEq (reflectEven_germ_center hcg.1),
      (hv c (hsub ⟨hac.le,le_rfl⟩)).congr_of_eventuallyEq (reflectOdd_germ_center hcg.2)⟩
  · have hrU : 2*c-s ∈ U := hsub ⟨by linarith [hs.2],by linarith⟩
    have ht' := (ht _ hrU).comp s ((hasDerivAt_id s).const_sub (2*c))
    have hv' := ((hv _ hrU).comp s ((hasDerivAt_id s).const_sub (2*c))).neg
    constructor
    · convert ht'.congr_of_eventuallyEq (reflectEven_germ_right t hcs) using 1 ; first | rfl | simp [reflectOdd,not_le.mpr hcs]
    · convert hv'.congr_of_eventuallyEq (reflectOdd_germ_right v hcs) using 1 ; first | rfl | simp [reflectEven,not_le.mpr hcs]

lemma reflected_scalar_smooth {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ U)
    (ht : ∀ s ∈ U, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ U, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (hta : ∀ s ∈ U, ContDiffAt ℝ ∞ t s) (hva : ∀ s ∈ U, ContDiffAt ℝ ∞ v s) :
    ∀ s ∈ Icc a (2*c-a), ContDiffAt ℝ ∞ (reflectEven c t) s ∧ ContDiffAt ℝ ∞ (reflectOdd c v) s := by
  have hcg := scalar_reflection_germ hF hU (hsub ⟨hac.le,le_rfl⟩) ht hv hvc
  intro s hs
  rcases lt_trichotomy s c with hsc | hsc | hcs
  · have hsU := hsub ⟨hs.1,hsc.le⟩
    exact ⟨(hta s hsU).congr_of_eventuallyEq (reflectEven_germ_left t hsc),
      (hva s hsU).congr_of_eventuallyEq (reflectOdd_germ_left v hsc)⟩
  · subst s
    exact ⟨(hta c (hsub ⟨hac.le,le_rfl⟩)).congr_of_eventuallyEq (reflectEven_germ_center hcg.1),
      (hva c (hsub ⟨hac.le,le_rfl⟩)).congr_of_eventuallyEq (reflectOdd_germ_center hcg.2)⟩
  · have hrU : 2*c-s ∈ U := hsub ⟨by linarith [hs.2],by linarith⟩
    exact ⟨((hta _ hrU).comp s (contDiffAt_const.sub contDiffAt_id)).congr_of_eventuallyEq
      (reflectEven_germ_right t hcs),
      (((hva _ hrU).comp s (contDiffAt_const.sub contDiffAt_id)).neg).congr_of_eventuallyEq
      (reflectOdd_germ_right v hcs)⟩

lemma reflected_closed_equations {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0) :
    ∀ s ∈ Icc a (2*c-a),
      HasDerivAt (reflectEven c t) (reflectOdd c v s) s ∧
      HasDerivAt (reflectOdd c v) (-F (reflectEven c t s)/2) s := by
  have hcg := scalar_reflection_germ hF isOpen_Ioo hc
    (fun s hs => ht s (Ioo_subset_Icc_self hs)) (fun s hs => hv s (Ioo_subset_Icc_self hs)) hvc
  intro s hs
  rcases lt_trichotomy s c with hsc | hsc | hcs
  · have hsU : s ∈ Icc a b := ⟨hs.1,hsc.le.trans hc.2.le⟩
    simp only [reflectOdd,reflectEven,ite_eq_left hsc.le]
    exact ⟨(ht s hsU).congr_of_eventuallyEq (reflectEven_germ_left t hsc),
      (hv s hsU).congr_of_eventuallyEq (reflectOdd_germ_left v hsc)⟩
  · subst s
    simp only [reflectOdd,reflectEven,ite_eq_left le_rfl]
    exact ⟨(ht c (Ioo_subset_Icc_self hc)).congr_of_eventuallyEq (reflectEven_germ_center hcg.1),
      (hv c (Ioo_subset_Icc_self hc)).congr_of_eventuallyEq (reflectOdd_germ_center hcg.2)⟩
  · have hrU : 2*c-s ∈ Icc a b := ⟨by linarith [hs.2],by linarith [hc.2]⟩
    have ht' := (ht _ hrU).comp s ((hasDerivAt_id s).const_sub (2*c))
    have hv' := ((hv _ hrU).comp s ((hasDerivAt_id s).const_sub (2*c))).neg
    constructor
    · convert ht'.congr_of_eventuallyEq (reflectEven_germ_right t hcs) using 1 ; first | rfl | simp [reflectOdd,not_le.mpr hcs]
    · convert hv'.congr_of_eventuallyEq (reflectOdd_germ_right v hcs) using 1 ; first | rfl | simp [reflectEven,not_le.mpr hcs]

lemma reflected_closed_smooth {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (hta : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc a b, ContDiffAt ℝ ∞ v s) :
    ∀ s ∈ Icc a (2*c-a), ContDiffAt ℝ ∞ (reflectEven c t) s ∧ ContDiffAt ℝ ∞ (reflectOdd c v) s := by
  have hcg := scalar_reflection_germ hF isOpen_Ioo hc
    (fun s hs => ht s (Ioo_subset_Icc_self hs)) (fun s hs => hv s (Ioo_subset_Icc_self hs)) hvc
  intro s hs
  rcases lt_trichotomy s c with hsc | hsc | hcs
  · have hsU : s ∈ Icc a b := ⟨hs.1,hsc.le.trans hc.2.le⟩
    exact ⟨(hta s hsU).congr_of_eventuallyEq (reflectEven_germ_left t hsc),
      (hva s hsU).congr_of_eventuallyEq (reflectOdd_germ_left v hsc)⟩
  · subst s
    exact ⟨(hta c (Ioo_subset_Icc_self hc)).congr_of_eventuallyEq (reflectEven_germ_center hcg.1),
      (hva c (Ioo_subset_Icc_self hc)).congr_of_eventuallyEq (reflectOdd_germ_center hcg.2)⟩
  · have hrU : 2*c-s ∈ Icc a b := ⟨by linarith [hs.2],by linarith [hc.2]⟩
    exact ⟨((hta _ hrU).comp s (contDiffAt_const.sub contDiffAt_id)).congr_of_eventuallyEq
      (reflectEven_germ_right t hcs),
      (((hva _ hrU).comp s (contDiffAt_const.sub contDiffAt_id)).neg).congr_of_eventuallyEq
      (reflectOdd_germ_right v hcs)⟩

theorem finite_turn_completion {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {a b c : ℝ} (hc : c ∈ Ioo a b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (ha : t a = 0) (hr : ∀ s ∈ Ioo a b, t s ∈ Ioo (0:ℝ) 1) :
    b ≤ 2*c-a ∧ EqOn (reflectEven c t) t (Icc a b) ∧ EqOn (reflectOdd c v) v (Icc a b) ∧
    reflectEven c t a = 0 ∧ reflectEven c t (2*c-a) = 0 ∧
    (∀ s ∈ Ioo a (2*c-a), reflectEven c t s ∈ Ioo (0:ℝ) 1) := by
  have hd := reflected_closed_equations hF hc ht hv hvc
  have ham : a < min b (2*c-a) := lt_min (hc.1.trans hc.2) (by linarith [hc.1])
  have hcm : c ∈ Ioo a (min b (2*c-a)) := ⟨hc.1,lt_min hc.2 (by linarith [hc.1])⟩
  have hsub : Icc a (min b (2*c-a)) ⊆ Icc a b := Icc_subset_Icc le_rfl (min_le_left _ _)
  have hrsub : Icc a (min b (2*c-a)) ⊆ Icc a (2*c-a) := Icc_subset_Icc le_rfl (min_le_right _ _)
  have he := scalar_equations_unique hF hcm
    (fun s hs => (hd s (hrsub hs)).1) (fun s hs => (hd s (hrsub hs)).2)
    (fun s hs => ht s (hsub hs)) (fun s hs => hv s (hsub hs))
    (by simp [reflectEven]) (by simp [reflectOdd])
  have hend : reflectEven c t (2*c-a) = 0 := by
    rw [reflectEven,ite_eq_right (by linarith [hc.1]),show 2*c-(2*c-a) = a by ring,ha]
  have hbL : b ≤ 2*c-a := by
    by_contra hn
    have hLb : 2*c-a < b := lt_of_not_ge hn
    have hs : 2*c-a ∈ Icc a (min b (2*c-a)) := ⟨by linarith [hc.1],by simp [hLb.le]⟩
    have hzero : t (2*c-a) = 0 := (he.1 hs).symm.trans hend
    have hh := (hr (2*c-a) ⟨by linarith [hc.1],hLb⟩).1
    rw [hzero] at hh
    exact lt_irrefl _ hh
  refine ⟨hbL,?_,?_,?_,hend,?_⟩
  · simpa only [min_eq_left hbL] using he.1
  · simpa only [min_eq_left hbL] using he.2
  · simpa [reflectEven,hc.1.le] using ha
  · intro s hs
    unfold reflectEven
    split_ifs with hsc
    · exact hr s ⟨hs.1,hsc.trans_lt hc.2⟩
    · exact hr (2*c-s) ⟨by linarith [hs.2],by linarith [hc.2]⟩
end ThreeManifold.PassageDynamics

namespace ThreeManifold.SupportExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def cut (b : ℝ) (V : ℝ → E) (s : ℝ) : E := if s ≤ b then V s else 0
omit [NormedSpace ℝ E] in
lemma cut_germ_left {b s : ℝ} {V : ℝ → E} (hs : s < b) : cut b V =ᶠ[𝓝 s] V := by
  filter_upwards [Iio_mem_nhds hs] with r hr
  exact ite_eq_left hr.le
omit [NormedSpace ℝ E] in
lemma cut_germ_right {b s : ℝ} {V : ℝ → E} (hs : b < s) : cut b V =ᶠ[𝓝 s] 0 := by
  filter_upwards [Ioi_mem_nhds hs] with r hr
  exact ite_eq_right (not_le.mpr hr)
omit [NormedSpace ℝ E] in
lemma cut_germ_center {b : ℝ} {V : ℝ → E} (hz : V =ᶠ[𝓝 b] 0) : cut b V =ᶠ[𝓝 b] 0 := by
  filter_upwards [hz] with r hr
  simp only [cut]
  split_ifs
  · exact hr
  · rfl
lemma cut_smoothAt {b s : ℝ} {V : ℝ → E} (hz : V =ᶠ[𝓝 b] 0)
    (hc : s ≤ b → ContDiffAt ℝ ∞ V s) : ContDiffAt ℝ ∞ (cut b V) s := by
  rcases lt_trichotomy s b with h | rfl | h
  · exact (hc h.le).congr_of_eventuallyEq (cut_germ_left h)
  · exact contDiffAt_const.congr_of_eventuallyEq (cut_germ_center hz)
  · exact contDiffAt_const.congr_of_eventuallyEq (cut_germ_right h)
omit [NormedSpace ℝ E] in
lemma cut_eq {b s : ℝ} {V : ℝ → E} (hs : s ≤ b) : cut b V s = V s := ite_eq_left hs
lemma cut_deriv {b s : ℝ} {V : ℝ → E} (hz : V =ᶠ[𝓝 b] 0) (hs : s ≤ b) :
    deriv (cut b V) s = deriv V s := by
  rcases hs.eq_or_lt with rfl | h
  · exact Filter.EventuallyEq.deriv_eq ((cut_germ_center hz).trans hz.symm)
  · exact Filter.EventuallyEq.deriv_eq (cut_germ_left h)
omit [NormedSpace ℝ E] in
lemma cut_zero {b s : ℝ} {V : ℝ → E} (hs : b < s) : cut b V s = 0 := ite_eq_right (not_le.mpr hs)
lemma cut_deriv_zero {b s : ℝ} {V : ℝ → E} (hs : b < s) : deriv (cut b V) s = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (cut_germ_right hs)]
  exact deriv_const s (0:E)
end ThreeManifold.SupportExtension
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck
lemma normalizedNeck_connection {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) (u v : E3) :
    connectionTerm (normalizedNeck hδ) (OpenPartialHomeomorph.refl E3) x u v =
      joinVector (gamma (P δ (x 0)) (deriv (Q δ) (x 0)) (splitVector u) (splitVector v)) :=
  connectionTerm_product _ _ (normalizedNeck_matrix_germ hδ hx)
    (Q_hasDerivAt ⟨hδ.1.le,hδ.2⟩ hx) (Q_mul_P ⟨hδ.1.le,hδ.2⟩ hx)
    (Q_deriv_transpose ⟨hδ.1.le,hδ.2⟩ hx) u v

lemma euclidean_curve_smooth {γ : ℝ → E3} {U : Set ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) : ContDiffOn ℝ ∞ γ U :=
  contMDiffOn_iff_contDiffOn.mp hγ
lemma euclidean_fieldCoordinates (γ J : ℝ → E3) :
    fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) = J := by
  funext s
  change mfderiv I3 I3 (id : E3 → E3) (γ s) (J s) = J s
  rw [mfderiv_eq_fderiv,fderiv_id]
  rfl
lemma euclidean_field_smooth {γ J : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) : ContDiffOn ℝ ∞ J U := by
  intro s hs
  have h := smoothField_coordinatesAt hU hγ hJ (chart_mem_atlas E3 (0 : E3)) hs (mem_univ _)
  change ContDiffAt ℝ ∞ (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s at h
  rw [euclidean_fieldCoordinates] at h
  exact h.contDiffWithinAt

lemma normalized_velocity_equation {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (normalizedNeck hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => splitVector (deriv γ r))
      (-gamma (P δ (γ s 0)) (deriv (Q δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))) s := by
  have hd := ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).derivWithin (m := ∞) (by simp)
  have he := hγ.2 (OpenPartialHomeomorph.refl E3) (chart_mem_atlas E3 (0 : E3)) s hs (mem_univ _)
  change deriv (deriv γ) s + connectionTerm (normalizedNeck hδ)
    (OpenPartialHomeomorph.refl E3) (γ s) (deriv γ s) (deriv γ s) = 0 at he
  rw [normalizedNeck_connection hδ ht] at he
  have h := TorusNeck.splitVector_hasDerivAt (hd.differentiableAt (by simp)).hasDerivAt
  rw [eq_neg_of_add_eq_zero_left he,TorusNeck.split_neg,split_join] at h
  exact h

lemma normalized_momentum_hasDerivAt {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (normalizedNeck hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => Q δ (γ r 0) *ᵥ (splitVector (deriv γ r)).2) 0 s := by
  have hg := ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
  have hheight := hasDerivAt_pi.mp hg.hasDerivAt 0
  have hv := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
    (normalized_velocity_equation hδ hU hγ hs ht)
  change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
    (-gamma (P δ (γ s 0)) (deriv (Q δ) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at hv
  have hu : HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-deriv γ s 0 • (P δ (γ s 0) *ᵥ (deriv (Q δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
    convert hv using 1
    ext i
    simp only [gamma, Prod.snd_neg, Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    change -deriv γ s 0 * _ = -(1/2 * (deriv γ s 0 * _ + deriv γ s 0 * _))
    ring
  exact momentum_hasDerivAt_zero (t := fun r => γ r 0) (v := fun r => deriv γ r 0) (Q_mul_P ⟨hδ.1.le,hδ.2⟩ ht)
    (Q_hasDerivAt ⟨hδ.1.le,hδ.2⟩ ht) hheight hu

lemma normalized_momentum_constant {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (ht : ∀ s ∈ U, γ s 0 ∈ Icc (0:ℝ) 1) :
    ∃ p : TVec, ∀ s ∈ U, Q δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p := by
  apply hU.exists_is_const_of_deriv_eq_zero hUc.isPreconnected
  · exact fun s hs => (normalized_momentum_hasDerivAt hδ hU hγ hs (ht s hs)).differentiableAt.differentiableWithinAt
  · exact fun s hs => (normalized_momentum_hasDerivAt hδ hU hγ hs (ht s hs)).deriv
end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma Q_deriv_jet_closed {δ t : ℝ} (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    deriv (Q δ) t = -Q δ t * P₁ δ t * Q δ t := by
  apply inverse_first_jet (P_hasDerivAt δ t) (Q_hasDerivAt hδ ht)
  · have hc : ContinuousAt (fun r => (P δ r).det) t :=
      (P_smooth δ).continuous.matrix_det.continuousAt
    filter_upwards [hc.eventually_ne (ne_of_gt (P_posDef hδ ht).det_pos)] with r hr
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hr)
  · exact Q_mul_P hδ ht

lemma normalized_velocity_torus {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : Q δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (splitVector (deriv γ s)).2 = P δ (γ s 0) *ᵥ p := by
  rw [← hp,mulVec_mulVec,P_mul_Q ⟨hδ.1.le,hδ.2⟩ ht,one_mulVec]

lemma normalized_scalar_equation {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (normalizedNeck hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : Q δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    HasDerivAt (fun r => deriv γ r 0) (-force false δ p (γ s 0)/2) s := by
  have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
    (normalized_velocity_equation hδ hU hγ hs ht)
  change HasDerivAt (fun r => deriv γ r 0)
    (-gamma (P δ (γ s 0)) (deriv (Q δ) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
  convert h using 1
  simp only [Prod.fst_neg,gamma]
  rw [normalized_velocity_torus hδ ht hp,Q_deriv_jet_closed ⟨hδ.1.le,hδ.2⟩ ht,
    pairing_mulVec_left,pairing_mulVec_right,
    Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ (γ s 0))]
  have he : P δ (γ s 0) * (-Q δ (γ s 0) * P₁ δ (γ s 0) * Q δ (γ s 0)) * P δ (γ s 0) =
      -P₁ δ (γ s 0) := by
    simp only [Matrix.neg_mul,Matrix.mul_neg,← Matrix.mul_assoc,
      P_mul_Q ⟨hδ.1.le,hδ.2⟩ ht,Matrix.one_mul]
    rw [Matrix.mul_assoc,Q_mul_P ⟨hδ.1.le,hδ.2⟩ ht,Matrix.mul_one]
  simp only [← Matrix.mul_assoc] at he
  simp only [← Matrix.mul_assoc]
  rw [he,pairing_matrix_neg]
  change -pairing (deriv (P δ) (γ s 0)) p p / 2 = _
  have hd : deriv (P δ) (γ s 0) = P₁ δ (γ s 0) := (P_hasDerivAt δ (γ s 0)).deriv
  rw [hd]
  ring

lemma euclidean_velocity {γ : ℝ → E3} : velocity γ = deriv γ := by
  funext s
  unfold velocity
  rw [mfderiv_eq_fderiv]
  rfl

lemma normalized_energy_identity {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : Q δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) =
      potential false δ p (γ s 0) + (deriv γ s 0)^2 := by
  rw [euclidean_velocity,normalizedNeck_bilin hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩]
  unfold Neck.metric
  rw [normalized_velocity_torus hδ ht hp,pairing_mulVec_left,pairing_mulVec_right,
    Matrix.isHermitian_iff_isSymm.mp (P_hermitian δ (γ s 0)),
    P_mul_Q ⟨hδ.1.le,hδ.2⟩ ht,Matrix.one_mul]
  simp only [potential,coordinateCometric,Bool.false_eq_true,ite_false,splitVector]
  ring

lemma normalized_energy_constant {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) :
    ∃ e : ℝ, ∀ s ∈ U, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = e := by
  apply hU.exists_is_const_of_deriv_eq_zero hUc.isPreconnected
  · exact fun s hs => (geodesic_speed_hasDerivAt _ hU hγ hs).differentiableAt.differentiableWithinAt
  · exact fun s hs => (geodesic_speed_hasDerivAt _ hU hγ hs).deriv

lemma normalizedNeck_curvature {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (0:ℝ) 1) (u v w : E3) :
    curvatureTerm (normalizedNeck hδ) (OpenPartialHomeomorph.refl E3) x u v w =
      joinVector (curvatureJet (P δ (x 0)) (deriv (Q δ) (x 0))
        (deriv (deriv (Q δ)) (x 0)) (splitVector u) (splitVector v) (splitVector w)) := by
  apply curvatureTerm_product _ _ (normalizedNeck_matrix_germ hδ ⟨hx.1.le,hx.2.le⟩)
  · filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact ⟨Q_hasDerivAt ⟨hδ.1.le,hδ.2⟩ ⟨ht.1.le,ht.2.le⟩,
      Q_mul_P ⟨hδ.1.le,hδ.2⟩ ⟨ht.1.le,ht.2.le⟩,
      Q_deriv_transpose ⟨hδ.1.le,hδ.2⟩ ⟨ht.1.le,ht.2.le⟩⟩
  · exact P_hasDerivAt_Qjet ⟨hδ.1.le,hδ.2⟩ hx
  · exact Q_deriv_hasDerivAt ⟨hδ.1.le,hδ.2⟩ ⟨hx.1.le,hx.2.le⟩

lemma normalizedNeck_covariant {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (γ J : ℝ → E3)
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    covariantDerivative (normalizedNeck hδ) γ J s = deriv J s +
      joinVector (gamma (P δ (γ s 0)) (deriv (Q δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s))) := by
  unfold covariantDerivative
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
    (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s = _
  rw [euclidean_fieldCoordinates,alongDerivative,normalizedNeck_connection hδ ht]

lemma normalizedNeck_curvatureAlong {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (γ J : ℝ → E3)
    {s : ℝ} (ht : γ s 0 ∈ Ioo (0:ℝ) 1) :
    curvatureAlong (normalizedNeck hδ) γ J s =
      joinVector (curvatureJet (P δ (γ s 0)) (deriv (Q δ) (γ s 0))
        (deriv (deriv (Q δ)) (γ s 0)) (splitVector (J s))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
    (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s) = _
  rw [euclidean_fieldCoordinates,normalizedNeck_curvature hδ ht]

lemma normalizedNeck_index_density {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Ioo (0:ℝ) 1) :
    indexPairDensity (normalizedNeck hδ) γ J J s =
      normalDensity (P δ (γ s 0)) (Q δ (γ s 0)) (deriv (Q δ) (γ s 0))
        (deriv (deriv (Q δ)) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s))
        (splitVector (deriv J s)) +
      ((normalizedNeck hδ).inner (γ s) (covariantDerivative (normalizedNeck hδ) γ J s) (velocity γ s))^2 := by
  rw [euclidean_velocity,normalizedNeck_covariant hδ γ J ⟨ht.1.le,ht.2.le⟩]
  unfold indexPairDensity
  rw [normalizedNeck_covariant hδ γ J ⟨ht.1.le,ht.2.le⟩,
    normalizedNeck_curvatureAlong hδ γ J ht]
  have hm : ∀ u v : E3, (normalizedNeck hδ).inner (γ s) u v = Neck.metric (Q δ (γ s 0)) (splitVector u) (splitVector v) :=
    normalizedNeck_bilin hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simp only [hm,
    TorusNeck.split_add,split_join,normalDensity]
  rw [metric_symm (Q_transpose δ (γ s 0)) (curvatureJet _ _ _ _ _ _) (splitVector (J s))]
  ring
end

section
open RiemannianCoordinates MetricConstruction Cometric Neck LocalNeck ReturningPassage

def fromRightLinear (δ : ℝ) : E3 ≃L[ℝ] E3 :=
  { toLinearEquiv :=
      { toFun := fun y => ![-y 0,δ^2*y 1+y 2,y 1]
        invFun := fun x => ![-x 0,x 2,x 1-δ^2*x 2]
        left_inv := by intro y; ext i; fin_cases i <;> simp
        right_inv := by intro x; ext i; fin_cases i <;> simp
        map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
        map_smul' := by intro a x; ext i; fin_cases i <;> simp [mul_add,mul_left_comm] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
def fromRight (δ : ℝ) (y : E3) : E3 := fromRightLinear δ y + ![1,0,0]
lemma fromRight_apply (δ : ℝ) (y : E3) : fromRight δ y = ![1-y 0,δ^2*y 1+y 2,y 1] := by
  ext i; fin_cases i <;> simp [fromRight,fromRightLinear]; ring
lemma fromRight_smooth (δ : ℝ) : ContDiff ℝ ∞ (fromRight δ) :=
  (fromRightLinear δ).contDiff.add contDiff_const
lemma fromRight_deriv (δ : ℝ) (y : E3) :
    mfderiv I3 I3 (fromRight δ) y = (fromRightLinear δ : E3 →L[ℝ] E3) := by
  rw [mfderiv_eq_fderiv]
  exact ((fromRightLinear δ).hasFDerivAt.add_const _).fderiv

def normalizedRight {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric E3 :=
  pullback (normalizedNeck hδ) (fromRight_smooth δ).contMDiff
    (fun _ => fromRightLinear δ) (fun y => (fromRight_deriv δ y).symm)

def fromRightIsometry {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) :
    LocalMetricIsometry (normalizedRight hδ) (normalizedNeck hδ) (fromRight δ) where
  domain := univ
  isOpen_domain := isOpen_univ
  smooth := (fromRight_smooth δ).contMDiff.contMDiffOn
  metric := by intro x _ u v; rfl

lemma right_inverse_formula (δ t : ℝ) :
    metricInverse true δ t = (T₂ δ)ᵀ * Q δ (1-t) * T₂ δ := by
  unfold metricInverse coordinateCometric
  simp only [ite_true, PEnd, Q, Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv]
  have hc : (C₂ δ)⁻¹ = T₂ δ := Matrix.inv_eq_right_inv (frame_inverse δ).1
  rw [hc,Matrix.mul_assoc]

lemma right_frame_pairing (δ : ℝ) (Q : TMat) (u v : E3) :
    metric Q (splitVector (fromRightLinear δ u)) (splitVector (fromRightLinear δ v)) =
      metric ((T₂ δ)ᵀ * Q * T₂ δ) (splitVector u) (splitVector v) := by
  have hu : (splitVector (fromRightLinear δ u)).2 = T₂ δ *ᵥ (splitVector u).2 := by
    ext i; fin_cases i <;> simp [splitVector,fromRightLinear,T₂,Matrix.mulVec]
  have hv : (splitVector (fromRightLinear δ v)).2 = T₂ δ *ᵥ (splitVector v).2 := by
    ext i; fin_cases i <;> simp [splitVector,fromRightLinear,T₂,Matrix.mulVec]
  unfold metric
  rw [hu,hv,pairing_mulVec_left,pairing_mulVec_right]
  change (-u 0)*(-v 0) + _ = u 0*v 0 + _
  rw [neg_mul_neg]

lemma normalizedRight_bilin {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) (u v : E3) :
    (normalizedRight hδ).inner x u v =
      metric (metricInverse true δ (x 0)) (splitVector u) (splitVector v) := by
  change (normalizedNeck hδ).inner (fromRight δ x)
    (mfderiv I3 I3 (fromRight δ) x u) (mfderiv I3 I3 (fromRight δ) x v) = _
  rw [fromRight_deriv]
  have hx' : fromRight δ x 0 ∈ Ioo (-1/4:ℝ) (5/4) := by
    rw [fromRight_apply]
    change 1-x 0 ∈ Ioo (-1/4:ℝ) (5/4)
    constructor <;> linarith [hx.1,hx.2]
  change (normalizedNeck hδ).inner (fromRight δ x) (show E3 from fromRightLinear δ u)
    (show E3 from fromRightLinear δ v) = _
  rw [normalizedNeck_bilin hδ hx',fromRight_apply]
  change metric (Q δ (1-x 0)) (splitVector (fromRightLinear δ u)) (splitVector (fromRightLinear δ v)) = _
  rw [right_frame_pairing,right_inverse_formula]

lemma normalizedRight_matrix {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) :
    metricMatrix (normalizedRight hδ) (OpenPartialHomeomorph.refl E3) x =
      blockMatrix (metricInverse true δ (x 0)) := by
  ext i j
  change (normalizedRight hδ).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change (normalizedRight hδ).inner x (basisVector i) (basisVector j) = _
  rw [normalizedRight_bilin hδ hx]
  fin_cases i <;> fin_cases j <;>
    simp [metric,splitVector,pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,basisVector,blockMatrix]
lemma normalizedRight_matrix_germ {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) :
    metricMatrix (normalizedRight hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[nhds x]
      fun y => blockMatrix (metricInverse true δ (y 0)) := by
  have hx' : x 0 ∈ Ioo (-1/4:ℝ) (5/4) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  filter_upwards [(continuous_apply 0).continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hx')] with y hy
  exact normalizedRight_matrix hδ hy

def framedNeck (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) : SmoothMetric E3 :=
  if right then normalizedRight hδ else normalizedNeck hδ

lemma framedNeck_bilin (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Ioo (-1/4:ℝ) (5/4)) (u v : E3) :
    (framedNeck right hδ).inner x u v =
      metric (metricInverse right δ (x 0)) (splitVector u) (splitVector v) := by
  cases right
  · exact normalizedNeck_bilin hδ hx u v
  · exact normalizedRight_bilin hδ hx u v

lemma framedNeck_matrix_germ (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) :
    metricMatrix (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[nhds x]
      fun y => blockMatrix (metricInverse right δ (y 0)) := by
  cases right
  · exact normalizedNeck_matrix_germ hδ hx
  · exact normalizedRight_matrix_germ hδ hx

lemma frame_elliptic (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) (q : TVec) :
    sqnorm q/9 ≤ qform (coordinateCometric right δ t) q ∧
      qform (coordinateCometric right δ t) q ≤ 18*sqnorm q := by
  cases right
  · have h := P_elliptic hδ ht q
    change sqnorm q/9 ≤ qform (P δ t) q ∧ qform (P δ t) q ≤ 18*sqnorm q
    constructor <;> linarith [h.1,h.2,sqnorm_nonneg q]
  · exact PEnd_elliptic hδ ht q
lemma frame_det_ne (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    (coordinateCometric right δ t).det ≠ 0 :=
  (coordinateCometric_posDef (fun q => (frame_elliptic right hδ ht q).1)).det_pos.ne'

lemma frame_QP (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    metricInverse right δ t * coordinateCometric right δ t = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (frame_det_ne right hδ ht))
lemma frame_PQ (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    coordinateCometric right δ t * metricInverse right δ t = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (frame_det_ne right hδ ht))
lemma framedNeck_connection (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) (u v : E3) :
    connectionTerm (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) x u v =
      joinVector (gamma (coordinateCometric right δ (x 0)) (deriv (metricInverse right δ) (x 0))
        (splitVector u) (splitVector v)) :=
  connectionTerm_product _ _ (framedNeck_matrix_germ right hδ hx)
    ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hx)).differentiableAt (by simp)).hasDerivAt
    (frame_QP right ⟨hδ.1.le,hδ.2⟩ hx) (metricInverse_deriv_transpose right δ (x 0)) u v
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma framed_velocity_equation (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => splitVector (deriv γ r))
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))) s := by
  have hd := ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).derivWithin (m := ∞) (by simp)
  have he := hγ.2 (OpenPartialHomeomorph.refl E3) (chart_mem_atlas E3 (0 : E3)) s hs (mem_univ _)
  change deriv (deriv γ) s + connectionTerm (framedNeck right hδ)
    (OpenPartialHomeomorph.refl E3) (γ s) (deriv γ s) (deriv γ s) = 0 at he
  rw [framedNeck_connection right hδ ht] at he
  have h := TorusNeck.splitVector_hasDerivAt (hd.differentiableAt (by simp)).hasDerivAt
  rw [eq_neg_of_add_eq_zero_left he,TorusNeck.split_neg,split_join] at h
  exact h

lemma framed_momentum_hasDerivAt (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => metricInverse right δ (γ r 0) *ᵥ (splitVector (deriv γ r)).2) 0 s := by
  have hg := ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)
  have hheight := hasDerivAt_pi.mp hg.hasDerivAt 0
  have hv := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
    (framed_velocity_equation right hδ hU hγ hs ht)
  change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
    (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at hv
  have hu : HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-deriv γ s 0 • (coordinateCometric right δ (γ s 0) *ᵥ (deriv (metricInverse right δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
    convert hv using 1
    ext i
    simp only [gamma, Prod.snd_neg, Pi.neg_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    change -deriv γ s 0 * _ = -(1/2 * (deriv γ s 0 * _ + deriv γ s 0 * _))
    ring
  exact momentum_hasDerivAt_zero (t := fun r => γ r 0) (v := fun r => deriv γ r 0) (frame_QP right ⟨hδ.1.le,hδ.2⟩ ht)
    (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht)).differentiableAt (by simp)).hasDerivAt) hheight hu

lemma framed_momentum_constant (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (ht : ∀ s ∈ U, γ s 0 ∈ Icc (0:ℝ) 1) :
    ∃ p : TVec, ∀ s ∈ U, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p := by
  apply hU.exists_is_const_of_deriv_eq_zero hUc.isPreconnected
  · exact fun s hs => (framed_momentum_hasDerivAt right hδ hU hγ hs (ht s hs)).differentiableAt.differentiableWithinAt
  · exact fun s hs => (framed_momentum_hasDerivAt right hδ hU hγ hs (ht s hs)).deriv

lemma framed_velocity_torus (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (splitVector (deriv γ s)).2 = coordinateCometric right δ (γ s 0) *ᵥ p := by
  rw [← hp,mulVec_mulVec,frame_PQ right ⟨hδ.1.le,hδ.2⟩ ht,one_mulVec]

lemma framed_scalar_equation (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    HasDerivAt (fun r => deriv γ r 0) (-force right δ p (γ s 0)/2) s := by
  have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
    (framed_velocity_equation right hδ hU hγ hs ht)
  change HasDerivAt (fun r => deriv γ r 0)
    (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
  convert h using 1
  simp only [Prod.fst_neg,gamma]
  rw [framed_velocity_torus right hδ ht hp,
    metricInverse_first (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),pairing_mulVec_left,pairing_mulVec_right,
    coordinateCometric_transpose]
  have he : coordinateCometric right δ (γ s 0) *
      (-metricInverse right δ (γ s 0) * deriv (coordinateCometric right δ) (γ s 0) * metricInverse right δ (γ s 0)) *
      coordinateCometric right δ (γ s 0) = -deriv (coordinateCometric right δ) (γ s 0) := by
    simp only [Matrix.neg_mul,Matrix.mul_neg,← Matrix.mul_assoc,
      frame_PQ right ⟨hδ.1.le,hδ.2⟩ ht,Matrix.one_mul]
    rw [Matrix.mul_assoc,frame_QP right ⟨hδ.1.le,hδ.2⟩ ht,Matrix.mul_one]
  simp only [← Matrix.mul_assoc] at he
  simp only [← Matrix.mul_assoc]
  rw [he,pairing_matrix_neg]
  change -pairing (deriv (coordinateCometric right δ) (γ s 0)) p p / 2 = _
  ring

lemma framed_energy_identity (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) :
    (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) =
      potential right δ p (γ s 0) + (deriv γ s 0)^2 := by
  rw [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩]
  unfold Neck.metric
  rw [framed_velocity_torus right hδ ht hp,pairing_mulVec_left,pairing_mulVec_right,
    coordinateCometric_transpose,frame_PQ right ⟨hδ.1.le,hδ.2⟩ ht,Matrix.one_mul]
  simp only [potential,splitVector]
  ring

lemma framed_P_hasDerivAt (right : Bool) {δ t : ℝ}
    (hδ : δ ∈ Icc 0 (1/2)) (ht : t ∈ Icc 0 1) :
    HasDerivAt (coordinateCometric right δ)
      (-coordinateCometric right δ t * deriv (metricInverse right δ) t * coordinateCometric right δ t) t := by
  have he : -coordinateCometric right δ t * deriv (metricInverse right δ) t * coordinateCometric right δ t =
      deriv (coordinateCometric right δ) t := by
    rw [metricInverse_first (frame_det_ne right hδ ht)]
    simp only [Matrix.neg_mul,Matrix.mul_neg,neg_neg,← Matrix.mul_assoc,
      frame_PQ right hδ ht,Matrix.one_mul]
    rw [Matrix.mul_assoc,frame_QP right hδ ht,Matrix.mul_one]
  rw [he]
  exact ((coordinateCometric_smooth right δ).differentiable (by simp) t).hasDerivAt
lemma framedNeck_curvature (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {x : E3}
    (hx : x 0 ∈ Icc (0:ℝ) 1) (u v w : E3) :
    curvatureTerm (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) x u v w =
      joinVector (curvatureJet (coordinateCometric right δ (x 0)) (deriv (metricInverse right δ) (x 0))
        (deriv (deriv (metricInverse right δ)) (x 0)) (splitVector u) (splitVector v) (splitVector w)) := by
  apply curvatureTerm_product _ _ (framedNeck_matrix_germ right hδ hx)
  · have hc : ContinuousAt (fun t => (coordinateCometric right δ t).det) (x 0) :=
      (coordinateCometric_smooth right δ).continuous.matrix_det.continuousAt
    filter_upwards [hc.eventually_ne (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hx)] with t ht
    exact ⟨((metricInverse_smoothAt ht).differentiableAt (by simp)).hasDerivAt,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr ht),metricInverse_deriv_transpose right δ t⟩
  · exact framed_P_hasDerivAt right ⟨hδ.1.le,hδ.2⟩ hx
  · exact (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hx)).derivWithin
      (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt

lemma framedNeck_covariant (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (γ J : ℝ → E3)
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    covariantDerivative (framedNeck right hδ) γ J s = deriv J s +
      joinVector (gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s))) := by
  unfold covariantDerivative
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
    (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s = _
  rw [euclidean_fieldCoordinates,alongDerivative,framedNeck_connection right hδ ht]

lemma framedNeck_curvatureAlong (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (γ J : ℝ → E3)
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    curvatureAlong (framedNeck right hδ) γ J s =
      joinVector (curvatureJet (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (J s))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
    (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s) = _
  rw [euclidean_fieldCoordinates,framedNeck_curvature right hδ ht]

lemma framedNeck_index_density (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    indexPairDensity (framedNeck right hδ) γ J J s =
      normalDensity (coordinateCometric right δ (γ s 0)) (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s))
        (splitVector (deriv J s)) +
      ((framedNeck right hδ).inner (γ s) (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2 := by
  rw [euclidean_velocity,framedNeck_covariant right hδ γ J ht]
  unfold indexPairDensity
  rw [framedNeck_covariant right hδ γ J ht,
    framedNeck_curvatureAlong right hδ γ J ht]
  have hm : ∀ u v : E3, (framedNeck right hδ).inner (γ s) u v = Neck.metric (metricInverse right δ (γ s 0)) (splitVector u) (splitVector v) :=
    framedNeck_bilin right hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩
  simp only [hm,
    TorusNeck.split_add,split_join,normalDensity]
  rw [metric_symm (metricInverse_transpose right δ (γ s 0)) (curvatureJet _ _ _ _ _ _) (splitVector (J s))]
  ring
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma split_deriv {J : ℝ → E3} {s : ℝ} (hJ : DifferentiableAt ℝ J s) :
    deriv (fun r => splitVector (J r)) s = splitVector (deriv J s) :=
  (TorusNeck.splitVector_hasDerivAt hJ.hasDerivAt).deriv

lemma normalized_return_density {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Ioo (0:ℝ) 1) {p : TVec}
    (hp : Q δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) (hJ : DifferentiableAt ℝ J s) :
    returnNormalDensity false δ p (fun r => γ r 0) (fun r => deriv γ r 0)
      (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s =
    indexPairDensity (normalizedNeck hδ) γ J J s -
      ((normalizedNeck hδ).inner (γ s) (covariantDerivative (normalizedNeck hδ) γ J s) (velocity γ s))^2 := by
  rw [normalizedNeck_index_density hδ ht,add_sub_cancel_right]
  have he : momentumVelocity false δ p (fun r => γ r 0) (fun r => deriv γ r 0) s =
      splitVector (deriv γ s) := by
    apply Prod.ext
    · rfl
    · exact (normalized_velocity_torus hδ ⟨ht.1.le,ht.2.le⟩ hp).symm
  rw [returnNormalDensity,he,split_deriv hJ]
  rfl

theorem normalized_left_return_index {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3 * C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (P δ u) q ∧ qform (P δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (P δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (P δ)) u) q ∧
      sqnorm (deriv (P δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (P δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hL : 0 < L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, Q δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0) (h1 : γ L 0 = 0)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hstar : 1/4 < γ (L/2) 0)
    (henergy : ∀ s ∈ Icc 0 L,
      (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (normalizedNeck hδ) γ J J s := by
  have hgc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ γ s :=
    (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))
  have hJc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ J s :=
    (euclidean_field_smooth hU hγ.1 hJ).contDiffAt (hU.mem_nhds (hsub hs))
  have hrc (s : ℝ) (hs : s ∈ Icc 0 L) : γ s 0 ∈ Icc (0:ℝ) 1 := by
    rcases eq_or_lt_of_le hs.1 with rfl | hs0
    · simp [h0]
    rcases eq_or_lt_of_le hs.2 with rfl | hsL
    · simp [h1]
    exact ⟨(hr s ⟨hs0,hsL⟩).1.le,(hr s ⟨hs0,hsL⟩).2.le⟩
  have hVa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ (fun r => splitVector (J r)) s := by
    exact (TorusNeck.splitVector_smooth.contDiffAt.comp s (hJc s hs))
  have hbound : 0 ≤ ∫ s in (0:ℝ)..L,
      returnNormalDensity false δ p (fun r => γ r 0) (fun r => deriv γ r 0)
        (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s := by
    apply returning_arbitrary_field_nonnegative (right := false) (p := p)
      (t := fun r => γ r 0) (v := fun r => deriv γ r 0) hC hsmall (fun u hu q => (hb u hu q).1)
      (fun u hu => ?_) (fun u hu q => (hb u hu q).2.2.1)
      (fun u hu => (hb u hu p).2.2.2) hL hstar
      (fun s hs => hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0)
      (fun s hs => normalized_scalar_equation hδ hU hγ (hsub hs) (hrc s hs) (hp s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s (hgc s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s
        ((hgc s hs).derivWithin (m := ∞) (by simp)))
      h0 h1 hr (fun s hs => (normalized_energy_identity hδ (hrc s hs) (hp s hs)).symm.trans (henergy s hs)) hVa
    simpa only [sqnorm_e,mul_one,coordinateCometric,Bool.false_eq_true,ite_false] using (hb u hu e).2.1
  let f := indexPairDensity (normalizedNeck hδ) γ J J
  let q := fun s => ((normalizedNeck hδ).inner (γ s)
      (covariantDerivative (normalizedNeck hδ) γ J s) (velocity γ s))^2
  have hfi : IntervalIntegrable f volume 0 L :=
    ((indexPairDensity_smooth _ hU hγ.1 hJ hJ).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have hqi : IntervalIntegrable q volume 0 L :=
    (((intrinsic_pairing_smooth _ hU hγ.1 (covariantDerivative_smooth _ hU hγ.1 hJ)
      (velocity_smooth hU hγ.1)).pow 2).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have he : (∫ s in (0:ℝ)..L, returnNormalDensity false δ p (fun r => γ r 0)
      (fun r => deriv γ r 0) (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s) =
      ∫ s in (0:ℝ)..L, (f s - q s) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le hL.le]
    intro s hs
    exact normalized_return_density hδ (hr s hs) (hp s (Ioo_subset_Icc_self hs))
      ((hJc s (Ioo_subset_Icc_self hs)).differentiableAt (by simp))
  rw [he,intervalIntegral.integral_sub hfi hqi] at hbound
  have hq : 0 ≤ ∫ s in (0:ℝ)..L, q s := intervalIntegral.integral_nonneg hL.le (fun s _ => sq_nonneg _)
  linarith
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients
lemma framed_return_density (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Ioo (0:ℝ) 1) {p : TVec}
    (hp : metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p) (hJ : DifferentiableAt ℝ J s) :
    returnNormalDensity right δ p (fun r => γ r 0) (fun r => deriv γ r 0)
      (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s =
    indexPairDensity (framedNeck right hδ) γ J J s -
      ((framedNeck right hδ).inner (γ s) (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2 := by
  rw [framedNeck_index_density right hδ ⟨ht.1.le,ht.2.le⟩,add_sub_cancel_right]
  have he : momentumVelocity right δ p (fun r => γ r 0) (fun r => deriv γ r 0) s =
      splitVector (deriv γ s) := by
    apply Prod.ext
    · rfl
    · exact (framed_velocity_torus right hδ ⟨ht.1.le,ht.2.le⟩ hp).symm
  rw [returnNormalDensity,he,split_deriv hJ]

theorem framed_return_index (right : Bool) {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3 * C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hL : 0 < L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0) (h1 : γ L 0 = 0)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hstar : 1/4 < γ (L/2) 0)
    (henergy : ∀ s ∈ Icc 0 L,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  have hgc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ γ s :=
    (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))
  have hJc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ J s :=
    (euclidean_field_smooth hU hγ.1 hJ).contDiffAt (hU.mem_nhds (hsub hs))
  have hrc (s : ℝ) (hs : s ∈ Icc 0 L) : γ s 0 ∈ Icc (0:ℝ) 1 := by
    rcases eq_or_lt_of_le hs.1 with rfl | hs0
    · simp [h0]
    rcases eq_or_lt_of_le hs.2 with rfl | hsL
    · simp [h1]
    exact ⟨(hr s ⟨hs0,hsL⟩).1.le,(hr s ⟨hs0,hsL⟩).2.le⟩
  have hVa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ (fun r => splitVector (J r)) s := by
    exact (TorusNeck.splitVector_smooth.contDiffAt.comp s (hJc s hs))
  have hbound : 0 ≤ ∫ s in (0:ℝ)..L,
      returnNormalDensity right δ p (fun r => γ r 0) (fun r => deriv γ r 0)
        (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s := by
    apply returning_arbitrary_field_nonnegative (right := right) (p := p)
      (t := fun r => γ r 0) (v := fun r => deriv γ r 0) hC hsmall (fun u hu q => (hb u hu q).1)
      (fun u hu => ?_) (fun u hu q => (hb u hu q).2.2.1)
      (fun u hu => (hb u hu p).2.2.2) hL hstar
      (fun s hs => hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0)
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s (hgc s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s
        ((hgc s hs).derivWithin (m := ∞) (by simp)))
      h0 h1 hr (fun s hs => (framed_energy_identity right hδ (hrc s hs) (hp s hs)).symm.trans (henergy s hs)) hVa
    simpa only [sqnorm_e,mul_one] using (hb u hu e).2.1
  let f := indexPairDensity (framedNeck right hδ) γ J J
  let q := fun s => ((framedNeck right hδ).inner (γ s)
      (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2
  have hfi : IntervalIntegrable f volume 0 L :=
    ((indexPairDensity_smooth _ hU hγ.1 hJ hJ).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have hqi : IntervalIntegrable q volume 0 L :=
    (((intrinsic_pairing_smooth _ hU hγ.1 (covariantDerivative_smooth _ hU hγ.1 hJ)
      (velocity_smooth hU hγ.1)).pow 2).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have he : (∫ s in (0:ℝ)..L, returnNormalDensity right δ p (fun r => γ r 0)
      (fun r => deriv γ r 0) (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s) =
      ∫ s in (0:ℝ)..L, (f s - q s) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le hL.le]
    intro s hs
    exact framed_return_density right hδ (hr s hs) (hp s (Ioo_subset_Icc_self hs))
      ((hJc s (Ioo_subset_Icc_self hs)).differentiableAt (by simp))
  rw [he,intervalIntegral.integral_sub hfi hqi] at hbound
  have hq : 0 ≤ ∫ s in (0:ℝ)..L, q s := intervalIntegral.integral_nonneg hL.le (fun s _ => sq_nonneg _)
  linarith
end ThreeManifold.CompactMetric

end

end OAI
