import OAI.Geometry.ComplexBundle.GrassmannManifold
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Equiv

namespace OAI

noncomputable section

namespace Kaplansky

/-! Punctures, collapse, and hyperplane retraction in projective space. -/

section
open Set
namespace ComplexGrassmann

/-- Interchange the two one-dimensional factors of a projective-line chart. -/
def oppositeLineFrame (F : GraphFrame 1 1) : GraphFrame 1 1 :=
  F.trans (LinearEquiv.prodComm ℂ _ _)

/-- In complex dimension one the opposite affine chart omits exactly the
origin of the original chart. This uses actual lines in the ambient space. -/
theorem oppositeLineFrame_source (F : GraphFrame 1 1) :
    (grassmannChart (oppositeLineFrame F)).source =
      ({graphPoint F 0}ᶜ : Set (Grassmann 1 1)) := by
  ext P
  change Function.Bijective (graphProjection (oppositeLineFrame F) P.val) ↔ P ≠ graphPoint F 0
  have hdim : Module.finrank ℂ P.val = Module.finrank ℂ (GraphHorizontal 1) := by
    simp [P.property, GraphHorizontal]
  rw [Function.Bijective, ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim,
    and_self]
  constructor
  · intro hi he
    subst P
    let x : GraphHorizontal 1 := fun _ => 1
    have h := hi (a₁ := graphPlaneEquiv F 0 x) (a₂ := 0) (by
      change (F (F.symm (x, (0 : GraphMap 1 1) x))).2 = (F 0).2
      rw [LinearEquiv.apply_symm_apply, F.map_zero]
      rfl)
    have hx0 : x = 0 := (graphPlaneEquiv F 0).injective
      (h.trans (graphPlaneEquiv F 0).map_zero.symm)
    have hx1 := congrFun hx0 0
    simp [x] at hx1
  · intro hne
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    apply Subtype.ext
    change z.val = 0
    by_contra hz0
    have hv : (F z.val).2 = 0 := hz
    have hm : z.val ∈ graphPlane F 0 := by
      change (F z.val).2 = (0 : GraphMap 1 1) (F z.val).1
      simpa using hv
    have hp := eq_span_singleton_of_mem_of_finrank_eq_one P.property z.property hz0
    have hq := eq_span_singleton_of_mem_of_finrank_eq_one (graphPlane_finrank F 0) hm hz0
    exact hne (Subtype.ext (hp.trans hq.symm))

/-- The projective line minus any point is the entire affine complex model. -/
def projectiveLinePunctureHomeomorph (P : Grassmann 1 1) :
    ({P}ᶜ : Set (Grassmann 1 1)) ≃ₜ GraphSlope 1 1 := by
  let F := (graph_charts_cover P.val P.property).choose
  have hF := (graph_charts_cover P.val P.property).choose_spec
  have hp : graphPoint F 0 = P := Subtype.ext hF
  let e := grassmannChart (oppositeLineFrame F)
  have hs : e.source = ({P}ᶜ : Set (Grassmann 1 1)) := by
    rw [oppositeLineFrame_source, hp]
  exact (Homeomorph.setCongr hs.symm).trans (e.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (grassmannChart_target _)).trans (Homeomorph.Set.univ _)))

theorem projectiveLinePuncture_contractible (P : Grassmann 1 1) :
    ContractibleSpace ({P}ᶜ : Set (Grassmann 1 1)) :=
  (projectiveLinePunctureHomeomorph P).contractibleSpace

end ComplexGrassmann

end

section
open Set Topology
namespace ComplexGrassmann

section
variable {k l : ℕ}

/-- The actual image line, when the linear map is injective on that line. -/
def projectiveLinearImage (L : Components 1 k →L[ℂ] Components 1 l)
    (P : Grassmann 1 k) (h : Function.Injective (L.toLinearMap.comp P.val.subtype)) :
    Grassmann 1 l :=
  ⟨P.val.map L.toLinearMap, by
    rw [← Submodule.range_subtype P.val, ← LinearMap.range_comp,
      LinearMap.finrank_range_of_inj h]
    exact P.property⟩

/-- A continuously varying independent frame for a graph-chart line. -/
def graphLineFrame (F : GraphFrame 1 k) (A : GraphSlope 1 k) : PlaneFrameMap 1 k :=
  F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ _).prod A)

theorem graphLineFrame_injective (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    Function.Injective (graphLineFrame F A) := by
  intro x y h
  exact congrArg Prod.fst (F.symm.injective h)

theorem graphLineFrame_point (F : GraphFrame 1 k) (A : GraphSlope 1 k) :
    framePoint ⟨graphLineFrame F A, graphLineFrame_injective F A⟩ = slopePoint F A := by
  apply Subtype.ext
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change (F (F.symm (x, A x))).2 = A (F (F.symm (x, A x))).1
    simp
  · intro hz
    refine ⟨(F z).1, ?_⟩
    change F.symm ((F z).1, A (F z).1) = z
    apply F.injective
    simp only [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hz.symm

theorem continuous_graphLineFrame (F : GraphFrame 1 k) : Continuous (graphLineFrame F) := by
  apply continuous_clm_apply.mpr
  intro v
  exact F.symm.toContinuousLinearEquiv.continuous.comp
    (continuous_const.prodMk (continuous_id.clm_apply continuous_const))

/-- Linear images vary continuously even if the ambient map is singular;
only injectivity on the input line is needed. -/
theorem continuous_projectiveLinearImage {X : Type*} [TopologicalSpace X]
    (L : X → Components 1 k →L[ℂ] Components 1 l) (P : X → Grassmann 1 k)
    (h : ∀ x, Function.Injective ((L x).toLinearMap.comp (P x).val.subtype))
    (hL : Continuous L) (hP : Continuous P) :
    Continuous (fun x => projectiveLinearImage (L x) (P x) (h x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨F, hF⟩ := grassmann_atlas_covers (P x)
  let U := P ⁻¹' (grassmannChart F).source
  have hU : IsOpen U := (grassmannChart F).open_source.preimage hP
  have hc : Continuous (fun y : U => slopeCoordinate F (P y.val)) :=
    (grassmannChart F).continuousOn.comp_continuous
      (hP.comp continuous_subtype_val) (fun y => y.property)
  let B : U → PlaneFrameMap 1 l := fun y =>
    (L y.val).comp (graphLineFrame F (slopeCoordinate F (P y.val)))
  have hB : ∀ y, Function.Injective (B y) := by
    intro y u v huv
    have hg := graphLineFrame_point F (slopeCoordinate F (P y.val))
    rw [slopePoint_coordinate F (P y.val) y.property] at hg
    have hm (w) : graphLineFrame F (slopeCoordinate F (P y.val)) w ∈ (P y.val).val := by
      have he := congrArg Subtype.val hg
      exact he ▸ (show graphLineFrame F (slopeCoordinate F (P y.val)) w ∈
        LinearMap.range (graphLineFrame F (slopeCoordinate F (P y.val))).toLinearMap from ⟨w, rfl⟩)
    have he := h y.val (a₁ := ⟨_, hm u⟩) (a₂ := ⟨_, hm v⟩) huv
    exact graphLineFrame_injective F _ (congrArg Subtype.val he)
  have he (y : U) : framePoint ⟨B y, hB y⟩ =
      projectiveLinearImage (L y.val) (P y.val) (h y.val) := by
    apply Subtype.ext
    change LinearMap.range ((L y.val).toLinearMap.comp
      (graphLineFrame F (slopeCoordinate F (P y.val))).toLinearMap) = _
    rw [LinearMap.range_comp]
    have hg := congrArg Subtype.val (graphLineFrame_point F (slopeCoordinate F (P y.val)))
    rw [slopePoint_coordinate F (P y.val) y.property] at hg
    exact congrArg (Submodule.map (L y.val).toLinearMap) hg
  have hb : Continuous B := (hL.comp continuous_subtype_val).clm_comp
    ((continuous_graphLineFrame F).comp hc)
  have hi : Continuous (fun y : U => projectiveLinearImage (L y.val) (P y.val) (h y.val)) :=
    (framePoint_continuous.comp (hb.subtype_mk hB)).congr he
  exact ((continuousOn_iff_continuous_domRestrict.mpr hi) x hF).continuousAt
    (hU.mem_nhds hF)

end

variable {k : ℕ}

/-- Projection along the removed line is injective on every other line. -/
theorem verticalProjection_injective_iff (F : GraphFrame 1 k) (P : Grassmann 1 k) :
    Function.Injective (fun z : P.val => (F z.val).2) ↔ P ≠ graphPoint F 0 := by
  constructor
  · intro hi he
    subst P
    let x : GraphHorizontal 1 := fun _ => 1
    have h := hi (a₁ := graphPlaneEquiv F 0 x) (a₂ := 0) (by
      simp [graphPlaneEquiv, graphPoint])
    have hx0 : x = 0 := (graphPlaneEquiv F 0).injective
      (h.trans (graphPlaneEquiv F 0).map_zero.symm)
    have hx1 := congrFun hx0 0
    simp [x] at hx1
  · intro hne
    let L := (LinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical k)).comp
      (F.toLinearMap.comp P.val.subtype)
    change Function.Injective L
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro z hz
    apply Subtype.ext
    change z.val = 0
    by_contra hz0
    have hv : (F z.val).2 = 0 := hz
    have hm : z.val ∈ graphPlane F 0 := by simpa using hv
    have hp := eq_span_singleton_of_mem_of_finrank_eq_one P.property z.property hz0
    have hq := eq_span_singleton_of_mem_of_finrank_eq_one (graphPlane_finrank F 0) hm hz0
    exact hne (Subtype.ext (hp.trans hq.symm))

/-- Scale the removed-line coordinate and leave the complementary coordinates fixed. -/
def punctureCollapseLinear (F : GraphFrame 1 k) (c : ℂ) :
    Components 1 k →L[ℂ] Components 1 k :=
  F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((c • ContinuousLinearMap.fst ℂ (GraphHorizontal 1) (GraphVertical k)).prod
      (ContinuousLinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical k))).comp
      F.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem punctureCollapseLinear_coordinates (F : GraphFrame 1 k) (c : ℂ)
    (v : Components 1 k) :
    F (punctureCollapseLinear F c v) = (c • (F v).1, (F v).2) :=
  F.apply_symm_apply _

theorem continuous_punctureCollapseLinear (F : GraphFrame 1 k) :
    Continuous (punctureCollapseLinear F) := by
  apply continuous_clm_apply.mpr
  intro v
  exact F.symm.toContinuousLinearEquiv.continuous.comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)

theorem punctureCollapseLinear_injective (F : GraphFrame 1 k) (c : ℂ)
    (P : Grassmann 1 k) (hP : P ≠ graphPoint F 0) :
    Function.Injective ((punctureCollapseLinear F c).toLinearMap.comp P.val.subtype) := by
  intro x y h
  apply (verticalProjection_injective_iff F P).mpr hP
  have he := congrArg (fun z => (F z).2) h
  simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
    Submodule.subtype_apply, punctureCollapseLinear_coordinates] using he

/-- Collapse within the punctured projective space, including at c=0. -/
def punctureCollapse (F : GraphFrame 1 k) (c : ℂ)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))) : Grassmann 1 k :=
  projectiveLinearImage (punctureCollapseLinear F c) P.val
    (punctureCollapseLinear_injective F c P.val P.property)

theorem punctureCollapse_ne_center (F : GraphFrame 1 k) (c : ℂ)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))) :
    punctureCollapse F c P ≠ graphPoint F 0 := by
  apply (verticalProjection_injective_iff F _).mp
  intro x y h
  obtain ⟨u, hu, hux⟩ := x.property
  obtain ⟨v, hv, hvy⟩ := y.property
  apply Subtype.ext
  have he : (F u).2 = (F v).2 := by
    change (F x.val).2 = (F y.val).2 at h
    rw [← hux, ← hvy] at h
    simpa only [ContinuousLinearMap.coe_coe, punctureCollapseLinear_coordinates] using h
  have huv := (verticalProjection_injective_iff F P.val).mpr P.property
    (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) he
  exact hux.symm.trans ((congrArg (punctureCollapseLinear F c)
    (congrArg Subtype.val huv)).trans hvy)

theorem continuous_punctureCollapse (F : GraphFrame 1 k) :
    Continuous (fun z : ℂ × ({graphPoint F 0}ᶜ : Set (Grassmann 1 k)) =>
      punctureCollapse F z.1 z.2) :=
  continuous_projectiveLinearImage _ _ _
    ((continuous_punctureCollapseLinear F).comp continuous_fst)
    (continuous_subtype_val.comp continuous_snd)

theorem punctureCollapse_one (F : GraphFrame 1 k)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))) : punctureCollapse F 1 P = P.val := by
  apply Subtype.ext
  have hL : (punctureCollapseLinear F 1).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro z
    apply F.injective
    simp
  change P.val.val.map (punctureCollapseLinear F 1).toLinearMap = P.val.val
  rw [hL, Submodule.map_id]

/-- The endpoint lies entirely in the complementary projective hyperplane. -/
theorem punctureCollapse_zero_horizontal (F : GraphFrame 1 k)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k)))
    (z : (punctureCollapse F 0 P).val) : (F z.val).1 = 0 := by
  obtain ⟨u, hu, huz⟩ := z.property
  rw [← huz]
  simp

/-- Every point already in the complementary hyperplane stays fixed. -/
theorem punctureCollapse_fixed (F : GraphFrame 1 k) (c : ℂ)
    (P : ({graphPoint F 0}ᶜ : Set (Grassmann 1 k)))
    (hP : ∀ z : P.val.val, (F z.val).1 = 0) : punctureCollapse F c P = P.val := by
  apply Subtype.ext
  have he (u : P.val.val) : punctureCollapseLinear F c u.val = u.val := by
    apply F.injective
    rw [punctureCollapseLinear_coordinates]
    exact Prod.ext (by simp [hP u]) rfl
  change P.val.val.map (punctureCollapseLinear F c).toLinearMap = P.val.val
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    change punctureCollapseLinear F c u ∈ P.val.val
    rw [he ⟨u, hu⟩]
    exact hu
  · intro hz
    exact ⟨z, hz, he ⟨z, hz⟩⟩

end ComplexGrassmann

end

section
open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {k : ℕ}

abbrev ProjectivePuncture (F : GraphFrame 1 k) :=
  ({graphPoint F 0}ᶜ : Set (Grassmann 1 k))

/-- The actual complementary projective hyperplane, as a subspace of the puncture. -/
def PunctureHyperplane (F : GraphFrame 1 k) :=
  {P : ProjectivePuncture F // ∀ z : P.val.val, (F z.val).1 = 0}

instance (F : GraphFrame 1 k) : TopologicalSpace (PunctureHyperplane F) :=
  inferInstanceAs (TopologicalSpace {P : ProjectivePuncture F //
    ∀ z : P.val.val, (F z.val).1 = 0})

def punctureHyperplaneInclusion (F : GraphFrame 1 k) :
    C(PunctureHyperplane F, ProjectivePuncture F) := ⟨Subtype.val, continuous_subtype_val⟩

def punctureHyperplaneRetraction (F : GraphFrame 1 k) :
    C(ProjectivePuncture F, PunctureHyperplane F) where
  toFun P := ⟨⟨punctureCollapse F 0 P, punctureCollapse_ne_center F 0 P⟩,
    punctureCollapse_zero_horizontal F P⟩
  continuous_toFun := ((continuous_punctureCollapse F).comp
    (continuous_const.prodMk continuous_id)).subtype_mk _ |>.subtype_mk _

theorem punctureHyperplaneRetraction_inclusion (F : GraphFrame 1 k)
    (P : PunctureHyperplane F) :
    punctureHyperplaneRetraction F (punctureHyperplaneInclusion F P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  exact punctureCollapse_fixed F 0 P.val P.property

/-- The deformation scales [a:v] to [(1-t)a:v]; it stays outside the
removed point and fixes the entire complementary hyperplane. -/
def punctureDeformation (F : GraphFrame 1 k) :
    (ContinuousMap.id (ProjectivePuncture F)).Homotopy
      ((punctureHyperplaneInclusion F).comp (punctureHyperplaneRetraction F)) where
  toFun z := ⟨punctureCollapse F (1 - (z.1.val : ℂ)) z.2,
    punctureCollapse_ne_center F _ z.2⟩
  continuous_toFun := ((continuous_punctureCollapse F).comp
    ((continuous_const.sub (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)).subtype_mk _
  map_zero_left P := by
    apply Subtype.ext
    change punctureCollapse F (1 - ((0 : ℝ) : ℂ)) P = P.val
    simpa using punctureCollapse_one F P
  map_one_left P := by
    apply Subtype.ext
    change punctureCollapse F (1 - ((1 : ℝ) : ℂ)) P = punctureCollapse F 0 P
    simp

theorem punctureDeformation_fixes (F : GraphFrame 1 k) (t : unitInterval)
    (P : PunctureHyperplane F) :
    punctureDeformation F (t, punctureHyperplaneInclusion F P) =
      punctureHyperplaneInclusion F P := by
  apply Subtype.ext
  exact punctureCollapse_fixed F _ P.val P.property

/-- A proved homotopy equivalence, not a deformation-retraction premise. -/
def punctureHyperplaneHomotopyEquiv (F : GraphFrame 1 k) :
    ProjectivePuncture F ≃ₕ PunctureHyperplane F where
  toFun := punctureHyperplaneRetraction F
  invFun := punctureHyperplaneInclusion F
  left_inv := ⟨(punctureDeformation F).symm⟩
  right_inv := by
    have he : (punctureHyperplaneRetraction F).comp (punctureHyperplaneInclusion F) =
        ContinuousMap.id _ := ContinuousMap.ext (punctureHyperplaneRetraction_inclusion F)
    rw [he]

end ComplexGrassmann

end

open Set Topology ContinuousMap
namespace ComplexGrassmann
variable {k : ℕ}

def verticalAmbientEquiv (k : ℕ) : Components 1 k ≃L[ℂ] GraphVertical (k+1) :=
  (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (k+1) => ℂ)
    (finCongr (Nat.add_comm 1 k))).toContinuousLinearEquiv

def hyperplaneEmbedLinear (F : GraphFrame 1 (k+1)) :
    Components 1 k →L[ℂ] Components 1 (k+1) :=
  F.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((0 : Components 1 k →L[ℂ] GraphHorizontal 1).prod
      (verticalAmbientEquiv k).toContinuousLinearMap)

def hyperplaneProjectLinear (F : GraphFrame 1 (k+1)) :
    Components 1 (k+1) →L[ℂ] Components 1 k :=
  (verticalAmbientEquiv k).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.snd ℂ (GraphHorizontal 1) (GraphVertical (k+1))).comp
      F.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem hyperplaneEmbedLinear_coordinates (F : GraphFrame 1 (k+1))
    (v : Components 1 k) : F (hyperplaneEmbedLinear F v) = (0, verticalAmbientEquiv k v) :=
  F.apply_symm_apply _

@[simp] theorem hyperplaneProjectLinear_embed (F : GraphFrame 1 (k+1))
    (v : Components 1 k) : hyperplaneProjectLinear F (hyperplaneEmbedLinear F v) = v := by
  change (verticalAmbientEquiv k).symm (F (hyperplaneEmbedLinear F v)).2 = v
  simp

theorem hyperplaneEmbedLinear_project (F : GraphFrame 1 (k+1))
    (v : Components 1 (k+1)) (hv : (F v).1 = 0) :
    hyperplaneEmbedLinear F (hyperplaneProjectLinear F v) = v := by
  apply F.injective
  rw [hyperplaneEmbedLinear_coordinates]
  change (0, verticalAmbientEquiv k ((verticalAmbientEquiv k).symm (F v).2)) = F v
  exact Prod.ext hv.symm ((verticalAmbientEquiv k).apply_symm_apply _)

theorem hyperplaneEmbedLinear_injective (F : GraphFrame 1 (k+1)) :
    Function.Injective (hyperplaneEmbedLinear F) :=
  Function.LeftInverse.injective (hyperplaneProjectLinear_embed F)

def hyperplaneEmbedPoint (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k) :
    Grassmann 1 (k+1) :=
  projectiveLinearImage (hyperplaneEmbedLinear F) P
    ((hyperplaneEmbedLinear_injective F).comp Subtype.val_injective)

theorem hyperplaneEmbedPoint_ne_center (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k) :
    hyperplaneEmbedPoint F P ≠ graphPoint F 0 := by
  apply (verticalProjection_injective_iff F _).mp
  intro x y h
  obtain ⟨u, hu, hux⟩ := x.property
  obtain ⟨v, hv, hvy⟩ := y.property
  apply Subtype.ext
  change (F x.val).2 = (F y.val).2 at h
  rw [← hux, ← hvy] at h
  have huv : u = v := (verticalAmbientEquiv k).injective (by
    simpa only [ContinuousLinearMap.coe_coe, hyperplaneEmbedLinear_coordinates] using h)
  exact hux.symm.trans ((congrArg (hyperplaneEmbedLinear F) huv).trans hvy)

theorem hyperplaneEmbedPoint_horizontal (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k)
    (z : (hyperplaneEmbedPoint F P).val) : (F z.val).1 = 0 := by
  obtain ⟨u, hu, huz⟩ := z.property
  rw [← huz]
  exact congrArg Prod.fst (hyperplaneEmbedLinear_coordinates F u)

def hyperplaneEmbed (F : GraphFrame 1 (k+1)) :
    C(Grassmann 1 k, PunctureHyperplane F) where
  toFun P := ⟨⟨hyperplaneEmbedPoint F P, hyperplaneEmbedPoint_ne_center F P⟩,
    hyperplaneEmbedPoint_horizontal F P⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_projectiveLinearImage (fun _ => hyperplaneEmbedLinear F)
      (fun P : Grassmann 1 k => P) _ continuous_const continuous_id

theorem hyperplaneProjectLinear_injective (F : GraphFrame 1 (k+1))
    (P : PunctureHyperplane F) :
    Function.Injective ((hyperplaneProjectLinear F).toLinearMap.comp P.val.val.val.subtype) := by
  intro x y h
  apply (verticalProjection_injective_iff F P.val.val).mpr P.val.property
  exact (verticalAmbientEquiv k).symm.injective h

def hyperplaneProject (F : GraphFrame 1 (k+1)) :
    C(PunctureHyperplane F, Grassmann 1 k) where
  toFun P := projectiveLinearImage (hyperplaneProjectLinear F) P.val.val
    (hyperplaneProjectLinear_injective F P)
  continuous_toFun := continuous_projectiveLinearImage _ _ _ continuous_const
    (continuous_subtype_val.comp continuous_subtype_val)

theorem hyperplaneProject_embed (F : GraphFrame 1 (k+1)) (P : Grassmann 1 k) :
    hyperplaneProject F (hyperplaneEmbed F P) = P := by
  apply Subtype.ext
  change (P.val.map (hyperplaneEmbedLinear F).toLinearMap).map
    (hyperplaneProjectLinear F).toLinearMap = P.val
  rw [← Submodule.map_comp]
  have he : (hyperplaneProjectLinear F).toLinearMap.comp
      (hyperplaneEmbedLinear F).toLinearMap = LinearMap.id :=
    LinearMap.ext (hyperplaneProjectLinear_embed F)
  rw [he, Submodule.map_id]

theorem hyperplaneEmbed_project (F : GraphFrame 1 (k+1)) (P : PunctureHyperplane F) :
    hyperplaneEmbed F (hyperplaneProject F P) = P := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (P.val.val.val.map (hyperplaneProjectLinear F).toLinearMap).map
    (hyperplaneEmbedLinear F).toLinearMap = P.val.val.val
  rw [← Submodule.map_comp]
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    change hyperplaneEmbedLinear F (hyperplaneProjectLinear F v) ∈ P.val.val.val
    rw [hyperplaneEmbedLinear_project F v (P.property ⟨v, hv⟩)]
    exact hv
  · intro hz
    exact ⟨z, hz, hyperplaneEmbedLinear_project F z (P.property ⟨z, hz⟩)⟩

/-- The complementary hyperplane carries exactly the topology of CP^k. -/
def projectiveHyperplaneHomeomorph (F : GraphFrame 1 (k+1)) :
    PunctureHyperplane F ≃ₜ Grassmann 1 k where
  toFun := hyperplaneProject F
  invFun := hyperplaneEmbed F
  left_inv := hyperplaneEmbed_project F
  right_inv := hyperplaneProject_embed F
  continuous_toFun := (hyperplaneProject F).continuous
  continuous_invFun := (hyperplaneEmbed F).continuous

/-- CP^(k+1) minus a chart center is homotopy equivalent to CP^k. -/
def projectivePunctureLowerHomotopyEquiv (F : GraphFrame 1 (k+1)) :
    ProjectivePuncture F ≃ₕ Grassmann 1 k :=
  (punctureHyperplaneHomotopyEquiv F).trans (projectiveHyperplaneHomeomorph F).toHomotopyEquiv

/-- The puncture retraction theorem holds at any actual projective point. -/
def projectivePointPunctureLowerHomotopyEquiv (P : Grassmann 1 (k+1)) :
    ({P}ᶜ : Set (Grassmann 1 (k+1))) ≃ₕ Grassmann 1 k := by
  let F := (graph_charts_cover P.val P.property).choose
  have hF := (graph_charts_cover P.val P.property).choose_spec
  have hp : graphPoint F 0 = P := Subtype.ext hF
  exact (Homeomorph.setCongr (congrArg (fun Q => ({Q}ᶜ : Set (Grassmann 1 (k+1)))) hp.symm)).toHomotopyEquiv.trans
    (projectivePunctureLowerHomotopyEquiv F)

end ComplexGrassmann

end Kaplansky

end

end OAI
