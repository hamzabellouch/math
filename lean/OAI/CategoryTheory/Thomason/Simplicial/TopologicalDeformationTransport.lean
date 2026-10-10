import OAI.CategoryTheory.Thomason.Gray.SimplexCylinderGeneration
import OAI.CategoryTheory.Thomason.Simplicial.HomotopyFiberPathEquivalence
import OAI.CategoryTheory.Thomason.Simplicial.NonsingularFaceCarriers
import OAI.CategoryTheory.Thomason.Simplicial.RealizationSubcomplexSemantics
import OAI.CategoryTheory.Thomason.Simplicial.SingularPathSpaceAdjunction
import OAI.CategoryTheory.Thomason.Simplicial.SubdivisionFaceImages
import OAI.CategoryTheory.Thomason.Simplicial.TruncationQuotientComposition
import OAI.CategoryTheory.Thomason.Transfer.HornAttachmentWeakEquivalences
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.CategoryTheory.MorphismProperty.Retract

namespace OAI

section

/-! # Straightening a boundary homotopy with a specified square

The realized cylinder ends and side form a pushout. A homotopy of the
boundary path to a constant path, fixed at both ends, extends across that
pushout by the actual realization homotopy extension property.
-/

namespace Thomason.Construction.RealizationHomotopyRectification

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

def pathAt (X : TopCat.{0}) (t : unitInterval) : continuousPathSpace X ⟶ X :=
  TopCat.ofHom ⟨fun γ => γ t, continuous_eval_const t⟩

def constantPath (X : TopCat.{0}) : X ⟶ continuousPathSpace X :=
  TopCat.ofHom ⟨fun x => ContinuousMap.const _ x, by fun_prop⟩

@[reassoc] theorem constantPath_pathAt (X : TopCat.{0}) (t : unitInterval) :
    constantPath X ≫ pathAt X t = 𝟙 X := rfl

theorem cylinder_comparison {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X))
    (t : unitInterval) (x : SSet.toTop.obj K) :
    (cylinderRealizationMap H).hom ((RealizedCylinder.comparison K).hom (x, t)) =
      H (t, x) := by
  change H (_, _) = H (t, x)
  rw [RealizedCylinder.comparison_time, RealizedCylinder.comparison_first]

theorem cylinder_zero {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) :
    SSet.toTop.map SSet.ι₀ ≫ cylinderRealizationMap H =
      TopCat.ofHom ⟨fun x => H (0, x), by fun_prop⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (cylinderRealizationMap H).hom ((SSet.toTop.map SSet.ι₀).hom x) = H (0, x)
  rw [← RealizedCylinder.comparison_zero]
  exact cylinder_comparison H 0 x

theorem cylinder_one {K : SSet.{0}} {X : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) :
    SSet.toTop.map SSet.ι₁ ≫ cylinderRealizationMap H =
      TopCat.ofHom ⟨fun x => H (1, x), by fun_prop⟩ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change (cylinderRealizationMap H).hom ((SSet.toTop.map SSet.ι₁).hom x) = H (1, x)
  rw [← RealizedCylinder.comparison_one]
  exact cylinder_comparison H 1 x

/-- The two ends detect maps out of the actual realized interval boundary,
with an arbitrary simplicial parameter and arbitrary topological target. -/
theorem interval_boundary_hom_ext {K : SSet.{0}} {X : TopCat.{0}}
    (f g : SSet.toTop.obj (K ⊗ (SSet.boundary 1 : SSet.{0})) ⟶ X)
    (h₀ : SSet.toTop.map (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫ f =
      SSet.toTop.map (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫ g)
    (h₁ : SSet.toTop.map (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫ f =
      SSet.toTop.map (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫ g) : f = g := by
  apply (sSetTopAdj.homEquiv _ _).injective
  apply interval_boundary_tensor_hom_ext
  · simpa only [sSetTopAdj.homEquiv_naturality_left] using
      congrArg (sSetTopAdj.homEquiv _ _) h₀
  · simpa only [sSetTopAdj.homEquiv_naturality_left] using
      congrArg (sSetTopAdj.homEquiv _ _) h₁

theorem cylinder_postcomp {K : SSet.{0}} {X Y : TopCat.{0}}
    (H : C(unitInterval × SSet.toTop.obj K, X)) (p : X ⟶ Y) :
    cylinderRealizationMap (p.hom.comp H) = cylinderRealizationMap H ≫ p := rfl

theorem cylinder_boundary_congr {K : SSet.{0}} {X : TopCat.{0}}
    (H G : C(unitInterval × SSet.toTop.obj K, X))
    (h₀ : ∀ x, H (0, x) = G (0, x)) (h₁ : ∀ x, H (1, x) = G (1, x)) :
    SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫ cylinderRealizationMap H =
      SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫ cylinderRealizationMap G := by
  apply interval_boundary_hom_ext
  · have he (F : C(unitInterval × SSet.toTop.obj K, X)) :
        SSet.toTop.map (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫
          (SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫ cylinderRealizationMap F) =
        SSet.toTop.map (fst K (Δ[0] : SSet.{0})) ≫
          TopCat.ofHom ⟨fun x => F (0, x), by fun_prop⟩ := by
      rw [← Category.assoc, ← SSet.toTop.map_comp, ← whiskerLeft_comp,
        SSet.boundary.ι_ι, whisker_zero_face, SSet.toTop.map_comp, Category.assoc,
        cylinder_zero]
    rw [he H, he G]
    exact congrArg (SSet.toTop.map (fst K (Δ[0] : SSet.{0})) ≫ ·)
      (TopCat.hom_ext (ContinuousMap.ext h₀))
  · have he (F : C(unitInterval × SSet.toTop.obj K, X)) :
        SSet.toTop.map (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫
          (SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫ cylinderRealizationMap F) =
        SSet.toTop.map (fst K (Δ[0] : SSet.{0})) ≫
          TopCat.ofHom ⟨fun x => F (1, x), by fun_prop⟩ := by
      rw [← Category.assoc, ← SSet.toTop.map_comp, ← whiskerLeft_comp,
        SSet.boundary.ι_ι, whisker_one_face, SSet.toTop.map_comp, Category.assoc,
        cylinder_one]
    rw [he H, he G]
    exact congrArg (SSet.toTop.map (fst K (Δ[0] : SSet.{0})) ≫ ·)
      (TopCat.hom_ext (ContinuousMap.ext h₁))

/-- A path-valued deformation on the cylinder ends and side, initially
equal to the given homotopy, straightens its side at the final time. -/
theorem straighten_of_cylinder_deformation
    {K : SSet.{0}} (A : K.Subcomplex) {X : TopCat.{0}}
    (f g : SSet.toTop.obj K ⟶ X) (H : f.hom.Homotopy g.hom)
    (q : SSet.toTop.obj (A.unionProd (SSet.boundary 1)).toSSet ⟶ continuousPathSpace X)
    (hq₀ : q ≫ pathAt X 0 = SSet.toTop.map (A.unionProd (SSet.boundary 1)).ι ≫
      cylinderRealizationMap H.toContinuousMap)
    (hqend : SSet.toTop.map (SSet.Subcomplex.unionProd.ι₁ A (SSet.boundary 1)) ≫ q =
      SSet.toTop.map (K ◁ (SSet.boundary 1).ι) ≫
        cylinderRealizationMap H.toContinuousMap ≫ constantPath X)
    (hqside : SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A (SSet.boundary 1)) ≫
      q ≫ pathAt X 1 = SSet.toTop.map (fst A.toSSet Δ[1] ≫ A.ι) ≫ f) :
    Nonempty (f.hom.HomotopyRel g.hom (Set.range (SSet.toTop.map A.ι).hom)) := by
  let U := A.unionProd (SSet.boundary 1)
  let F := cylinderRealizationMap H.toContinuousMap
  let Q := continuousPathFamilyEquiv U.toSSet X q
  let q₁ : SSet.toTop.obj U.toSSet ⟶ X := q ≫ pathAt X 1
  let h : (SSet.toTop.map U.ι ≫ F).hom.Homotopy q₁.hom := {
    toContinuousMap := Q
    map_zero_left := by
      intro x
      exact congrArg (fun k => k.hom x) hq₀
    map_one_left := fun _ => rfl }
  obtain ⟨F', hF'₀, hF'U⟩ := realization_homotopy_extension U.ι F h
  let G : C(unitInterval × SSet.toTop.obj K, X) :=
    ⟨fun z => F' (1, (RealizedCylinder.comparison K).hom (z.2, z.1)),
      F'.continuous.comp (continuous_const.prodMk
        ((RealizedCylinder.comparison K).hom.continuous.comp continuous_swap))⟩
  have hend (t : unitInterval)
      (x : SSet.toTop.obj (K ⊗ (SSet.boundary 1 : SSet.{0}))) :
      F' (t, (SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom x) =
        F.hom ((SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom x) := by
    have hu := congrArg (fun k => k.hom x)
      (SSet.toTop.map_comp (SSet.Subcomplex.unionProd.ι₁ A (SSet.boundary 1)) U.ι)
    rw [SSet.Subcomplex.unionProd.ι₁_ι] at hu
    change (SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom x =
      (SSet.toTop.map U.ι).hom
        ((SSet.toTop.map (SSet.Subcomplex.unionProd.ι₁ A (SSet.boundary 1))).hom x) at hu
    rw [hu, hF'U]
    have hh := congrArg (fun k => (show C(unitInterval, X) from k.hom x) t) hqend
    change h (t, (SSet.toTop.map (SSet.Subcomplex.unionProd.ι₁ A (SSet.boundary 1))).hom x) =
      F.hom ((SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom x) at hh
    rw [hu] at hh
    exact hh
  have hside (t : unitInterval) (x : SSet.toTop.obj A.toSSet) :
      G (t, (SSet.toTop.map A.ι).hom x) = f.hom ((SSet.toTop.map A.ι).hom x) := by
    have hn := congrArg (fun k => k.hom (x, t)) (RealizedCylinder.comparison_naturality A.ι)
    change (RealizedCylinder.comparison K).hom ((SSet.toTop.map A.ι).hom x, t) =
      (SSet.toTop.map (A.ι ▷ Δ[1])).hom ((RealizedCylinder.comparison A.toSSet).hom (x, t)) at hn
    change F' (1, _) = _
    rw [hn]
    have hu := congrArg (fun k => k.hom ((RealizedCylinder.comparison A.toSSet).hom (x, t)))
      (SSet.toTop.map_comp (SSet.Subcomplex.unionProd.ι₂ A (SSet.boundary 1)) U.ι)
    rw [SSet.Subcomplex.unionProd.ι₂_ι] at hu
    change (SSet.toTop.map (A.ι ▷ Δ[1])).hom ((RealizedCylinder.comparison A.toSSet).hom (x, t)) =
      (SSet.toTop.map U.ι).hom
        ((SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A (SSet.boundary 1))).hom
          ((RealizedCylinder.comparison A.toSSet).hom (x, t))) at hu
    rw [hu, hF'U]
    have hh := congrArg (fun k => k.hom ((RealizedCylinder.comparison A.toSSet).hom (x, t))) hqside
    change (show C(unitInterval, X) from q.hom
      ((SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A (SSet.boundary 1))).hom
        ((RealizedCylinder.comparison A.toSSet).hom (x, t)))) 1 = _ at hh
    change (show C(unitInterval, X) from q.hom
      ((SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A (SSet.boundary 1))).hom
        ((RealizedCylinder.comparison A.toSSet).hom (x, t)))) 1 = _
    rw [hh, SSet.toTop.map_comp]
    change f.hom ((SSet.toTop.map A.ι).hom
      ((SSet.toTop.map (fst A.toSSet Δ[1])).hom ((RealizedCylinder.comparison A.toSSet).hom (x, t)))) = _
    rw [RealizedCylinder.comparison_first]
  have hend₀ (x : SSet.toTop.obj K) : G (0, x) = f.hom x := by
    change F' (1, _) = _
    rw [RealizedCylinder.comparison_zero]
    let z := (SSet.toTop.map (K ◁ SSet.boundary.ι (1 : Fin 2))).hom
      ((SSet.toTop.map (zeroFaceSection K)).hom x)
    have hz : (SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom z =
        (SSet.toTop.map SSet.ι₀).hom x := by
      change ((SSet.toTop.map (zeroFaceSection K) ≫
        SSet.toTop.map (K ◁ SSet.boundary.ι (1 : Fin 2))) ≫
        SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom x = _
      rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, Category.assoc,
        ← whiskerLeft_comp, SSet.boundary.ι_ι, zeroFaceSection_face]
    rw [← hz, hend, hz]
    exact (cylinder_zero H.toContinuousMap |> congrArg (fun k => k.hom x)).trans
      (H.map_zero_left x)
  have hend₁ (x : SSet.toTop.obj K) : G (1, x) = g.hom x := by
    change F' (1, _) = _
    rw [RealizedCylinder.comparison_one]
    let z := (SSet.toTop.map (K ◁ SSet.boundary.ι (0 : Fin 2))).hom
      ((SSet.toTop.map (zeroFaceSection K)).hom x)
    have hz : (SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom z =
        (SSet.toTop.map SSet.ι₁).hom x := by
      change ((SSet.toTop.map (zeroFaceSection K) ≫
        SSet.toTop.map (K ◁ SSet.boundary.ι (0 : Fin 2))) ≫
        SSet.toTop.map (K ◁ (SSet.boundary 1).ι)).hom x = _
      rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, Category.assoc,
        ← whiskerLeft_comp, SSet.boundary.ι_ι, whisker_one_face,
        ← Category.assoc, zeroFaceSection_fst, Category.id_comp]
    rw [← hz, hend, hz]
    exact (cylinder_one H.toContinuousMap |> congrArg (fun k => k.hom x)).trans
      (H.map_one_left x)
  exact ⟨{
    toHomotopy := { toContinuousMap := G, map_zero_left := hend₀, map_one_left := hend₁ }
    prop' := by
      intro t x hx
      obtain ⟨a, rfl⟩ := hx
      exact hside t a }⟩

/-- Restriction of a continuous homotopy to a realized simplicial subobject. -/
def restriction {K : SSet.{0}} (A : K.Subcomplex) {X : TopCat.{0}}
    {f g : SSet.toTop.obj K ⟶ X} (H : f.hom.Homotopy g.hom) :
    C(unitInterval × SSet.toTop.obj A.toSSet, X) :=
  H.toContinuousMap.comp ⟨fun z => (z.1, (SSet.toTop.map A.ι).hom z.2), by fun_prop⟩

def constantSide {K : SSet.{0}} (A : K.Subcomplex) {X : TopCat.{0}}
    (f : SSet.toTop.obj K ⟶ X) : C(unitInterval × SSet.toTop.obj A.toSSet, X) :=
  ⟨fun z => f.hom ((SSet.toTop.map A.ι).hom z.2), by fun_prop⟩

/-- A square from the boundary path to the constant path, with its two
ends fixed, straightens the full homotopy relative to that boundary. -/
theorem straighten {K : SSet.{0}} (A : K.Subcomplex) {X : TopCat.{0}}
    (f g : SSet.toTop.obj K ⟶ X) (H : f.hom.Homotopy g.hom)
    (D : (restriction A H).HomotopyRel (constantSide A f)
      {z | z.1 = 0 ∨ z.1 = 1}) :
    Nonempty (f.hom.HomotopyRel g.hom (Set.range (SSet.toTop.map A.ι).hom)) := by
  let T : (Δ[1] : SSet.{0}).Subcomplex := SSet.boundary 1
  let U := A.unionProd T
  let sq := (SSet.Subcomplex.unionProd.isPushout A T).map SSet.toTop
  let F := cylinderRealizationMap H.toContinuousMap
  let R := restriction A H
  let W : C(unitInterval × SSet.toTop.obj A.toSSet, continuousPathSpace X) :=
    (D.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let w := cylinderRealizationMap W
  let c := SSet.toTop.map (K ◁ T.ι) ≫ F ≫ constantPath X
  have hn : A.ι ▷ T.toSSet ≫ K ◁ T.ι = A.toSSet ◁ T.ι ≫ A.ι ▷ Δ[1] := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hr : SSet.toTop.map (A.ι ▷ Δ[1]) ≫ F = cylinderRealizationMap R :=
    cylinderRealizationMap_naturality A.ι H.toContinuousMap
  have hb : SSet.toTop.map (A.toSSet ◁ T.ι) ≫
      (cylinderRealizationMap R ≫ constantPath X) =
      SSet.toTop.map (A.toSSet ◁ T.ι) ≫ w := by
    rw [← cylinder_postcomp]
    apply cylinder_boundary_congr
    · intro x
      apply ContinuousMap.ext
      intro s
      exact (D.prop s (0, x) (Or.inl rfl)).symm
    · intro x
      apply ContinuousMap.ext
      intro s
      exact (D.prop s (1, x) (Or.inr rfl)).symm
  have hc : SSet.toTop.map (A.ι ▷ T.toSSet) ≫ c =
      SSet.toTop.map (A.toSSet ◁ T.ι) ≫ w := by
    dsimp only [c]
    rw [← Category.assoc, ← SSet.toTop.map_comp, hn, SSet.toTop.map_comp,
      Category.assoc, ← Category.assoc (SSet.toTop.map (A.ι ▷ Δ[1])), hr]
    exact hb
  let q := sq.desc c w hc
  have hqc : SSet.toTop.map (SSet.Subcomplex.unionProd.ι₁ A T) ≫ q = c :=
    sq.inl_desc c w hc
  have hqw : SSet.toTop.map (SSet.Subcomplex.unionProd.ι₂ A T) ≫ q = w :=
    sq.inr_desc c w hc
  have hw₀ : w ≫ pathAt X 0 = cylinderRealizationMap R := by
    rw [← cylinder_postcomp]
    congr 1
    apply ContinuousMap.ext
    intro z
    exact D.map_zero_left z
  have hw₁ : w ≫ pathAt X 1 = SSet.toTop.map (fst A.toSSet Δ[1] ≫ A.ι) ≫ f := by
    rw [← cylinder_postcomp]
    have hd : (pathAt X 1).hom.comp W = constantSide A f := by
      apply ContinuousMap.ext
      intro z
      exact D.map_one_left z
    rw [hd]
    rw [SSet.toTop.map_comp]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  apply straighten_of_cylinder_deformation A f g H q
  · apply sq.hom_ext
    · rw [← Category.assoc, hqc]
      dsimp only [c]
      rw [Category.assoc, Category.assoc, constantPath_pathAt, Category.comp_id]
      rw [← Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.unionProd.ι₁_ι]
    · rw [← Category.assoc, hqw, hw₀, ← hr]
      rw [← Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.unionProd.ι₂_ι]
  · exact hqc
  · rw [← Category.assoc, hqw, hw₁]

end

end Thomason.Construction.RealizationHomotopyRectification

end

section

/-! # Boundary-square rectification along any simplicial monomorphism -/

namespace Thomason.Construction.RealizationHomotopyRectification

open CategoryTheory

noncomputable section

def restrictionAlong {A K : SSet.{0}} (i : A ⟶ K) {X : TopCat.{0}}
    {f g : SSet.toTop.obj K ⟶ X} (H : f.hom.Homotopy g.hom) :
    C(unitInterval × SSet.toTop.obj A, X) :=
  H.toContinuousMap.comp ⟨fun z => (z.1, (SSet.toTop.map i).hom z.2), by fun_prop⟩

def constantSideAlong {A K : SSet.{0}} (i : A ⟶ K) {X : TopCat.{0}}
    (f : SSet.toTop.obj K ⟶ X) : C(unitInterval × SSet.toTop.obj A, X) :=
  ⟨fun z => f.hom ((SSet.toTop.map i).hom z.2), by fun_prop⟩

/-- Passing through the actual range removes the literal-subcomplex
restriction from boundary-square rectification. -/
theorem straighten_mono {A K : SSet.{0}} (i : A ⟶ K) [Mono i] {X : TopCat.{0}}
    (f g : SSet.toTop.obj K ⟶ X) (H : f.hom.Homotopy g.hom)
    (D : (restrictionAlong i H).HomotopyRel (constantSideAlong i f)
      {z | z.1 = 0 ∨ z.1 = 1}) :
    Nonempty (f.hom.HomotopyRel g.hom (Set.range (SSet.toTop.map i).hom)) := by
  let R := SSet.Subcomplex.range i
  let q : A ⟶ R.toSSet := SSet.Subcomplex.toRange i
  let r : R.toSSet ⟶ A := inv q
  have hq : q ≫ R.ι = i := SSet.Subcomplex.toRange_ι i
  have hr : r ≫ i = R.ι := by
    rw [← hq, ← Category.assoc]
    change (inv q ≫ q) ≫ R.ι = R.ι
    rw [IsIso.inv_hom_id, Category.id_comp]
  have hpoint (x : SSet.toTop.obj R.toSSet) :
      (SSet.toTop.map i).hom ((SSet.toTop.map r).hom x) =
        (SSet.toTop.map R.ι).hom x := by
    have h := congrArg (fun k => (SSet.toTop.map k).hom x) hr
    rw [SSet.toTop.map_comp] at h
    exact h
  let D' : (restriction R H).HomotopyRel (constantSide R f)
      {z | z.1 = 0 ∨ z.1 = 1} := {
    toHomotopy := {
      toContinuousMap := ⟨fun z => D (z.1, (z.2.1, (SSet.toTop.map r).hom z.2.2)), by
        exact D.continuous.comp (continuous_fst.prodMk
          (continuous_snd.fst.prodMk
            ((SSet.toTop.map r).hom.continuous.comp continuous_snd.snd)))⟩
      map_zero_left := by
        intro z
        change D (0, (z.1, (SSet.toTop.map r).hom z.2)) = H (z.1, _)
        exact (D.map_zero_left _).trans (by
          change H (z.1, (SSet.toTop.map i).hom ((SSet.toTop.map r).hom z.2)) = _
          rw [hpoint])
      map_one_left := by
        intro z
        change D (1, (z.1, (SSet.toTop.map r).hom z.2)) = f.hom _
        exact (D.map_one_left _).trans (by
          change f.hom ((SSet.toTop.map i).hom ((SSet.toTop.map r).hom z.2)) = _
          rw [hpoint]) }
    prop' := by
      intro s z hz
      change D (s, (z.1, (SSet.toTop.map r).hom z.2)) = H (z.1, _)
      exact (D.prop s _ hz).trans (by
        change H (z.1, (SSet.toTop.map i).hom ((SSet.toTop.map r).hom z.2)) = _
        rw [hpoint]) }
  obtain ⟨G⟩ := straighten R f g H D'
  refine ⟨{ toHomotopy := G.toHomotopy, prop' := ?_ }⟩
  intro t x hx
  apply G.prop t
  obtain ⟨a, rfl⟩ := hx
  refine ⟨(SSet.toTop.map q).hom a, ?_⟩
  have h := congrArg (fun k => (SSet.toTop.map k).hom a) hq
  rw [SSet.toTop.map_comp] at h
  exact h

end

end Thomason.Construction.RealizationHomotopyRectification

end

section

/-! # Straight interpolation on the actual realized standard simplex -/

namespace Thomason.Construction

open CategoryTheory Convexity
open scoped Simplicial

noncomputable section

/-- Convex interpolation in the barycentric coordinates of a standard simplex. -/
def simplexPointInterpolation (n : ℕ) :
    C(unitInterval × (SSet.toTop.obj (Δ[n] : SSet.{0}) ×
      SSet.toTop.obj (Δ[n] : SSet.{0})), SSet.toTop.obj (Δ[n] : SSet.{0})) :=
  (⟨(HornBarycentric.simplexHomeomorph n).symm,
    (HornBarycentric.simplexHomeomorph n).symm.continuous⟩ : C(_, _)).comp
    ⟨fun z => convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
      (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
      (HornBarycentric.simplexHomeomorph n z.2.1)
      (HornBarycentric.simplexHomeomorph n z.2.2), by
      rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
      apply continuous_pi
      intro k
      simp only [Function.comp_def, StdSimplex.weights_convexCombPair,
        Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, unitInterval.coe_symm_eq]
      fun_prop⟩

@[simp]
theorem simplexPointInterpolation_zero (n : ℕ) (x y : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    simplexPointInterpolation n (0, x, y) = x := by
  apply (HornBarycentric.simplexHomeomorph n).injective
  change (HornBarycentric.simplexHomeomorph n)
    ((HornBarycentric.simplexHomeomorph n).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  ext k
  simp

@[simp]
theorem simplexPointInterpolation_one (n : ℕ) (x y : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    simplexPointInterpolation n (1, x, y) = y := by
  apply (HornBarycentric.simplexHomeomorph n).injective
  change (HornBarycentric.simplexHomeomorph n)
    ((HornBarycentric.simplexHomeomorph n).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  ext k
  simp

@[simp]
theorem simplexPointInterpolation_diagonal (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (Δ[n] : SSet.{0})) : simplexPointInterpolation n (t, x, x) = x := by
  apply (HornBarycentric.simplexHomeomorph n).injective
  change (HornBarycentric.simplexHomeomorph n)
    ((HornBarycentric.simplexHomeomorph n).symm _) = _
  rw [Homeomorph.apply_symm_apply]
  ext k
  change (convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (HornBarycentric.simplexHomeomorph n x) (HornBarycentric.simplexHomeomorph n x)).weights k = _
  simp only [StdSimplex.weights_convexCombPair, Finsupp.coe_add, Finsupp.coe_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitInterval.coe_symm_eq]
  ring

/-- The projection of the genuine homotopy fibre over a geometric simplex
is a homotopy equivalence, for any continuous map into that simplex. -/
def simplexHomotopyFiberEquiv {X : TopCat.{0}} (n : ℕ)
    (p : X ⟶ SSet.toTop.obj (Δ[n] : SSet.{0})) (b : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    ContinuousMap.HomotopyEquiv (continuousHomotopyFiber p b) X :=
  continuousHomotopyFiberEquiv p b (simplexPointInterpolation n)
    (simplexPointInterpolation_zero n) (simplexPointInterpolation_one n)
    (simplexPointInterpolation_diagonal n)

end

end Thomason.Construction

end

section

/-! # Relative homotopies between paths in a barycentric simplex -/

namespace Thomason.Construction

open Convexity

noncomputable section

/-- Linear interpolation between two barycentric paths fixes their common
endpoints. This is the path-level triangle compatibility used in realization. -/
def barycentricPathHomotopy {n : ℕ} {x y : StdSimplex ℝ (Fin (n+1))}
    (p q : Path x y) : p.Homotopy q where
  toFun z := convexCombPair (R := ℝ) (unitInterval.symm z.1) z.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p z.2) (q z.2)
  continuous_toFun := by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
    apply continuous_pi
    intro j
    simp only [Function.comp_def, StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, unitInterval.coe_symm_eq]
    fun_prop
  map_zero_left s := by ext j; simp
  map_one_left s := by ext j; simp
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s
      change convexCombPair (R := ℝ) (unitInterval.symm t) t
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p 0) (q 0) = p 0
      rw [p.source, q.source]
      ext j
      simp only [StdSimplex.weights_convexCombPair,
        Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, unitInterval.coe_symm_eq]
      ring
    · rw [Set.mem_singleton_iff] at hs
      subst s
      change convexCombPair (R := ℝ) (unitInterval.symm t) t
        (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp) (p 1) (q 1) = p 1
      rw [p.target, q.target]
      ext j
      simp only [StdSimplex.weights_convexCombPair,
        Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, unitInterval.coe_symm_eq]
      ring

/-- The image of the standard interval inside a barycentric simplex along
any ordinal edge. -/
def barycentricEdge {n : ℕ} (f : Fin 2 →o Fin (n+1)) :
    Path (StdSimplex.single (f 0) : StdSimplex ℝ (Fin (n+1))) (StdSimplex.single (f 1)) where
  toFun t := StdSimplex.map f (StdSimplex.homeomorphI.symm t)
  continuous_toFun := by fun_prop
  source' := by rw [StdSimplex.homeomorphI_symm_zero, StdSimplex.map_single]
  target' := by rw [StdSimplex.homeomorphI_symm_one, StdSimplex.map_single]

end

end Thomason.Construction

end

section

/-! # Literal fibres of a product over a contractible base -/

namespace Thomason.Construction

open CategoryTheory
open scoped Simplicial

noncomputable section

def continuousProductProjection (X B : TopCat.{0}) : TopCat.of (X × B) ⟶ B :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- Interpolation in the base makes each literal product fibre a
homotopy-equivalent subspace of the entire product. -/
def continuousProductFiberEquiv (X B : TopCat.{0}) (b : B)
    (c : C(unitInterval × (B × B), B))
    (h₀ : ∀ x y, c (0,x,y) = x) (h₁ : ∀ x y, c (1,x,y) = y) :
    ContinuousMap.HomotopyEquiv
      (continuousFiber (continuousProductProjection X B) b) (TopCat.of (X × B)) where
  toFun := (continuousFiberInclusion (continuousProductProjection X B) b).hom
  invFun := ⟨fun x => ⟨(x.1,b), rfl⟩, by fun_prop⟩
  left_inv := ⟨{
    toFun z := z.2
    continuous_toFun := continuous_snd
    map_zero_left x := by
      apply Subtype.ext
      exact Prod.ext rfl x.property
    map_one_left _ := rfl }⟩
  right_inv := ⟨{
    toFun z := (z.2.1, c (z.1,b,z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left x := by
      change (x.1, c (0,b,x.2)) = (x.1,b)
      rw [h₀]
    map_one_left x := by
      change (x.1, c (1,b,x.2)) = x
      rw [h₁] }⟩

/-- In particular, the inclusion of any fibre over a realized simplex is
an actual weak homotopy equivalence, without any Kan hypothesis. -/
theorem continuousProductSimplexFiberInclusion_weak (X : TopCat.{0}) (n : ℕ)
    (b : SSet.toTop.obj (Δ[n] : SSet.{0})) :
    topologicalWeakEquivalences (continuousFiberInclusion
      (continuousProductProjection X (SSet.toTop.obj (Δ[n] : SSet.{0}))) b) :=
  homotopyEquiv_isWeakHomotopyEquivalence
    (continuousProductFiberEquiv X _ b (simplexPointInterpolation n)
      (simplexPointInterpolation_zero n) (simplexPointInterpolation_one n))

end

end Thomason.Construction

end

section

/-! # Actual path spaces preserve singular Kan fibrations -/

namespace Thomason.Construction

open CategoryTheory
open SSet.modelCategoryQuillen

noncomputable section

/-- The natural internal-hom comparison transports the proved simplicial
pushout-product theorem to the actual compact-open path space. -/
theorem singularPathMap_fibration {X Y : TopCat.{0}} (p : X ⟶ Y)
    [HomotopicalAlgebra.Fibration (TopCat.toSSet.map p)] :
    HomotopicalAlgebra.Fibration (TopCat.toSSet.map (continuousPathMap p)) := by
  rw [fibration_iff]
  intro A B i hi
  apply (HasLiftingProperty.iff_of_arrow_iso_right i (singularPathMapArrowIso p)).mpr
  exact ((fibration_iff _).mp (inferInstance : HomotopicalAlgebra.Fibration
    ((ihom (SSet.stdSimplex.obj (SimplexCategory.mk 1))).map (TopCat.toSSet.map p)))) i hi

end

end Thomason.Construction

end

section

/-! # Face inclusions under the actual subdivision functor -/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

noncomputable section

/-- The actual inclusion of a subdivided face into the finite-chain nerve. -/
def subdividedFaceMap {n : ℕ} (S : Finset (Fin (n + 1))) :
    SSet.sd.obj (SSet.stdSimplex.face S : SSet.{0}) ⟶ SimplexCategory.sd.obj ⦋n⦌ :=
  SSet.sd.map (SSet.stdSimplex.face S).ι ≫ SSet.stdSimplex.sdIso.hom.app ⦋n⦌

/-- The full chain subcomplex supported on the original face vertices. -/
def subdividedFace {n : ℕ} (S : Finset (Fin (n + 1))) :
    (SimplexCategory.sd.obj ⦋n⦌).Subcomplex :=
  fullSubposetComplex (chainsSupported (Set.ofPred (fun x : ULift.{0} (Fin (n+1)) => x.down ∈ S)))

def faceOrdinalMap {n m : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o S) : ⦋m⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)

instance faceOrdinalMap_mono {n m : ℕ} (S : Finset (Fin (n+1)))
    (e : Fin (m+1) ≃o S) : Mono (faceOrdinalMap S e) := by
  rw [SimplexCategory.mono_iff_injective]
  intro i j h
  exact e.injective (Subtype.ext h)

theorem faceIso_inclusion {n m : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o S) :
    (SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)).hom ≫
      (SSet.stdSimplex.face S).ι = SSet.stdSimplex.map (faceOrdinalMap S e) := by
  ext d x
  rfl

theorem subdividedFaceMap_fac {n m : ℕ} (S : Finset (Fin (n + 1)))
    (e : Fin (m + 1) ≃o S) :
    SSet.sd.map
        (SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)).hom ≫
      subdividedFaceMap S =
        SSet.stdSimplex.sdIso.hom.app ⦋m⦌ ≫ SimplexCategory.sd.map (faceOrdinalMap S e) := by
  rw [subdividedFaceMap, ← Category.assoc, ← SSet.sd.map_comp, faceIso_inclusion]
  exact SSet.stdSimplex.sdIso.hom.naturality (faceOrdinalMap S e)

theorem faceOrdinalMap_range {n m : ℕ} (S : Finset (Fin (n+1)))
    (e : Fin (m+1) ≃o S) :
    Set.range (fun x : ULift.{0} (Fin (m+1)) =>
        (ULift.up ((faceOrdinalMap S e).toOrderHom x.down) : ULift.{0} (Fin (n+1)))) =
      {x | x.down ∈ S} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i.down).property
  · intro hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x.down, hx⟩
    refine ⟨ULift.up i, ?_⟩
    apply ULift.ext
    exact congrArg Subtype.val hi

/-- Subdivision preserves every face inclusion, including arbitrary codimension. -/
theorem subdividedFaceMap_mono {n : ℕ} (S : Finset (Fin (n+1))) :
    Mono (subdividedFaceMap S) := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
    let e := monoEquivOfFin S (by simpa using hm)
    have := simplexSubdivision_map_mono (faceOrdinalMap S e)
    have hcomp := subdividedFaceMap_fac S e
    have : Mono (SSet.sd.map
        (SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)).hom ≫
        subdividedFaceMap S) := by
      rw [hcomp]
      infer_instance
    let u := SSet.sd.map
      (SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)).hom
    have hh : Mono (inv u ≫ (u ≫ subdividedFaceMap S)) := inferInstance
    simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using hh
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst S
    have hi : IsInitial (SSet.stdSimplex.face (∅ : Finset (Fin (n+1))) : SSet.{0}) := by
      simpa using (SSet.Subcomplex.isInitialBot (X := (Δ[n] : SSet.{0})))
    have hj := IsInitial.isInitialObj SSet.sd _ hi
    rw [NatTrans.mono_iff_mono_app]
    intro d
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro x y _
    have ht := IsInitial.isInitialObj (SSet.evaluation.obj d) _ hj
    exact (((Types.initial_iff_empty _).mp ⟨ht⟩).false x).elim

/-- Exact range: every chain is supported on the original face and every such
chain simplex lifts, in every simplicial dimension. -/
theorem subdividedFaceMap_range {n : ℕ} (S : Finset (Fin (n+1))) :
    SSet.Subcomplex.range (subdividedFaceMap S) = subdividedFace S := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
    let e := monoEquivOfFin S (by simpa using hm)
    let u := SSet.sd.map
      (SSet.stdSimplex.isoOfRepresentableBy (SSet.stdSimplex.faceRepresentableBy S m e)).hom
    have hleft : SSet.Subcomplex.range (u ≫ subdividedFaceMap S) =
        SSet.Subcomplex.range (subdividedFaceMap S) := by
      rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
        SSet.Subcomplex.image_top]
    have hright : SSet.Subcomplex.range
        (SSet.stdSimplex.sdIso.hom.app ⦋m⦌ ≫ SimplexCategory.sd.map (faceOrdinalMap S e)) =
        SSet.Subcomplex.range (SimplexCategory.sd.map (faceOrdinalMap S e)) := by
      rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
        SSet.Subcomplex.image_top]
    rw [← hleft, subdividedFaceMap_fac S e, hright, simplexSubdivision_map_range,
      faceOrdinalMap_range]
    rfl
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst S
    have hi : IsInitial (SSet.stdSimplex.face (∅ : Finset (Fin (n+1))) : SSet.{0}) := by
      simpa using (SSet.Subcomplex.isInitialBot (X := (Δ[n] : SSet.{0})))
    have hj := IsInitial.isInitialObj SSet.sd _ hi
    ext d s
    constructor
    · rintro ⟨x, _⟩
      have ht := IsInitial.isInitialObj (SSet.evaluation.obj d) _ hj
      have he := (Types.initial_iff_empty _).mp ⟨ht⟩
      exact (he.false x).elim
    · intro h
      obtain ⟨x, hx⟩ := (s.obj 0).nonempty
      have hf := h 0 x hx
      change x.down ∈ (∅ : Finset (Fin (n+1))) at hf
      exact (Finset.notMem_empty x.down hf).elim

theorem subdividedFace_inter {n : ℕ} (S T : Finset (Fin (n+1))) :
    subdividedFace S ⊓ subdividedFace T = subdividedFace (S ∩ T) := by
  ext d s
  constructor
  · rintro ⟨hs, ht⟩ i x hx
    exact Finset.mem_inter.mpr ⟨hs i x hx, ht i x hx⟩
  · intro h
    exact ⟨fun i x hx => (Finset.mem_inter.mp (h i x hx)).1,
      fun i x hx => (Finset.mem_inter.mp (h i x hx)).2⟩

@[simp]
theorem subdividedFace_empty (n : ℕ) :
    subdividedFace (∅ : Finset (Fin (n+1))) = ⊥ := by
  apply bot_unique
  intro d s h
  obtain ⟨x, hx⟩ := (s.obj 0).nonempty
  have hf := h 0 x hx
  change x.down ∈ (∅ : Finset (Fin (n+1))) at hf
  exact (Finset.notMem_empty x.down hf).elim

end

end Thomason.Construction

end

section

/-! # Coproducts of stationary deformations

This supplies simultaneous horn attachments, the stages used in the
countable small-object factorization.
-/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {α : Type} (A B : α → TopCat.{0}) (i : ∀ a, A a ⟶ B a) (d : ∀ a, Data (i a))

def coproductRetraction : (∐ B) ⟶ ∐ A :=
  Sigma.desc (fun a => (d a).retraction ≫ Sigma.ι A a)

@[reassoc]
theorem coproductRetraction_fac (a : α) :
    Sigma.ι B a ≫ coproductRetraction A B i d = (d a).retraction ≫ Sigma.ι A a :=
  Sigma.ι_comp_desc _ a

theorem coproductRetraction_left :
    CategoryTheory.Limits.Sigma.map i ≫ coproductRetraction A B i d = 𝟙 (∐ A) := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, Sigma.ι_map, Category.assoc, coproductRetraction_fac,
    ← Category.assoc, (d a).left_inv, Category.id_comp, Category.comp_id]

/-- Assemble the tracks using preservation of coproducts by the interval cylinder. -/
def coproductTrack : TopologicalInterval.cylinder.obj (∐ B) ⟶ ∐ B :=
  (isColimitOfPreserves TopologicalInterval.cylinder (coproductIsCoproduct B)).desc {
    pt := ∐ B
    ι := Discrete.natTrans (fun a => (d a.as).track ≫ Sigma.ι B a.as) }

@[reassoc]
theorem coproductTrack_fac (a : α) :
    TopologicalInterval.cylinder.map (Sigma.ι B a) ≫ coproductTrack A B i d =
      (d a).track ≫ Sigma.ι B a :=
  (isColimitOfPreserves TopologicalInterval.cylinder (coproductIsCoproduct B)).fac _ ⟨a⟩

theorem coproductTrack_zero :
    TopologicalInterval.sectionAt (∐ B) 0 ≫ coproductTrack A B i d =
      coproductRetraction A B i d ≫ CategoryTheory.Limits.Sigma.map i := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, section_naturality, Category.assoc, coproductTrack_fac,
    ← Category.assoc, (d a).track_zero, Category.assoc]
  rw [← Category.assoc (Sigma.ι B a), coproductRetraction_fac, Category.assoc, Sigma.ι_map]

theorem coproductTrack_one :
    TopologicalInterval.sectionAt (∐ B) 1 ≫ coproductTrack A B i d = 𝟙 (∐ B) := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, section_naturality, Category.assoc, coproductTrack_fac,
    ← Category.assoc, (d a).track_one, Category.id_comp, Category.comp_id]

theorem coproductTrack_stationary :
    TopologicalInterval.cylinder.map (CategoryTheory.Limits.Sigma.map i) ≫ coproductTrack A B i d =
      TopologicalInterval.projection (∐ A) ≫ CategoryTheory.Limits.Sigma.map i := by
  apply (isColimitOfPreserves TopologicalInterval.cylinder (coproductIsCoproduct A)).hom_ext
  intro a
  change TopologicalInterval.cylinder.map (Sigma.ι A a.as) ≫ _ =
    TopologicalInterval.cylinder.map (Sigma.ι A a.as) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, Sigma.ι_map, Functor.map_comp,
    Category.assoc, coproductTrack_fac, ← Category.assoc, (d a.as).track_stationary]
  have hn : TopologicalInterval.cylinder.map (Sigma.ι A a.as) ≫
      TopologicalInterval.projection (∐ A) =
      TopologicalInterval.projection (A a.as) ≫ Sigma.ι A a.as := rfl
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Sigma.ι_map]

/-- A whole coproduct of relative deformations remains a relative deformation. -/
def coproductData : Data (CategoryTheory.Limits.Sigma.map i) where
  retraction := coproductRetraction A B i d
  left_inv := coproductRetraction_left A B i d
  homotopy := {
    toFun := fun p => (coproductTrack A B i d).hom (p.2, p.1)
    continuous_toFun := (coproductTrack A B i d).hom.continuous.comp (by fun_prop)
    map_zero_left := fun x => congrArg (fun f => f.hom x) (coproductTrack_zero A B i d)
    map_one_left := fun x => congrArg (fun f => f.hom x) (coproductTrack_one A B i d)
    prop' := by
      intro t y hy
      obtain ⟨x, rfl⟩ := hy
      have ht := congrArg (fun f => f.hom (x, t)) (coproductTrack_stationary A B i d)
      have hr := congrArg (fun f => f.hom x) (coproductRetraction_left A B i d)
      exact ht.trans (congrArg (CategoryTheory.Limits.Sigma.map i).hom hr).symm }

end

end Thomason.Construction.TopologicalDeformation

end

section

/-! # Stationary deformations descend through arrow retracts -/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory

noncomputable section

variable {A B C D : TopCat.{0}} {f : A ⟶ B} {g : C ⟶ D}

/-- The retraction obtained by traversing the given arrow retract. -/
def Data.retractMap (e : Data g) (r : RetractArrow f g) : B ⟶ A :=
  r.i.right ≫ e.retraction ≫ r.r.left

@[reassoc]
theorem Data.retractMap_left (e : Data g) (r : RetractArrow f g) :
    f ≫ e.retractMap r = 𝟙 A := by
  change f ≫ (r.i.right ≫ e.retraction ≫ r.r.left) = _
  rw [← Category.assoc, ← Category.assoc, ← r.i_w]
  rw [Category.assoc r.i.left g e.retraction, e.left_inv]
  exact (congrArg (fun k => k ≫ r.r.left) (Category.comp_id r.i.left)).trans r.retract_left

/-- An arrow retract of a stationary deformation inclusion is again one. -/
def Data.ofRetract (e : Data g) (r : RetractArrow f g) : Data f where
  retraction := e.retractMap r
  left_inv := e.retractMap_left r
  homotopy := {
    toFun := fun p => r.r.right.hom (e.homotopy (p.1, r.i.right.hom p.2))
    continuous_toFun := r.r.right.hom.continuous.comp
      (e.homotopy.continuous.comp (by fun_prop))
    map_zero_left := by
      intro x
      change r.r.right.hom (e.homotopy (0, r.i.right.hom x)) = _
      refine (congrArg r.r.right.hom (e.homotopy.map_zero_left (r.i.right.hom x))).trans ?_
      exact congrArg (fun q => q.hom (e.retraction.hom (r.i.right.hom x))) r.r_w.symm
    map_one_left := by
      intro x
      change r.r.right.hom (e.homotopy (1, r.i.right.hom x)) = x
      exact (congrArg r.r.right.hom (e.homotopy.map_one_left (r.i.right.hom x))).trans
        (congrArg (fun q => q.hom x) r.retract_right)
    prop' := by
      intro t y hy
      obtain ⟨x, rfl⟩ := hy
      have hw : r.i.right.hom (f.hom x) = g.hom (r.i.left.hom x) :=
        congrArg (fun q => q.hom x) r.i_w.symm
      change r.r.right.hom (e.homotopy (t, r.i.right.hom (f.hom x))) = _
      rw [hw]
      have hs := e.homotopy.eq_snd t (Set.mem_range_self (r.i.left.hom x))
      change e.homotopy (t, g.hom (r.i.left.hom x)) = g.hom (r.i.left.hom x) at hs
      rw [hs]
      have hr : (e.retractMap r ≫ f).hom (f.hom x) = f.hom x := by
        have he : f ≫ (e.retractMap r ≫ f) = f := by
          rw [← Category.assoc, e.retractMap_left r, Category.id_comp]
        exact congrArg (fun q => q.hom x) he
      refine (show r.r.right.hom (g.hom (r.i.left.hom x)) = f.hom x from ?_).trans hr.symm
      rw [← hw]
      exact congrArg (fun q => q.hom (f.hom x)) r.retract_right }

end

end Thomason.Construction.TopologicalDeformation

end

section

/-! # Transporting stationary deformation data across actual isomorphisms -/

namespace Thomason.Construction.TopologicalDeformation

open CategoryTheory

noncomputable section

variable {A B A' B' : TopCat.{0}} {i : A ⟶ B}

/-- Change coordinates in both the retract and its ambient space. -/
def Data.conjugate (d : Data i) (a : A ≅ A') (b : B ≅ B') :
    Data (a.inv ≫ i ≫ b.hom) where
  retraction := b.inv ≫ d.retraction ≫ a.hom
  left_inv := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc i d.retraction, d.left_inv]
    simp
  homotopy := {
    toFun := fun p => b.hom.hom (d.homotopy (p.1, b.inv.hom p.2))
    continuous_toFun := b.hom.hom.continuous.comp
      (d.homotopy.continuous.comp (by fun_prop))
    map_zero_left := by
      intro x
      change b.hom.hom (d.homotopy (0, b.inv.hom x)) = _
      refine (congrArg b.hom.hom (d.homotopy.map_zero_left (b.inv.hom x))).trans ?_
      change b.hom.hom (i.hom (d.retraction.hom (b.inv.hom x))) =
        b.hom.hom (i.hom (a.inv.hom (a.hom.hom (d.retraction.hom (b.inv.hom x)))))
      rw [show ∀ y, a.inv.hom (a.hom.hom y) = y from
        fun y => congrArg (fun f => f.hom y) a.hom_inv_id]
    map_one_left := by
      intro x
      change b.hom.hom (d.homotopy (1, b.inv.hom x)) = x
      exact (congrArg b.hom.hom (d.homotopy.map_one_left (b.inv.hom x))).trans
        (congrArg (fun f => f.hom x) b.inv_hom_id)
    prop' := by
      intro t y hy
      obtain ⟨x, rfl⟩ := hy
      have hb (z : B) : b.inv.hom (b.hom.hom z) = z :=
        congrArg (fun f => f.hom z) b.hom_inv_id
      change b.hom.hom (d.homotopy (t, b.inv.hom (b.hom.hom (i.hom (a.inv.hom x))))) = _
      rw [hb]
      have hs := d.homotopy.eq_fst t (Set.mem_range_self (a.inv.hom x))
      rw [hs]
      change b.hom.hom (i.hom (d.retraction.hom (i.hom (a.inv.hom x)))) = _
      simp only [TopCat.comp_app]
      rw [hb]
      have ha (z : A) : a.inv.hom (a.hom.hom z) = z :=
        congrArg (fun f => f.hom z) a.hom_inv_id
      rw [ha] }

/-- The same data transported across a commuting square of isomorphisms. -/
def Data.ofIso (d : Data i) {i' : A' ⟶ B'} (a : A ≅ A') (b : B ≅ B')
    (w : i ≫ b.hom = a.hom ≫ i') : Data i' := by
  have he : a.inv ≫ i ≫ b.hom = i' := by rw [w]; simp
  exact he ▸ d.conjugate a b

end

end Thomason.Construction.TopologicalDeformation

end

end OAI
