import Mathlib
import OAI.Algebra.GroupRing.SphereTopology
import OAI.Algebra.GroupRing.ConeCells

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.GraphConeCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open scoped unitInterval Classical
variable {V E : Type} (src dst : E→V)
local instance optionVertexTopology : TopologicalSpace (Option V) := ⊥
local instance optionVertexDiscreteTopology : DiscreteTopology (Option V) := ⟨rfl⟩
instance oneNonempty : Nonempty (One src dst) := ⟨vertex src dst none⟩
lemma zero_dimension (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Option V)) n) : n<1 := by
  cases n with
  | zero => omega
  | succ n => exact i.elim
instance oneCW : CWComplex (Set.univ : Set (One src dst)) := layerCW _ zero_dimension
instance oneT2 : T2Space (One src dst) := t2Space _ realSeparated_of_tychonoff
lemma one_dimension (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set (One src dst)) n) : n<2 :=
  layerCW_dimensions _ zero_dimension n i
instance coneCW : CWComplex (Set.univ : Set (Cone src dst)) := layerCW _ (one_dimension src dst)
instance coneT2 : T2Space (Cone src dst) := t2Space _ (realSeparated _ realSeparated_of_tychonoff)
lemma no_higher (n : ℕ) (hn : 2<n) : IsEmpty (RelCWComplex.cell (Set.univ : Set (Cone src dst)) n) := by
  refine ⟨fun i=>?_⟩
  have := layerCW_dimensions (twoBoundary src dst) (one_dimension src dst) n i
  omega
lemma finite [Finite V] [Finite E] : CWComplex.Finite (Set.univ : Set (Cone src dst)) where
  eventually_isEmpty_cell := Filter.eventually_atTop.mpr ⟨3,fun n hn=>no_higher src dst n (by omega)⟩
  finite_cell n := by
    apply layerCW_finite_cells
    intro m
    apply layerCW_finite_cells
    intro k
    cases k with
    | zero => change Finite (Set.univ : Set (Option V)); infer_instance
    | succ k => change Finite PEmpty; infer_instance
lemma two_cell [Nonempty E] : Nonempty (RelCWComplex.cell (Set.univ : Set (Cone src dst)) 2) :=
  ⟨Sum.inr ⟨⟨⟨rfl⟩,Classical.choice inferInstance⟩⟩⟩
variable {Y : Type*} [TopologicalSpace Y]
variable (v : C(Option V,Y)) (ed : V⊕E→C(Disk 1,Y))
    (hed : ∀i x,ed i (boundary 1 x)=v (oneBoundary src dst i x))
def mapOne : C(One src dst,Y) := lift _ v ed hed
@[simp] lemma mapOne_vertex (x : Option V) : mapOne src dst v ed hed (vertex src dst x)=v x := rfl
@[simp] lemma mapOne_edge (i : V⊕E) (d : Disk 1) : mapOne src dst v ed hed (cell (oneBoundary src dst) i d)=ed i d :=
  lift_cell _ _ _ _ i d
variable (sq : E→C(Disk 2,Y)) (hsq : ∀e x,sq e (boundary 2 x)=mapOne src dst v ed hed (twoBoundary src dst e x))
def mapCone : C(Cone src dst,Y) := lift _ (mapOne src dst v ed hed) sq hsq
@[simp] lemma mapCone_one (x : One src dst) : mapCone src dst v ed hed sq hsq (inclusion src dst x)=mapOne src dst v ed hed x := rfl
@[simp] lemma mapCone_square (e : E) (d : Disk 2) : mapCone src dst v ed hed sq hsq (square src dst e d)=sq e d :=
  lift_cell _ _ _ _ e d
end TorsionFreeZeroDivisors.GraphConeCW

namespace TorsionFreeZeroDivisors.CellPresentation
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval
variable {G S Q : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (s : S→G) (a : Q→C(Sphere 2,Cayley.Graph s))
abbrev Cover := Space (equivariantFamily (G:=G) a)
def inclusion : C(Cayley.Graph s,Cover s a) := ⟨base _,continuous_base _⟩
lemma inclusion_smul (g : G) (x : Cayley.Graph s) : inclusion s a (g • x)=g • inclusion s a x := rfl
def wordLift : FreeGroup S →* Extension G (inclusion s a (Cayley.vertex s 1)) :=
  (PathExtension.map (inclusion s a) (inclusion_smul s a) (Cayley.vertex s 1)).comp (Cayley.wordLift s)
variable (rel : Q→FreeGroup S) (ha : ∀q,wordLift s a (rel q)=1)
variable (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker=Subgroup.normalClosure (Set.range rel))
include ha hker in
lemma wordLift_ker : (FreeGroup.lift s).ker≤(wordLift s a).ker := by
  rw [hker]
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨q,rfl⟩
  exact ha q
def sectionMap : G →* Extension G (inclusion s a (Cayley.vertex s 1)) :=
  (FreeGroup.lift s).liftOfSurjective hs ⟨wordLift s a,wordLift_ker s a rel ha hker⟩
lemma sectionMap_lift (w : FreeGroup S) :
    sectionMap s a rel ha hs hker (FreeGroup.lift s w)=wordLift s a w :=
  MonoidHom.liftOfRightInverse_comp_apply ..
lemma sectionMap_fst (g : G) : (sectionMap s a rel ha hs hker g).1=g := by
  obtain ⟨w,rfl⟩ := hs g
  rw [sectionMap_lift]
  exact Cayley.wordLift_fst s w
lemma sectionMap_generator (i : S) : PathExtension.Q.Equal
    (sectionMap s a rel ha hs hker (s i)).2
    (Path.Homotopic.Quotient.mk ((Cayley.edge s 1 i).map (inclusion s a).continuous)) := by
  have hh : sectionMap s a rel ha hs hker (s i)=
      PathExtension.map (inclusion s a) (inclusion_smul s a) (Cayley.vertex s 1)
        (Cayley.pathGenerator s i) := by
    simpa only [FreeGroup.lift_apply_of,wordLift,MonoidHom.comp_apply,Cayley.wordLift]
      using sectionMap_lift s a rel ha hs hker (FreeGroup.of i)
  rw [hh]
  exact (PathExtension.mapFun_equal (inclusion s a) (inclusion_smul s a)
    (Cayley.vertex s 1) (Cayley.pathGenerator s i)).trans
      ((Cayley.pathGenerator_equal s i).map (inclusion s a))
def graphNullhomotopy : (inclusion s a).Homotopy
    (.const _ (inclusion s a (Cayley.vertex s 1))) :=
  Cayley.nullhomotopyOfSection s (inclusion s a) (inclusion_smul s a)
    (sectionMap s a rel ha hs hker) (sectionMap_fst s a rel ha hs hker)
    (sectionMap_generator s a rel ha hs hker)
instance coverT2 : T2Space (Cover s a) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y:=G)))
instance coverCW : CWComplex (Set.univ : Set (Cover s a)) :=
  layerCW _ (Cayley.graph_dimension s)
include hs in
lemma cover_pathConnected : PathConnectedSpace (Cover s a) := by
  have hgen : Subgroup.closure (Set.range s)=⊤ := by
    rw [←FreeGroup.range_lift_eq_closure,MonoidHom.range_eq_top]
    exact hs
  let := Cayley.graph_pathConnected s hgen
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
include ha hs hker in
lemma cover_circleFill (b : C(Sphere 2,Cover s a)) : SphereTopology.Extends b := by
  let := SphereTopology.sphere_nonempty 1
  have hdim : dimH (Set.univ : Set (Sphere 2))<2 :=
    (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base _ b hdim
  apply SphereTopology.extends_of_homotopy H
  exact SphereTopology.extends_of_nullhomotopic
    (((graphNullhomotopy s a rel ha hs hker).compContinuousMap g).symm)
include ha hs hker in
lemma cover_simplyConnected : SimplyConnectedSpace (Cover s a) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨cover_pathConnected s a hs,?_⟩
  intro x p
  obtain ⟨F,hF⟩ := cover_circleFill s a rel ha hs hker (LoopSphere.map p)
  apply LoopSphere.homotopic_of_fill p F
  intro z
  exact ContinuousMap.congr_fun hF z

def diskAttaching : Q→C(Sphere 2,PresentationTopology.Rose s) := fun q=>
  (PresentationTopology.graphProjection s).comp (a q)
abbrev Base := Space (diskAttaching s a)
def projection : C(Cover s a,Base s a) :=
  coverMap a (PresentationTopology.graphProjection s)
    (PresentationTopology.graphProjection_quotient s) (diskAttaching s a) (fun _ _=>rfl)
lemma projection_quotient : IsQuotientCoveringMap (projection s a) G :=
  coverMap_isQuotientCovering _ _ _ _ _
instance baseT2 : T2Space (Base s a) := t2Space _ (realSeparated _ realSeparated_of_tychonoff)
instance baseCW : CWComplex (Set.univ : Set (Base s a)) :=
  layerCW _ (PresentationTopology.rose_dimension s)
lemma base_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Base s a)) m) : m < 3 :=
  layerCW_dimensions _ (PresentationTopology.rose_dimension s) m i
lemma base_no_higher (m : ℕ) (hm : 2 < m) : IsEmpty (RelCWComplex.cell (Set.univ : Set (Base s a)) m) :=
  ⟨fun i=>by have := base_dimension s a m i; omega⟩
lemma base_finite [Finite S] [Finite Q] : CWComplex.Finite (Set.univ : Set (Base s a)) where
  eventually_isEmpty_cell := Filter.eventually_atTop.mpr ⟨3,fun m hm=>base_no_higher s a m (by omega)⟩
  finite_cell m := layerCW_finite_cells _ (PresentationTopology.rose_finite s) (PresentationTopology.rose_dimension s) m
lemma base_two_cell [Nonempty Q] : Nonempty (RelCWComplex.cell (Set.univ : Set (Base s a)) 2) :=
  ⟨Sum.inr ⟨⟨⟨rfl⟩,Classical.choice inferInstance⟩⟩⟩
instance basePathConnected : PathConnectedSpace (Base s a) := by
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _
def coverPoint : Cover s a := inclusion s a (Cayley.vertex s 1)
def basePoint : Base s a := projection s a (coverPoint s a)
def fundamentalEquiv : G ≃* FundamentalGroup (Base s a) (basePoint s a) := by
  let := cover_simplyConnected s a rel ha hs hker
  exact (MulEquiv.inv' G).trans
    ((projection_quotient s a).fundamentalGroupEquiv ⟨coverPoint s a,rfl⟩).symm
lemma cover_no_higher (m : ℕ) (hm : 2 < m) :
    IsEmpty (RelCWComplex.cell (Set.univ : Set (Cover s a)) m) := by
  refine ⟨fun i=>?_⟩
  have := layerCW_dimensions (equivariantFamily (G:=G) a) (Cayley.graph_dimension s) m i
  omega
include ha hs hker in
lemma contractible_cover
    (hfill : ∀a : C(Sphere 3,Cover s a),SphereTopology.Extends a) :
    ContractibleSpace (Cover s a) := by
  let := cover_pathConnected s a hs
  exact FiniteDimensionalCW.contractible_of_two_dimensional_fills (cover_no_higher s a)
    (cover_circleFill s a rel ha hs hker) hfill
end TorsionFreeZeroDivisors.CellPresentation
namespace TorsionFreeZeroDivisors.ConeCells
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval Classical
variable {G S V E : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (s : S→G)
def wordClass (w : FreeGroup S) : Path.Homotopic.Quotient (Cayley.vertex s 1) (Cayley.vertex s (FreeGroup.lift s w)) :=
  (Cayley.wordLift s w).2.cast rfl (by rw [Cayley.wordLift_fst,Cayley.smul_vertex,_root_.mul_one])
def wordPath (w : FreeGroup S) : Path (Cayley.vertex s 1) (Cayley.vertex s (FreeGroup.lift s w)) :=
  (Path.Homotopic.Quotient.mk_surjective (wordClass s w)).choose
lemma wordPath_equal (w : FreeGroup S) : Q.Equal (Path.Homotopic.Quotient.mk (wordPath s w)) (Cayley.wordLift s w).2 :=
  (Q.Equal.ofEq (Path.Homotopic.Quotient.mk_surjective (wordClass s w)).choose_spec).trans (Q.cast_equal _ _ _)
variable (src dst : E→V) (z : V→FreeGroup S) (lab : E→FreeGroup S)
variable (he : ∀e,FreeGroup.lift s (z (src e))*FreeGroup.lift s (lab e)=FreeGroup.lift s (z (dst e)))
def outerPath (e : E) : Path (Cayley.vertex s (FreeGroup.lift s (z (src e)))) (Cayley.vertex s (FreeGroup.lift s (z (dst e)))) :=
  ((wordPath s (lab e)).map (smulMap (FreeGroup.lift s (z (src e)))).continuous).cast
    (by simp [smulMap,Cayley.smul_vertex]) (by simpa only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex] using congrArg (Cayley.vertex s) (he e).symm)
lemma outerPath_equal (e : E) : Q.Equal (Path.Homotopic.Quotient.mk (outerPath s src dst z lab he e))
    ((Cayley.wordLift s (lab e)).2.map (smulMap (Cayley.wordLift s (z (src e))).1)) := by
  rw [Cayley.wordLift_fst]
  exact (Q.cast_equal _ _ _).trans ((wordPath_equal s (lab e)).map _)
local instance optionVertexTopology : TopologicalSpace (Option V) := ⊥
local instance optionVertexDiscreteTopology : DiscreteTopology (Option V) := ⟨rfl⟩
def vertexMap : C(Option V,Cayley.Graph s) :=
  ⟨fun v=>Cayley.vertex s (match v with | none=>1 | some v=>FreeGroup.lift s (z v)),continuous_of_discreteTopology⟩
def edgeMap : V⊕E→C(Disk 1,Cayley.Graph s)
  | .inl v => (wordPath s (z v)).symm.toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
  | .inr e => (outerPath s src dst z lab he e).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
lemma edgeMap_boundary (i : V⊕E) (x : Sphere 1) :
    edgeMap s src dst z lab he i (boundary 1 x)=vertexMap s z (GraphConeCW.oneBoundary src dst i x) := by
  cases i with
  | inl v =>
    rcases Cayley.sphere_one_eq x with rfl|rfl <;>
      simp [edgeMap,Cayley.edgeTime_minus,Cayley.edgeTime_plus,GraphConeCW.endpoint,vertexMap]
  | inr e =>
    rcases Cayley.sphere_one_eq x with rfl|rfl <;>
      simp [edgeMap,Cayley.edgeTime_minus,Cayley.edgeTime_plus,GraphConeCW.endpoint,vertexMap]
def oneMap : C(GraphConeCW.One src dst,Cayley.Graph s) :=
  GraphConeCW.mapOne src dst (vertexMap s z) (edgeMap s src dst z lab he) (edgeMap_boundary s src dst z lab he)
def attaching (e : E) : C(Sphere 2,Cayley.Graph s) :=
  (oneMap s src dst z lab he).comp (GraphConeCW.twoBoundary src dst e)
abbrev Cover := CellPresentation.Cover s (attaching s src dst z lab he)
def coneMap : C(GraphConeCW.Cone src dst,Cover s src dst z lab he) :=
  lift _ ((CellPresentation.inclusion s (attaching s src dst z lab he)).comp (oneMap s src dst z lab he))
    (fun e=>cell _ (show FreeIndex G E from ((1:G),e))) (by
      intro e x
      rw [cell_boundary]
      simp only [equivariantFamily,ContinuousMap.coe_mk,one_smul]
      rfl)
@[simp] lemma coneMap_one (x : GraphConeCW.One src dst) :
    coneMap s src dst z lab he (GraphConeCW.inclusion src dst x)=
      CellPresentation.inclusion s (attaching s src dst z lab he) (oneMap s src dst z lab he x) := rfl
@[simp] lemma coneMap_square (e : E) (d : Disk 2) :
    coneMap s src dst z lab he (GraphConeCW.square src dst e d)=cell _ (show FreeIndex G E from ((1:G),e)) d := lift_cell _ _ _ _ e d
lemma path_equal_of_pointwise {Y : Type*} [TopologicalSpace Y] {a b c d : Y}
    (p : Path a b) (q : Path c d) (h : ∀t,p t=q t) :
    Q.Equal (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q) :=
  ⟨by simpa using h 0,by simpa using h 1,Path.Homotopic.hpath_hext h⟩
def coneRadial (v : V) : Path
    (GraphConeCW.inclusion src dst (GraphConeCW.vertex src dst (some v))) (GraphConeCW.apex src dst) where
  toFun t := GraphConeCW.inclusion src dst (GraphConeCW.radial src dst v t)
  continuous_toFun := (GraphConeCW.inclusion src dst).continuous.comp (GraphConeCW.radial src dst v).continuous
  source' := by rw [GraphConeCW.radial_zero]
  target' := by rw [GraphConeCW.radial_one]; rfl
@[simp] lemma coneRadial_apply (v : V) (t : I) : coneRadial src dst v t =
    GraphConeCW.inclusion src dst (GraphConeCW.radial src dst v t) := rfl
def coneOuter (e : E) : Path
    (GraphConeCW.inclusion src dst (GraphConeCW.vertex src dst (some (src e))))
    (GraphConeCW.inclusion src dst (GraphConeCW.vertex src dst (some (dst e)))) where
  toFun t := GraphConeCW.inclusion src dst (GraphConeCW.outer src dst e (Cayley.edgeParam t))
  continuous_toFun := (GraphConeCW.inclusion src dst).continuous.comp
    ((GraphConeCW.outer src dst e).continuous.comp Cayley.continuous_edgeParam)
  source' := by rw [Cayley.edgeParam_zero,GraphConeCW.outer_minus]
  target' := by rw [Cayley.edgeParam_one,GraphConeCW.outer_plus]
lemma map_radial (v : V) (t : I) :
    coneMap s src dst z lab he ((coneRadial src dst v).symm t)=
      CellPresentation.inclusion s (attaching s src dst z lab he) (wordPath s (z v) t) := by
  simp only [Path.symm_apply,Function.comp_apply,coneRadial_apply]
  rw [coneMap_one]
  change CellPresentation.inclusion s _ (GraphConeCW.mapOne _ _ _ _ _
    (cell (GraphConeCW.oneBoundary src dst) (.inl v) (Cayley.edgeParam (unitInterval.symm t))))=_
  rw [GraphConeCW.mapOne_edge]
  change CellPresentation.inclusion s _ ((wordPath s (z v)).symm (Cayley.edgeTime (Cayley.edgeParam (unitInterval.symm t))))=_
  rw [Cayley.edgeTime_param]
  simp only [Path.symm_apply,Function.comp_apply,unitInterval.symm_symm]
lemma map_outer (e : E) (t : I) :
    coneMap s src dst z lab he (coneOuter src dst e t)=
      CellPresentation.inclusion s (attaching s src dst z lab he) (outerPath s src dst z lab he e t) := by
  change coneMap s src dst z lab he (GraphConeCW.inclusion src dst
    (cell (GraphConeCW.oneBoundary src dst) (.inr e) (Cayley.edgeParam t)))=_
  rw [coneMap_one]
  change CellPresentation.inclusion s _ (GraphConeCW.mapOne _ _ _ _ _ (cell _ _ _))=_
  rw [GraphConeCW.mapOne_edge]
  change CellPresentation.inclusion s _ (outerPath s src dst z lab he e (Cayley.edgeTime (Cayley.edgeParam t)))=_
  rw [Cayley.edgeTime_param]
lemma route_equal (e : E) : Q.Equal
    (Path.Homotopic.Quotient.mk ((wordPath s (z (src e))).trans (outerPath s src dst z lab he e)))
    (Cayley.wordLift s (z (src e)*lab e)).2 := by
  rw [map_mul]
  exact (Q.Equal.comp (wordPath_equal s _) (outerPath_equal s src dst z lab he e)).trans (mul_path_equal _ _).symm
lemma wordLift_edge (e : E) :
    CellPresentation.wordLift s (attaching s src dst z lab he) (z (src e)*lab e)=
      CellPresentation.wordLift s (attaching s src dst z lab he) (z (dst e)) := by
  let f := coneMap s src dst z lab he
  let inc := CellPresentation.inclusion s (attaching s src dst z lab he)
  let p := ((coneRadial src dst (src e)).symm).trans (coneOuter src dst e)
  let q := (coneRadial src dst (dst e)).symm
  have hpq : p.Homotopic q := SimplyConnectedSpace.paths_homotopic p q
  have hleft : Q.Equal (Path.Homotopic.Quotient.mk (p.map f.continuous))
      ((Cayley.wordLift s (z (src e)*lab e)).2.map inc) := by
    apply Q.Equal.trans ?_ ((route_equal s src dst z lab he e).map inc)
    change Q.Equal (Path.Homotopic.Quotient.mk (((coneRadial src dst (src e)).symm.trans (coneOuter src dst e)).map f.continuous)) _
    rw [Path.map_trans]
    have h1 := path_equal_of_pointwise
      (((coneRadial src dst (src e)).symm).map f.continuous)
      ((wordPath s (z (src e))).map inc.continuous) (map_radial s src dst z lab he (src e))
    have h2 := path_equal_of_pointwise ((coneOuter src dst e).map f.continuous)
      ((outerPath s src dst z lab he e).map inc.continuous) (map_outer s src dst z lab he e)
    exact (Q.Equal.comp h1 h2).trans (Q.Equal.ofEq (Q.map_trans
      (Path.Homotopic.Quotient.mk (wordPath s (z (src e))))
      (Path.Homotopic.Quotient.mk (outerPath s src dst z lab he e)) inc).symm)
  have hright : Q.Equal (Path.Homotopic.Quotient.mk (q.map f.continuous))
      ((Cayley.wordLift s (z (dst e))).2.map inc) :=
    (path_equal_of_pointwise _ _ (map_radial s src dst z lab he (dst e))).trans ((wordPath_equal s _).map inc)
  apply PathExtension.ext
  · change (Cayley.wordLift s (z (src e)*lab e)).1=(Cayley.wordLift s (z (dst e))).1
    rw [Cayley.wordLift_fst,Cayley.wordLift_fst,map_mul,he]
  · apply Q.Equal.path
    exact (PathExtension.mapFun_equal inc (CellPresentation.inclusion_smul s _) (Cayley.vertex s 1) _).trans
      (hleft.symm.trans ((Q.Equal.ofEq (Path.Homotopic.Quotient.eq.mpr (hpq.map f))).trans
      (hright.trans (PathExtension.mapFun_equal inc (CellPresentation.inclusion_smul s _) (Cayley.vertex s 1) _).symm)))
lemma wordLift_triangle (e : E) :
    CellPresentation.wordLift s (attaching s src dst z lab he) (z (src e)*lab e*(z (dst e))⁻¹)=1 := by
  rw [map_mul,map_inv,wordLift_edge,mul_inv_cancel]
end TorsionFreeZeroDivisors.ConeCells

end

end OAI
