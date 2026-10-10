import Mathlib
import OAI.Algebra.GroupRing.CayleyFurther
import OAI.Algebra.GroupRing.WordResponse

namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphLabels
open GroupRingTopology GroupRingTopology.Attachment GroupRingTopology.PathExtension
open scoped unitInterval
noncomputable section
variable {G S Y : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] (s : S→G) (y : Y) (k : G×S→FundamentalGroup Y y)
def representative (e : G×S) : Path y y :=
  (Path.Homotopic.Quotient.mk_surjective (k e)).choose
omit [Group G] [TopologicalSpace G] [DiscreteTopology G] in
lemma representative_class (e : G×S) : Path.Homotopic.Quotient.mk (representative y k e)=k e :=
  (Path.Homotopic.Quotient.mk_surjective (k e)).choose_spec
def edgeMap (e : G×S) : C(Disk 1,Y) :=
  (representative y k e).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩
omit [Group G] [TopologicalSpace G] [DiscreteTopology G] in
lemma edgeMap_boundary (e : G×S) (z : Sphere 1) : edgeMap y k e (boundary 1 z)=y := by
  obtain rfl|rfl:=Cayley.sphere_one_eq z
  · change representative y k e (Cayley.edgeTime (boundary 1 Cayley.minus))=y
    rw [Cayley.edgeTime_minus,Path.source]
  · change representative y k e (Cayley.edgeTime (boundary 1 Cayley.plus))=y
    rw [Cayley.edgeTime_plus,Path.target]
def map : C(Cayley.Graph s,Y) :=
  lift (equivariantFamily (G:=G) (Cayley.attaching s)) (.const _ y) (edgeMap y k)
    (fun e z=>edgeMap_boundary y k e z)
lemma map_vertex (g : G) : map s y k (Cayley.vertex s g)=y := rfl
lemma map_edge (g : G) (a : S) (t : unitInterval) :
    map s y k (Cayley.edge s g a t)=representative y k (g,a) t := by
  change map s y k (cell _ (g,a) (Cayley.edgeParam t))=_
  unfold map
  erw [lift_cell]
  change representative y k (g,a) (Cayley.edgeTime (Cayley.edgeParam t))=_
  rw [Cayley.edgeTime_param]

lemma edge_translate (g : G) (a : S) : Q.Equal
    ((Path.Homotopic.Quotient.mk (Cayley.edge s 1 a)).map (smulMap g))
    (Path.Homotopic.Quotient.mk (Cayley.edge s g a)) := by
  refine ⟨?_,?_,Path.Homotopic.hpath_hext ?_⟩
  · change g • Cayley.vertex s 1=Cayley.vertex s g
    rw [Cayley.smul_vertex,_root_.mul_one]
  · change g • Cayley.vertex s (1*s a)=Cayley.vertex s (g*s a)
    rw [Cayley.smul_vertex,_root_.one_mul]
  · intro t
    change g • cell (equivariantFamily (G:=G) (Cayley.attaching s)) ((1:G),a) (Cayley.edgeParam t)=cell (equivariantFamily (G:=G) (Cayley.attaching s)) (g,a) (Cayley.edgeParam t)
    erw [smul_cell _ (equivariantFamily_smul (Cayley.attaching s))]
    change cell (equivariantFamily (G:=G) (Cayley.attaching s)) (g*1,a) (Cayley.edgeParam t)=_
    rw [_root_.mul_one]
lemma response_generator (g : G) (a : S) :
    WordResponse.response s (map s y k) y (map_vertex s y k) g (FreeGroup.of a)=Additive.ofMul (k (g,a)) := by
  have hh : Q.Equal (((Cayley.wordLift s (FreeGroup.of a)).2).map (smulMap g))
      (Path.Homotopic.Quotient.mk (Cayley.edge s g a)) :=
    by
      rw [show Cayley.wordLift s (FreeGroup.of a)=Cayley.pathGenerator s a from FreeGroup.lift_apply_of]
      exact ((Cayley.pathGenerator_equal s a).map (smulMap g)).trans (edge_translate s g a)
  change WordResponse.basedClass (((Cayley.wordLift s (FreeGroup.of a)).2).map (smulMap g)) (map s y k) y
    (WordResponse.source_eq s (map s y k) y (map_vertex s y k) g)
    (WordResponse.target_eq s (map s y k) y (map_vertex s y k) g (FreeGroup.of a))=k (g,a)
  erw [WordResponse.basedClass_equal hh (map s y k) y _ _ (map_vertex s y k g) (map_vertex s y k (g*s a))]
  change Path.Homotopic.Quotient.mk (((Cayley.edge s g a).map (map s y k).continuous).cast _ _)=k (g,a)
  rw [show (((Cayley.edge s g a).map (map s y k).continuous).cast (map_vertex s y k g).symm
    (map_vertex s y k (g*s a)).symm)=representative y k (g,a) from by
      ext t;exact map_edge s y k g a t]
  exact representative_class y k (g,a)
variable [IsMulCommutative (FundamentalGroup Y y)]
local instance : CommGroup (FundamentalGroup Y y) :=
  { (inferInstance : Group (FundamentalGroup Y y)) with mul_comm:=isMulCommutative_iff.mp inferInstance }
lemma realizes (c : CellModule.Module G S→+Additive (FundamentalGroup Y y)) (g : G) (w : FreeGroup S) :
    WordResponse.response s (map s y (fun e=>(c (Finsupp.single e 1)).toMul)) y
      (map_vertex s y _) g w=c (CellModule.translate g (CellModule.fox (FreeGroup.lift s) w)) := by
  rw [←WordResponse.edges_fox]
  have he : WordResponse.edges s (map s y (fun e=>(c (Finsupp.single e 1)).toMul)) y
      (map_vertex s y _)=c := by
    apply Finsupp.addHom_ext
    intro e z
    simp only [WordResponse.edges,Finsupp.liftAddHom_apply_single,zmultiplesHom_apply,response_generator]
    change z • c (Finsupp.single e 1)=c (Finsupp.single e z)
    rw [←map_zsmul]
    congr 1
    simp
  rw [he]
end
end TorsionFreeZeroDivisors.GraphLabels

end



end OAI
