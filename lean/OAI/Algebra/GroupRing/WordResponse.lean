import Mathlib
import OAI.Algebra.GroupRing.LoopSphere
import OAI.Algebra.GroupRing.CellModule

namespace OAI



section
namespace TorsionFreeZeroDivisors.WordResponse
open GroupRingTopology GroupRingTopology.PathExtension
open Path.Homotopic
noncomputable section
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}
def basedClass {a b : X} (p : Path.Homotopic.Quotient a b) {Y : Type*} [TopologicalSpace Y]
    (f : C(X,Y)) (y : Y) (ha : f a=y) (hb : f b=y) : FundamentalGroup Y y :=
  (p.map f).cast ha.symm hb.symm
lemma basedClass_equal {a b c d : X} {p : Path.Homotopic.Quotient a b}
    {q : Path.Homotopic.Quotient c d} (h : Q.Equal p q) {Y : Type*} [TopologicalSpace Y]
    (f : C(X,Y)) (y : Y) (ha : f a=y) (hb : f b=y) (hc : f c=y) (hd : f d=y) :
    basedClass p f y ha hb=basedClass q f y hc hd := by
  rcases h with ⟨h1,h2,h3⟩
  subst c;subst d;cases eq_of_heq h3;rfl
lemma basedClass_trans {a b c : X} (p : Path.Homotopic.Quotient a b)
    (q : Path.Homotopic.Quotient b c) {Y : Type*} [TopologicalSpace Y]
    (f : C(X,Y)) (y : Y) (ha : f a=y) (hb : f b=y) (hc : f c=y) :
    basedClass (p.trans q) f y ha hc=basedClass q f y hb hc * basedClass p f y ha hb := by
  unfold basedClass
  rw [Q.map_trans,←Q.trans_cast _ _ ha.symm hb.symm hc.symm]
  rfl
lemma basedClass_map {a b : X} (p : Path.Homotopic.Quotient a b)
    {Z Y : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X,Y)) (k : C(Y,Z)) (z : Z) (ha : k (f a)=z) (hb : k (f b)=z) :
    basedClass (p.map f) k z ha hb=basedClass p (k.comp f) z ha hb := by
  unfold basedClass
  congr 1
  induction p using Path.Homotopic.Quotient.ind with | mk p=>rfl
variable {G S Y : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace Y] (s : S→G) (f : C(Cayley.Graph s,Y)) (y : Y)
  (hv : ∀g,f (Cayley.vertex s g)=y)
include hv in
lemma source_eq (g : G) : f (g • Cayley.vertex s 1)=y := by rw [Cayley.smul_vertex,_root_.mul_one,hv]
include hv in
lemma target_eq (g : G) (w : FreeGroup S) : f (g • ((Cayley.wordLift s w).1 • Cayley.vertex s 1))=y := by
  rw [Cayley.smul_vertex,Cayley.smul_vertex,_root_.mul_one,hv]
def response (g : G) (w : FreeGroup S) : Additive (FundamentalGroup Y y) :=
  Additive.ofMul (basedClass ((Cayley.wordLift s w).2.map (smulMap g)) f y
    (source_eq s f y hv g) (target_eq s f y hv g w))
variable [IsMulCommutative (FundamentalGroup Y y)]
local instance : CommGroup (FundamentalGroup Y y) :=
  { (inferInstance : Group (FundamentalGroup Y y)) with mul_comm:=isMulCommutative_iff.mp inferInstance }
lemma response_mul (g : G) (w v : FreeGroup S) :
    response s f y hv g (w*v)=response s f y hv g w+
      response s f y hv (g*FreeGroup.lift s w) v := by
  let a:=Cayley.wordLift s w
  let b:=Cayley.wordLift s v
  have h := ((mul_path_equal a b).map (smulMap g)).trans
    (Q.Equal.ofEq (Q.map_trans a.2 (b.2.map (smulMap a.1)) (smulMap g)))
  have h2 := map_mul_equal b.2 g a.1
  have he : Q.Equal ((Cayley.wordLift s (w*v)).2.map (smulMap g)) ((a*b).2.map (smulMap g)) := by
    rw [show Cayley.wordLift s (w*v)=a*b from map_mul _ _ _]
    exact .refl _
  change basedClass ((Cayley.wordLift s (w*v)).2.map (smulMap g)) f y
    (source_eq s f y hv g) (target_eq s f y hv g (w*v))= _ * _
  rw [basedClass_equal (he.trans h) f y (source_eq s f y hv g)
    (target_eq s f y hv g (w*v)) (source_eq s f y hv g) (by
      change f (g • (a.1 • (b.1 • Cayley.vertex s 1)))=y
      simp only [Cayley.smul_vertex,hv])]
  erw [basedClass_trans _ _ f y (source_eq s f y hv g) (by
    change f (g • (a.1 • Cayley.vertex s 1))=y
    simp only [Cayley.smul_vertex,hv]) (by
      change f (g • (a.1 • (b.1 • Cayley.vertex s 1)))=y
      simp only [Cayley.smul_vertex,hv])]
  rw [mul_comm]
  congr 1
  have hh:= basedClass_equal h2 f y (by
    simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv]) (by
    simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv])
    (by simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv]) (by
      simp only [smulMap,ContinuousMap.coe_mk,Cayley.smul_vertex,hv])
  refine hh.trans ?_
  change (response s f y hv (g*a.1) v).toMul=(response s f y hv (g*FreeGroup.lift s w) v).toMul
  exact congrArg (fun h : G=>(response s f y hv (g*h) v).toMul) (Cayley.wordLift_fst s w)
lemma response_one (g : G) : response s f y hv g 1=0 := by
  have h:=response_mul s f y hv g 1 1
  simpa only [_root_.one_mul,map_one,_root_.mul_one] using (add_eq_left.mp h.symm)
lemma response_inv (g : G) (w : FreeGroup S) :
    response s f y hv g w⁻¹= -response s f y hv (g*(FreeGroup.lift s w)⁻¹) w := by
  have h:=response_mul s f y hv g w⁻¹ w
  rw [_root_.inv_mul_cancel,response_one s f y hv,map_inv] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def edges : CellModule.Module G S→+ Additive (FundamentalGroup Y y) :=
  Finsupp.liftAddHom (fun z : G×S=>zmultiplesHom _ (response s f y hv z.1 (FreeGroup.of z.2)))
lemma edges_fox (g : G) (w : FreeGroup S) :
    edges s f y hv (CellModule.translate g (CellModule.fox (FreeGroup.lift s) w))=response s f y hv g w := by
  induction w using FreeGroup.induction_on generalizing g with
  | one=>rw [CellModule.fox_one,map_zero,map_zero,response_one s f y hv]
  | of a=>simp [CellModule.fox_of,CellModule.translate_single,edges]
  | inv_of a ih=>
    rw [CellModule.fox_inv,map_neg,map_neg,←CellModule.translate_mul,ih,response_inv s f y hv]
  | mul w v hw hv'=>
    rw [CellModule.fox_mul,map_add,map_add,←CellModule.translate_mul,hw,hv',response_mul s f y hv]
end
end TorsionFreeZeroDivisors.WordResponse

end


end OAI
