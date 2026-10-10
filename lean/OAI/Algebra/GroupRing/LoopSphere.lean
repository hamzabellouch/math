import Mathlib
import OAI.Algebra.GroupRing.Cayley

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cellular
open Set Metric Topology
variable {Y : Type*} [TopologicalSpace Y]

/-- One cylinder boundary filling is enough for its path-space lift. -/
theorem cylinderFill {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
    (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (F : C(Disk (n+1),Y)) (hF : ∀ x, F (boundary (n+1) x) = cylinderBoundaryMap a b h x) :
    ∃ e : C(Disk n,C(unitInterval,Y)),
      (∀ x, e (boundary n x) = a x) ∧ (∀ x, pathEndpoint (e x) = b x) := by
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]

end GroupRingTopology.Cellular
namespace GroupRingTopology.LoopSphere
open Set Metric Topology Cellular
open scoped unitInterval
universe u v
variable {X : Type u} [TopologicalSpace X] {x : X}

def sides : C(Sphere 1,C(I,X)) := .const _ (.const _ x)
def ends (p : Path x x) : C(Disk 1,X × X) :=
  ⟨fun d => (p (Cayley.edgeTime d),x),
    (p.continuous.comp Cayley.continuous_edgeTime).prodMk continuous_const⟩
lemma ends_sides (p : Path x x) (z : Sphere 1) :
    pathEndpoint (sides (x := x) z) = ends p (boundary 1 z) := by
  obtain rfl|rfl := Cayley.sphere_one_eq z
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.minus)),x)
    rw [Cayley.edgeTime_minus,p.source]
  · change (x,x) = (p (Cayley.edgeTime (Attachment.boundary 1 Cayley.plus)),x)
    rw [Cayley.edgeTime_plus,p.target]

def map (p : Path x x) : C(Sphere 2,X) := cylinderBoundaryMap sides (ends p) (ends_sides p)

/-- Attaching one ordinary 2-cell along this square boundary kills its loop. -/
theorem homotopic_of_fill (p : Path x x) (F : C(Disk 2,X))
    (hF : ∀ z, F (boundary 2 z) = map p z) : p.Homotopic (Path.refl x) := by
  obtain ⟨e,he,hep⟩ := cylinderFill sides (ends p) (ends_sides p) F hF
  refine ⟨{
    toFun := fun z => e (Cayley.edgeParam z.2) z.1
    continuous_toFun := e.uncurry.continuous.comp
      ((Cayley.continuous_edgeParam.comp continuous_snd).prodMk continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    have h := congrArg Prod.fst (hep (Cayley.edgeParam t))
    change e (Cayley.edgeParam t) 0 = p t
    change e (Cayley.edgeParam t) 0 = p (Cayley.edgeTime (Cayley.edgeParam t)) at h
    simpa only [Cayley.edgeTime_param] using h
  · intro t
    exact congrArg Prod.snd (hep (Cayley.edgeParam t))
  · intro t q hq
    obtain rfl|hq := hq
    · change e (Cayley.edgeParam 0) t = p 0
      rw [Cayley.edgeParam_zero,p.source]
      exact ContinuousMap.congr_fun (he Cayley.minus) t
    · obtain rfl := Set.mem_singleton_iff.mp hq
      change e (Cayley.edgeParam 1) t = p 1
      rw [Cayley.edgeParam_one,p.target]
      exact ContinuousMap.congr_fun (he Cayley.plus) t

variable {Y : Type v} [TopologicalSpace Y]
lemma natural (p : Path x x) (f : C(X,Y)) : map (p.map f.continuous) = f.comp (map p) := by
  apply ContinuousMap.ext; intro z
  have hz : z ∈ ⋃ i, cylinderFace 1 i := by rw [cylinderFace_cover]; trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change cylinderBoundaryMap sides (ends (p.map f.continuous)) (ends_sides _) z =
    f (cylinderBoundaryMap sides (ends p) (ends_sides p) z)
  rw [cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩,cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩]
  cases i with
  | none => rfl
  | some b => cases b <;> rfl

lemma homotopic_map_of_fill (p : Path x x) (f : C(X,Y)) (F : C(Disk 2,Y))
    (hF : ∀ z, F (boundary 2 z) = f (map p z)) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  apply homotopic_of_fill _ F
  intro z
  rw [natural]
  exact hF z
end GroupRingTopology.LoopSphere

/-! The path-class extension of an acting group. This is geometric support for
the finite presentation Cayley cover, not an assumption of simple connectivity. -/

namespace GroupRingTopology.PathExtension

section
open Path.Homotopic
universe u v
variable {X : Type u} [TopologicalSpace X]

namespace Q
variable {x y z : X}
lemma trans_cast {x' y' z' : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) (hx : x' = x) (hy : y' = y) (hz : z' = z) :
    (p.cast hx hy).trans (q.cast hy hz) = (p.trans q).cast hx hz := by
  subst x'; subst y'; subst z'; simp
lemma map_trans {Y : Type*} [TopologicalSpace Y]
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) (f : C(X,Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  induction q using Path.Homotopic.Quotient.ind with | mk q =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_trans q f.continuous)
lemma map_refl {Y : Type*} [TopologicalSpace Y] (x : X) (f : C(X,Y)) :
    (Path.Homotopic.Quotient.refl x).map f = Path.Homotopic.Quotient.refl (f x) := rfl
lemma map_symm {Y : Type*} [TopologicalSpace Y] (p : Path.Homotopic.Quotient x y) (f : C(X,Y)) :
    p.symm.map f = (p.map f).symm := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact congrArg Path.Homotopic.Quotient.mk (p.map_symm f.continuous)
/-- Equality of path classes together with equality of both endpoint labels. -/
structure Equal {x' y' : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient x' y') : Prop where
  source : x = x'
  target : y = y'
  path : HEq p q

namespace Equal
lemma refl (p : Path.Homotopic.Quotient x y) : Equal p p := ⟨rfl,rfl,HEq.rfl⟩
lemma ofEq {p q : Path.Homotopic.Quotient x y} (h : p = q) : Equal p q := ⟨rfl,rfl,heq_of_eq h⟩
lemma symm {x' y' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient x' y'} (h : Equal p q) : Equal q p :=
  ⟨h.source.symm,h.target.symm,h.path.symm⟩
lemma trans {x' y' x'' y'' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient x' y'} {r : Path.Homotopic.Quotient x'' y''}
    (h : Equal p q) (k : Equal q r) : Equal p r :=
  ⟨h.source.trans k.source,h.target.trans k.target,h.path.trans k.path⟩
lemma map {Y : Type*} [TopologicalSpace Y] {x' y' : X}
    {p : Path.Homotopic.Quotient x y} {q : Path.Homotopic.Quotient x' y'}
    (h : Equal p q) (f : C(X,Y)) : Equal (p.map f) (q.map f) := by
  rcases h with ⟨hx,hy,hp⟩
  subst x'; subst y'
  cases eq_of_heq hp
  exact .refl _
lemma comp {x' y' z' : X} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient y z} {p' : Path.Homotopic.Quotient x' y'}
    {q' : Path.Homotopic.Quotient y' z'} (hp : Equal p p') (hq : Equal q q') :
    Equal (p.trans q) (p'.trans q') := by
  rcases hp with ⟨hx,hy,hp⟩
  rcases hq with ⟨_,hz,hq⟩
  subst x'; subst y'; subst z'
  cases eq_of_heq hp; cases eq_of_heq hq
  exact .refl _
end Equal
lemma cast_equal {x' y' : X} (p : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    Equal (p.cast hx hy) p := ⟨hx,hy,Path.Homotopic.Quotient.cast_heq hx hy⟩
lemma refl_equal {x y : X} (h : x = y) :
    Equal (Path.Homotopic.Quotient.refl x) (Path.Homotopic.Quotient.refl y) := by
  subst y
  exact .refl _

end Q

variable {G : Type v} [Group G] [MulAction G X] [ContinuousConstSMul G X]

def smulMap (g : G) : C(X,X) := ⟨fun x => g • x,continuous_const_smul g⟩

lemma map_one_equal {x y : X} (p : Path.Homotopic.Quotient x y) :
    Q.Equal (p.map (smulMap (1 : G))) p := by
  refine ⟨one_smul G x,one_smul G y,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => one_smul G (p t))

lemma map_mul_equal {x y : X} (p : Path.Homotopic.Quotient x y) (g h : G) :
    Q.Equal ((p.map (smulMap h)).map (smulMap g)) (p.map (smulMap (g*h))) := by
  refine ⟨(mul_smul g h x).symm,(mul_smul g h y).symm,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => (mul_smul g h (p t)).symm)

variable (G) (x₀ : X)
abbrev Extension := Σ g : G, Path.Homotopic.Quotient x₀ (g • x₀)
variable {G x₀}

omit [ContinuousConstSMul G X] in
@[ext] lemma ext {a b : Extension G x₀} (hg : a.1 = b.1) (hp : HEq a.2 b.2) : a = b :=
  Sigma.ext hg hp

instance : One (Extension G x₀) :=
  ⟨⟨1,(Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)⟩⟩
instance : Mul (Extension G x₀) :=
  ⟨fun a b => ⟨a.1*b.1,(a.2.trans (b.2.map (smulMap a.1))).cast rfl (mul_smul ..)⟩⟩
instance : Inv (Extension G x₀) :=
  ⟨fun a => ⟨a.1⁻¹,((a.2.map (smulMap a.1⁻¹)).symm).cast (inv_smul_smul a.1 x₀).symm rfl⟩⟩

lemma mul_path_equal (a b : Extension G x₀) :
    Q.Equal (a*b).2 (a.2.trans (b.2.map (smulMap a.1))) :=
  Q.cast_equal _ _ _

omit [ContinuousConstSMul G X] in
lemma one_path_equal : Q.Equal (1 : Extension G x₀).2 (Path.Homotopic.Quotient.refl x₀) := by
  change Q.Equal ((Path.Homotopic.Quotient.refl x₀).cast rfl (one_smul G x₀)) _
  exact Q.cast_equal _ _ _

lemma mul_assoc (a b c : Extension G x₀) : a*b*c = a*(b*c) := by
  apply ext (_root_.mul_assoc _ _ _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal (a*b) c)
  apply Q.Equal.trans (Q.Equal.comp (mul_path_equal a b) (map_mul_equal c.2 a.1 b.1).symm)
  apply Q.Equal.trans (Q.Equal.ofEq (Path.Homotopic.Quotient.trans_assoc _ _ _))
  apply Q.Equal.trans ?_ (mul_path_equal a (b*c)).symm
  apply Q.Equal.comp (Q.Equal.refl _)
  apply Q.Equal.trans ?_ ((mul_path_equal b c).map (smulMap a.1)).symm
  exact Q.Equal.ofEq (Q.map_trans _ _ _).symm

lemma one_mul (a : Extension G x₀) : 1*a = a := by
  apply ext (_root_.one_mul _)
  apply Q.Equal.path
  exact (mul_path_equal 1 a).trans
    ((Q.Equal.comp one_path_equal (map_one_equal a.2)).trans
      (Q.Equal.ofEq (Path.Homotopic.Quotient.refl_trans a.2)))

lemma mul_one (a : Extension G x₀) : a*1 = a := by
  apply ext (_root_.mul_one _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal a 1)
  apply Q.Equal.trans (Q.Equal.comp (Q.Equal.refl _) (one_path_equal.map (smulMap a.1)))
  rw [Q.map_refl]
  exact Q.Equal.ofEq (Path.Homotopic.Quotient.trans_refl a.2)

lemma inv_mul_cancel (a : Extension G x₀) : a⁻¹*a = 1 := by
  apply ext (_root_.inv_mul_cancel _)
  apply Q.Equal.path
  apply Q.Equal.trans (mul_path_equal a⁻¹ a)
  have hi : Q.Equal (a⁻¹).2 (a.2.map (smulMap a.1⁻¹)).symm := Q.cast_equal _ _ _
  exact (Q.Equal.comp hi (Q.Equal.refl _)).trans
    ((Q.Equal.ofEq (Path.Homotopic.Quotient.symm_trans _)).trans
      ((Q.refl_equal (inv_smul_smul a.1 x₀)).trans one_path_equal.symm))

instance : Group (Extension G x₀) where
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := inv_mul_cancel

/-- Endpoint projection of the genuine path-class extension. -/
def projection : Extension G x₀ →* G where
  toFun := Sigma.fst
  map_one' := rfl
  map_mul' _ _ := rfl

end
open Path.Homotopic
universe u v w
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(X,Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

include hf in
lemma natural_smul_equal {x y : X} (p : Path.Homotopic.Quotient x y) (g : G) :
    Q.Equal ((p.map (smulMap g)).map f) ((p.map f).map (smulMap g)) := by
  refine ⟨hf g x,hf g y,?_⟩
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.hpath_hext (fun t => hf g (p t))

variable (x₀ : X)
def mapFun (a : Extension G x₀) : Extension G (f x₀) :=
  ⟨a.1,(a.2.map f).cast rfl (hf a.1 x₀).symm⟩
omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
lemma mapFun_equal (a : Extension G x₀) :
    Q.Equal (mapFun f hf x₀ a).2 (a.2.map f) := Q.cast_equal _ _ _
omit [ContinuousConstSMul G X] [ContinuousConstSMul G Y] in
lemma mapFun_one : mapFun f hf x₀ 1 = 1 := by
  apply ext rfl
  apply Q.Equal.path
  apply (mapFun_equal f hf x₀ 1).trans
  apply (one_path_equal.map f).trans
  rw [Q.map_refl]
  exact one_path_equal.symm
lemma mapFun_mul (a b : Extension G x₀) : mapFun f hf x₀ (a*b) = mapFun f hf x₀ a * mapFun f hf x₀ b := by
  apply ext (a := mapFun f hf x₀ (a*b)) (b := mapFun f hf x₀ a * mapFun f hf x₀ b) (by rfl)
  apply Q.Equal.path
  apply (mapFun_equal f hf x₀ (a*b)).trans
  apply ((mul_path_equal a b).map f).trans
  apply (Q.Equal.ofEq (Q.map_trans _ _ _)).trans
  apply Q.Equal.trans ?_ (mul_path_equal (mapFun f hf x₀ a) (mapFun f hf x₀ b)).symm
  exact Q.Equal.comp (mapFun_equal f hf x₀ a).symm
    ((natural_smul_equal f hf b.2 a.1).trans
      ((mapFun_equal f hf x₀ b).map (smulMap a.1)).symm)

def map : Extension G x₀ →* Extension G (f x₀) where
  toFun := mapFun f hf x₀
  map_one' := mapFun_one f hf x₀
  map_mul' := mapFun_mul f hf x₀

lemma projection_map : projection.comp (map f hf x₀) = projection := rfl
end GroupRingTopology.PathExtension
namespace GroupRingTopology.Cayley
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)

lemma smul_vertex (g h : G) : g • vertex s h = vertex s (g*h) := rfl

def pathGenerator (i : S) : PathExtension.Extension G (vertex s 1) :=
  ⟨s i,Path.Homotopic.Quotient.mk ((edge s 1 i).cast rfl (by
    rw [smul_vertex]; simp only [_root_.mul_one,_root_.one_mul]))⟩
def wordLift : FreeGroup S →* PathExtension.Extension G (vertex s 1) :=
  FreeGroup.lift (pathGenerator s)
lemma projection_wordLift : PathExtension.projection.comp (wordLift s) = FreeGroup.lift s := by
  ext i
  simp only [MonoidHom.comp_apply,wordLift,FreeGroup.lift_apply_of]
  rfl
lemma wordLift_fst (w : FreeGroup S) : (wordLift s w).1 = FreeGroup.lift s w :=
  DFunLike.congr_fun (projection_wordLift s) w

variable (rels : Set (FreeGroup S)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
def relatorClass (r : rels) : Path.Homotopic.Quotient (vertex s 1) (vertex s 1) :=
  (wordLift s r.1).2.cast rfl (by rw [wordLift_fst,hrel r.1 r.2,one_smul])
def relatorLoop (r : rels) : Path (vertex s 1) (vertex s 1) :=
  (Path.Homotopic.Quotient.mk_surjective (relatorClass s rels hrel r)).choose
lemma relatorLoop_eq (r : rels) : Path.Homotopic.Quotient.mk (relatorLoop s rels hrel r) =
    relatorClass s rels hrel r :=
  (Path.Homotopic.Quotient.mk_surjective (relatorClass s rels hrel r)).choose_spec
lemma relatorLoop_equal (r : rels) :
    PathExtension.Q.Equal (Path.Homotopic.Quotient.mk (relatorLoop s rels hrel r))
      (wordLift s r.1).2 :=
  (PathExtension.Q.Equal.ofEq (relatorLoop_eq s rels hrel r)).trans (PathExtension.Q.cast_equal _ _ _)

def relatorAttaching (r : rels) : C(Sphere 2,Graph s) := LoopSphere.map (relatorLoop s rels hrel r)
abbrev PresentationCover := Space (equivariantFamily (G := G) (relatorAttaching s rels hrel))
def presentationBase : C(Graph s,PresentationCover s rels hrel) := ⟨base _,continuous_base _⟩
lemma presentationBase_smul (g : G) (x : Graph s) :
    presentationBase s rels hrel (g • x) = g • presentationBase s rels hrel x := rfl

def coverWordLift : FreeGroup S →* PathExtension.Extension G (presentationBase s rels hrel (vertex s 1)) :=
  (PathExtension.map (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1)).comp
    (wordLift s)

lemma mapped_relator_homotopic (r : rels) :
    ((relatorLoop s rels hrel r).map (presentationBase s rels hrel).continuous).Homotopic
      (Path.refl (presentationBase s rels hrel (vertex s 1))) := by
  apply LoopSphere.homotopic_map_of_fill _ _ (cell _ ((1:G),r))
  intro z
  change cell (equivariantFamily (G := G) (relatorAttaching s rels hrel)) ((1:G),r)
    (Attachment.boundary 2 z) = _
  erw [cell_boundary]
  simp only [equivariantFamily,ContinuousMap.coe_mk,one_smul]
  rfl

lemma coverWordLift_relator (r : rels) : coverWordLift s rels hrel r.1 = 1 := by
  apply PathExtension.ext (a := coverWordLift s rels hrel r.1) (b := 1)
    ((wordLift_fst s r.1).trans (hrel r.1 r.2))
  apply PathExtension.Q.Equal.path
  apply (PathExtension.mapFun_equal (presentationBase s rels hrel)
    (presentationBase_smul s rels hrel) (vertex s 1) (wordLift s r.1)).trans
  apply ((relatorLoop_equal s rels hrel r).map (presentationBase s rels hrel)).symm.trans
  apply (PathExtension.Q.Equal.ofEq (Quotient.sound (mapped_relator_homotopic s rels hrel r))).trans
  exact PathExtension.one_path_equal.symm

lemma coverWordLift_ker (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    (FreeGroup.lift s).ker ≤ (coverWordLift s rels hrel).ker := by
  rw [hker]
  apply Subgroup.normalClosure_le_normal
  intro r hr
  exact coverWordLift_relator s rels hrel ⟨r,hr⟩

def presentationSection (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    G →* PathExtension.Extension G (presentationBase s rels hrel (vertex s 1)) :=
  (FreeGroup.lift s).liftOfSurjective hs ⟨coverWordLift s rels hrel,coverWordLift_ker s rels hrel hker⟩
lemma presentationSection_lift (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (w : FreeGroup S) :
    presentationSection s rels hrel hs hker (FreeGroup.lift s w) = coverWordLift s rels hrel w :=
  MonoidHom.liftOfRightInverse_comp_apply ..
lemma presentationSection_fst (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) (g : G) :
    (presentationSection s rels hrel hs hker g).1 = g := by
  obtain ⟨w,rfl⟩ := hs g
  rw [presentationSection_lift]
  exact wordLift_fst s w
end GroupRingTopology.Cayley

end

end OAI
