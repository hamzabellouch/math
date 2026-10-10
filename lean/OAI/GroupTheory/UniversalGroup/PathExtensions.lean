import OAI.GroupTheory.UniversalGroup.Cayley

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.PathExtension

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
end UniversalFInfinity.PathExtension
namespace UniversalFInfinity.Cayley

section
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
  refine (cell_boundary (equivariantFamily (G := G) (relatorAttaching s rels hrel))
    (1,r) z).trans ?_
  change base _ ((1 : G) • relatorAttaching s rels hrel r z) = _
  rw [one_smul]
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
end
section
open Set Metric Topology Attachment PathExtension
open scoped unitInterval
universe u v
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G)
variable {Y : Type v} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable (f : C(Graph s,Y)) (hf : ∀ (g : G) x, f (g • x) = g • f x)
include hf in
omit [ContinuousConstSMul G Y] in
lemma vertex_action (g : G) : f (vertex s g) = g • f (vertex s 1) := by
  rw [← hf,smul_vertex,_root_.mul_one]

lemma pathGenerator_equal (i : S) : Q.Equal (pathGenerator s i).2 (Path.Homotopic.Quotient.mk (edge s 1 i)) := by
  refine ⟨rfl,?_,?_⟩
  · rw [smul_vertex]; simp only [_root_.one_mul,_root_.mul_one]; rfl
  · exact Path.Homotopic.hpath_hext (fun _ => rfl)

include hf in
lemma edge_smul_equal (g : G) (i : S) :
    Q.Equal (((Path.Homotopic.Quotient.mk (edge s 1 i)).map f).map (smulMap g))
      (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) := by
  refine ⟨(vertex_action s f hf g).symm,?_,?_⟩
  · change g • f (vertex s (1*s i)) = f (vertex s (g*s i))
    rw [←hf,smul_vertex,_root_.one_mul]
  · apply Path.Homotopic.hpath_hext
    intro t
    change g • f (cell _ ((1:G),i) (edgeParam t)) = f (cell _ (g,i) (edgeParam t))
    refine (hf g _).symm.trans (congrArg f ?_)
    refine (smul_cell _ (equivariantFamily_smul (attaching s)) g (1,i) _).trans ?_
    exact congrArg (fun first : G => cell _ (first,i) (edgeParam t)) (_root_.mul_one g)

variable (τ : G →* PathExtension.Extension G (f (vertex s 1)))
variable (hτ : ∀ g, (τ g).1 = g)
def coherentClass (g : G) : Path.Homotopic.Quotient (f (vertex s 1)) (f (vertex s g)) :=
  (τ g).2.cast rfl (by rw [hτ]; exact vertex_action s f hf g)
def coherentPath (g : G) : Path (f (vertex s 1)) (f (vertex s g)) :=
  (Path.Homotopic.Quotient.mk_surjective (coherentClass s f hf τ hτ g)).choose
lemma coherentPath_equal (g : G) : Q.Equal (Path.Homotopic.Quotient.mk (coherentPath s f hf τ hτ g)) (τ g).2 :=
  (Q.Equal.ofEq (Path.Homotopic.Quotient.mk_surjective (coherentClass s f hf τ hτ g)).choose_spec).trans
    (Q.cast_equal _ _ _)

variable (hgen : ∀ i, Q.Equal (τ (s i)).2 (Path.Homotopic.Quotient.mk ((edge s 1 i).map f.continuous)))
include hgen in
lemma coherentPath_edge (g : G) (i : S) :
    ((coherentPath s f hf τ hτ g).trans ((edge s g i).map f.continuous)).Homotopic
      (coherentPath s f hf τ hτ (g*s i)) := by
  apply Path.Homotopic.Quotient.exact
  change (Path.Homotopic.Quotient.mk (coherentPath s f hf τ hτ g)).trans
    (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) = _
  apply eq_of_heq
  apply Q.Equal.path
  have he : Q.Equal ((τ (s i)).2.map (smulMap (τ g).1))
      (Path.Homotopic.Quotient.mk ((edge s g i).map f.continuous)) := by
    apply ((hgen i).map (smulMap (τ g).1)).trans
    rw [hτ]
    exact edge_smul_equal s f hf g i
  apply (Q.Equal.comp (coherentPath_equal s f hf τ hτ g) he.symm).trans
  apply (mul_path_equal (τ g) (τ (s i))).symm.trans
  have hm : Q.Equal (τ g * τ (s i)).2 (τ (g*s i)).2 := by
    rw [←τ.map_mul]
    exact .refl _
  exact hm.trans (coherentPath_equal s f hf τ hτ (g*s i)).symm

def nullhomotopyOfSection : f.Homotopy (.const _ (f (vertex s 1))) :=
  graphNullhomotopy s f (f (vertex s 1)) (coherentPath s f hf τ hτ)
    (coherentPath_edge s f hf τ hτ hgen)
end
open PathExtension Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
variable (hs : Function.Surjective (FreeGroup.lift s))
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)
lemma presentationSection_generator (i : S) :
    Q.Equal (presentationSection s rels hrel hs hker (s i)).2
      (Path.Homotopic.Quotient.mk ((edge s 1 i).map (presentationBase s rels hrel).continuous)) := by
  have hh : presentationSection s rels hrel hs hker (s i) =
      PathExtension.map (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1)
        (pathGenerator s i) := by
    simpa only [FreeGroup.lift_apply_of,coverWordLift,MonoidHom.comp_apply,wordLift]
      using presentationSection_lift s rels hrel hs hker (FreeGroup.of i)
  rw [hh]
  exact (PathExtension.mapFun_equal (presentationBase s rels hrel) (presentationBase_smul s rels hrel) (vertex s 1) (pathGenerator s i)).trans
    ((pathGenerator_equal s i).map (presentationBase s rels hrel))

def presentationGraphNullhomotopy :
    (presentationBase s rels hrel).Homotopy
      (.const _ (presentationBase s rels hrel (vertex s 1))) :=
  nullhomotopyOfSection s (presentationBase s rels hrel) (presentationBase_smul s rels hrel)
    (presentationSection s rels hrel hs hker) (presentationSection_fst s rels hrel hs hker)
    (presentationSection_generator s rels hrel hs hker)
end UniversalFInfinity.Cayley
namespace UniversalFInfinity.Attachment
open Set Metric Topology
universe u v w z
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : Type z} {n : ℕ} (a : ι → C(Sphere n,X))

lemma exists_equivariant_extension (f : C(X,Y))
    (hf : ∀ (g : G) x, f (g • x) = g • f x) (hY : Cellular.SphereFillable Y) :
    ∃ F : C(Space (equivariantFamily (G := G) a),Y),
      (∀ x, F (base _ x) = f x) ∧ (∀ (g : G) x, F (g • x) = g • F x) := by
  choose e he using fun i => hY n (f.comp (a i))
  let b : FreeIndex G ι → C(Disk n,Y) := fun i =>
    ⟨fun d => i.1 • e i.2 d,(continuous_const_smul i.1).comp (e i.2).continuous⟩
  have hb (i : FreeIndex G ι) (x : Sphere n) :
      b i (boundary n x) = f (equivariantFamily a i x) := by
    change i.1 • e i.2 (Cellular.boundary n x) = f (i.1 • a i.2 x)
    rw [he,hf]
    rfl
  refine ⟨lift _ f b hb,fun _ => rfl,?_⟩
  intro g x
  cases x with
  | inl x => exact hf g x
  | inr p => exact (mul_smul g p.1.1 (e p.1.2 (interior n p.2)))

lemma compactFundamentalSet [Finite ι] (hX : Milnor.CompactFundamentalSet G (X := X)) :
    Milnor.CompactFundamentalSet G (X := Space (equivariantFamily (G := G) a)) := by
  let b := equivariantFamily (G := G) a
  obtain ⟨K,hK,hcov⟩ := hX
  let L : Set (Space b) := (base b '' K) ∪ ⋃ i : ι, Set.range (cell b ((1:G),i))
  refine ⟨L,(hK.image (continuous_base b)).union (isCompact_iUnion (fun i =>
    isCompact_range (cell b ((1:G),i)).continuous)),?_⟩
  intro x
  cases x with
  | inl x =>
    obtain ⟨g,y,hy,rfl⟩ := hcov x
    exact ⟨g,base b y,Or.inl ⟨y,hy,rfl⟩,rfl⟩
  | inr p =>
    refine ⟨p.1.1,cell b ((1:G),p.1.2) (interior n p.2),?_,?_⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨p.1.2,Set.mem_range_self _⟩)
    · refine Eq.trans ?_ (congrArg (fun point : Space b => p.1.1 • point)
        (cell_interior b (1,p.1.2) p.2)).symm
      exact congrArg (fun first : G => openCell b (first,p.1.2) p.2)
        (mul_one p.1.1).symm
end UniversalFInfinity.Attachment

end

end OAI
