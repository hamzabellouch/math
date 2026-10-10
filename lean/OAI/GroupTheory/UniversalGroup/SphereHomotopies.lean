import OAI.GroupTheory.UniversalGroup.Cylinders

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.SphereCube

section
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]

lemma bottom_repr (s : Sphere (n+1)) (h : s.1 0 = -1) :
    rimSphere n (rimBottom n (diskTail (boundary (n+1) s))) = s := by
  apply Subtype.ext
  change (diskCons (diskTail (boundary (n+1) s)) 0).1 = s.1
  exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1)
    (faceTime_eq_zero s h)).symm.trans (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
lemma top_repr (s : Sphere (n+1)) (h : s.1 0 = 1) :
    top n (diskTail (boundary (n+1) s)) = s := by
  apply Subtype.ext
  change (diskCons (diskTail (boundary (n+1) s)) 1).1 = s.1
  exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1)
    (faceTime_eq_one s h)).symm.trans (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
lemma side_repr (s : Sphere (n+1)) (h : (diskTail (boundary (n+1) s)).1 ∈ sphere 0 1) :
    rimSphere n (rimSide n (faceSphere ⟨s,h⟩,faceTime none ⟨s,h⟩)) = s := by
  apply Subtype.ext
  change (diskCons (diskTail (boundary (n+1) s)) (diskTime (boundary (n+1) s))).1 = s.1
  exact congrArg Subtype.val (cons_tail_time (boundary (n+1) s))

variable (F : C(Sphere (n+1),Y)) (g : C(Disk n,Y)) (y : Y)
variable (hr : ∀ x, F (rimSphere n x) = y) (ht : ∀ x, F (top n x) = g x)
variable (H : g.Homotopy (ContinuousMap.const _ y))
variable (hb : ∀ t s, H (t,boundary n s) = y)

def nullTopPaths : C(Disk n,C(unitInterval,Y)) :=
  (H.toContinuousMap.comp ContinuousMap.prodSwap).curry

def nullSpherePaths : C(Sphere (n+1),C(unitInterval,Y)) :=
  cylinderBoundaryMap (ContinuousMap.const _ (ContinuousMap.const _ (ContinuousMap.const _ y)))
    ((ContinuousMap.const _ (ContinuousMap.const _ y)).prodMk (nullTopPaths g y H)) (by
      intro s
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        exact (hb t s).symm)

include hr ht in
lemma nullSphere_zero (s : Sphere (n+1)) : nullSpherePaths g y H hb s 0 = F s := by
  rcases sphere_split s with h | h | h
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨s,h⟩]
    change y = F s
    rw [← bottom_repr s h,hr]
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨s,h⟩]
    change H (0,diskTail (boundary (n+1) s)) = F s
    rw [ContinuousMap.Homotopy.apply_zero,← ht,top_repr s h]
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ none ⟨s,h⟩]
    change y = F s
    rw [← side_repr s h,hr]

lemma nullSphere_one (s : Sphere (n+1)) : nullSpherePaths g y H hb s 1 = y := by
  rcases sphere_split s with h | h | h
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨s,h⟩]; rfl
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨s,h⟩]
    exact H.apply_one _
  · rw [nullSpherePaths,cylinderBoundaryMap_face _ _ _ none ⟨s,h⟩]; rfl

def nullSphere : F.Homotopy (ContinuousMap.const _ y) where
  toFun p := nullSpherePaths g y H hb p.2 p.1
  continuous_toFun := continuous_eval.comp (((nullSpherePaths g y H hb).continuous.comp continuous_snd).prodMk continuous_fst)
  map_zero_left s := nullSphere_zero F g y hr ht H hb s
  map_one_left s := nullSphere_one g y H hb s

end

section
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v
variable {n : ℕ} {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

def basedDiskLoop (g : C(Disk n,Y)) (y : Y) (hg : ∀ s, g (boundary n s) = y) : GenLoop (Fin n) Y y :=
  ⟨g.comp (DiskCube.fromCube n),by
    intro x hx
    exact hg ⟨_,DiskCube.from_boundary n x hx⟩⟩

theorem killsSpheres_of_null_cubes [PathConnectedSpace Y] (y : Y) (q : C(Y,Z))
    (hq : ∀ p : GenLoop (Fin n) Y y,
      Nonempty ((q.comp p.1).HomotopyRel (ContinuousMap.const _ (q y)) (Cube.boundary (Fin n)))) :
    KillsSpheres q (n+1) := by
  intro f
  obtain ⟨K⟩ := rim_nullhomotopy f y
  let g := normalizedTop f y K
  let p := basedDiskLoop g y (normalizedTop_boundary f y K)
  obtain ⟨L⟩ := hq p
  let H : (q.comp g).Homotopy (ContinuousMap.const _ (q y)) :=
    { toFun := fun v => L (v.1,DiskCube.toCube n v.2)
      continuous_toFun := L.continuous.comp
        (continuous_fst.prodMk ((DiskCube.toCube n).continuous.comp continuous_snd))
      map_zero_left := by
        intro x
        change L (0,DiskCube.toCube n x) = _
        rw [L.apply_zero]
        change q (g (DiskCube.fromCube n (DiskCube.toCube n x))) = q (g x)
        rw [DiskCube.from_to]
      map_one_left := by intro x; exact L.apply_one _ }
  have hb : ∀ t s, H (t,boundary n s) = q y := by
    intro t s
    exact L.eq_snd t (DiskCube.to_boundary n s)
  let J := nullSphere ((q.comp (normalizedSphere f y K))) (q.comp g) (q y)
    (fun x => congrArg q (normalizedSphere_rim f y K x))
    (fun x => congrArg q (normalizedSphere_top f y K x)) H hb
  let N := (ContinuousMap.Homotopy.refl q).comp (normalizeHomotopy f y K)
  let : Nonempty (SphereTopology.Sphere (n+1)) := SphereTopology.sphere_nonempty n
  obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic (N.trans J).symm
  exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩

end

open scoped Topology Topology.Homotopy
universe u v
variable {n : ℕ} {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
lemma killsSpheres_of_homotopy_zero [Nonempty (Fin n)] [PathConnectedSpace Y]
    (y : Y) (q : C(Y,Z))
    (hq : ∀ a : HomotopyGroup (Fin n) Y y, HomotopyFunctor.map q rfl a = 1) :
    Cellular.KillsSpheres q (n+1) := by
  apply killsSpheres_of_null_cubes y q
  intro p
  have hh := hq (Quotient.mk' p)
  change Quotient.mk' (HomotopyFunctor.loopMap q rfl p) = Quotient.mk' GenLoop.const at hh
  exact Quotient.exact hh
end UniversalFInfinity.SphereCube

namespace UniversalFInfinity.Cellular
open Set Metric Topology
universe u v
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
variable (Y : ℕ → Type v) [∀ i,TopologicalSpace (Y i)] (q : ∀ i,C(Y i,Y (i+1)))

def towerComposite (f : C(X,Y 0)) : ∀ i,C(X,Y i)
  | 0 => f
  | i+1 => (q i).comp (towerComposite f i)

variable (f g : C(X,Y 0)) (hq : ∀ i,KillsSpheres (q i) (i+1))

def towerPartialHomotopy : ∀ i,PartialHomotopy (C := (Set.univ : Set X))
    (towerComposite Y q f i) (towerComposite Y q g i) i
  | 0 => PartialHomotopy.start f g
  | i+1 => (towerPartialHomotopy i).next (q i) (hq i)

def towerHomotopy (d : ℕ) (hd : Skeleton (Set.univ : Set X) d = Set.univ) :
    (towerComposite Y q f d).Homotopy (towerComposite Y q g d) :=
  (towerPartialHomotopy Y q f g hq d).toHomotopy hd

end UniversalFInfinity.Cellular

namespace UniversalFInfinity.SphereCube
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v w
variable {n : ℕ} {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

lemma rim_nullhomotopy_of_joined (r : C(X,Y)) (y : Y)
    (hy : ∀ x, Joined (r x) y) (f : C(Sphere (n+1),X)) :
    Nonempty (((r.comp f).comp (rimSphere n)).Homotopy (ContinuousMap.const _ y)) := by
  let := rim_contractible n
  obtain ⟨p,⟨H⟩⟩ := id_nullhomotopic (Cylinder.Rim n)
  let F := (r.comp f).comp (rimSphere n)
  let K := (ContinuousMap.Homotopy.refl F).comp H
  let q : Path (F p) y := (hy (f (rimSphere n p))).somePath
  let L : (ContinuousMap.const (Cylinder.Rim n) (F p)).Homotopy (ContinuousMap.const _ y) :=
    { toFun := fun z => q z.1
      continuous_toFun := q.continuous.comp continuous_fst
      map_zero_left := fun _ => q.source
      map_one_left := fun _ => q.target }
  exact ⟨K.trans L⟩

lemma fills_of_rim_nullhomotopy (y : Y) (q : C(Y,Z))
    (hq : ∀ p : GenLoop (Fin n) Y y,
      Nonempty ((q.comp p.1).HomotopyRel (ContinuousMap.const _ (q y)) (Cube.boundary (Fin n))))
    (f : C(Sphere (n+1),Y))
    (K : (f.comp (rimSphere n)).Homotopy (ContinuousMap.const _ y)) :
    ∃ F : C(Disk (n+1),Z), ∀ x, F (boundary (n+1) x) = q (f x) := by
  let g := normalizedTop f y K
  let p := basedDiskLoop g y (normalizedTop_boundary f y K)
  obtain ⟨L⟩ := hq p
  let H : (q.comp g).Homotopy (ContinuousMap.const _ (q y)) :=
    { toFun := fun v => L (v.1,DiskCube.toCube n v.2)
      continuous_toFun := L.continuous.comp
        (continuous_fst.prodMk ((DiskCube.toCube n).continuous.comp continuous_snd))
      map_zero_left := by
        intro x
        change L (0,DiskCube.toCube n x) = _
        rw [L.apply_zero]
        change q (g (DiskCube.fromCube n (DiskCube.toCube n x))) = q (g x)
        rw [DiskCube.from_to]
      map_one_left := by intro x; exact L.apply_one _ }
  have hb : ∀ t s, H (t,boundary n s) = q y := by
    intro t s
    exact L.eq_snd t (DiskCube.to_boundary n s)
  let J := nullSphere (q.comp (normalizedSphere f y K)) (q.comp g) (q y)
    (fun x => congrArg q (normalizedSphere_rim f y K x))
    (fun x => congrArg q (normalizedSphere_top f y K x)) H hb
  let N := (ContinuousMap.Homotopy.refl q).comp (normalizeHomotopy f y K)
  let : Nonempty (SphereTopology.Sphere (n+1)) := SphereTopology.sphere_nonempty n
  obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic (N.trans J).symm
  exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩

lemma killsSpheres_of_connected_image [Nonempty (Fin n)] (r : C(X,Y)) (y : Y)
    (hy : ∀ x, Joined (r x) y) (q : C(Y,Z)) (z : Z) (hbase : q y = z)
    (hq : ∀ a : HomotopyGroup (Fin n) Y y, HomotopyFunctor.map q hbase a = 1) :
    KillsSpheres (q.comp r) (n+1) := by
  subst z
  intro f
  obtain ⟨K⟩ := rim_nullhomotopy_of_joined r y hy f
  apply fills_of_rim_nullhomotopy y q (fun p => ?_) (r.comp f) K
  have hh := hq (Quotient.mk' p)
  change Quotient.mk' (HomotopyFunctor.loopMap q rfl p) = Quotient.mk' GenLoop.const at hh
  exact Quotient.exact hh
end UniversalFInfinity.SphereCube

namespace UniversalFInfinity.Cellular
open Set Metric Topology
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
lemma KillsSpheres.post {q : C(X,Y)} {n : ℕ} (hq : KillsSpheres q n) (r : C(Y,Z)) :
    KillsSpheres (r.comp q) n := by
  intro a
  obtain ⟨d,hd⟩ := hq a
  exact ⟨r.comp d,fun x => congrArg r (hd x)⟩
lemma joined_of_killsSpheres_one (q : C(X,Y)) (hq : KillsSpheres q 1) (x y : X) :
    Joined (q x) (q y) := by
  classical
  let a : C(Sphere 1,X) := ⟨fun s => if s = Cayley.minus then x else y,continuous_of_discreteTopology⟩
  obtain ⟨d,hd⟩ := hq a
  have hm : a Cayley.minus = x := ite_eq_left rfl
  have hp : a Cayley.plus = y := by
    apply ite_eq_right
    intro h
    have := congrArg (fun z : Sphere 1 => z.1 0) h
    norm_num [Cayley.plus,Cayley.minus] at this
  have hh := (PathConnectedSpace.joined (boundary 1 Cayley.minus) (boundary 1 Cayley.plus)).map d.continuous
  rw [hd,hd,hm,hp] at hh
  exact hh
end UniversalFInfinity.Cellular
namespace UniversalFInfinity.Milnor

section
open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
open scoped Topology.Homotopy
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

lemma uniform_low_fp (S : Shapes G) :
    ∃ (T : Shapes G) (hST : S ⊆ T), ∀ n : ℕ, n = 1 ∨ n = 2 →
      KillsSpheres (stageIncl G S T hST) n := by
  obtain ⟨m,q,hq,R,hR,hker⟩ := Group.IsFinitelyPresented.out (G := G)
  let s : Fin m → G := fun i => q (FreeGroup.of i)
  have hs : FreeGroup.lift s = q := by
    apply FreeGroup.ext_hom
    intro i
    exact FreeGroup.lift_apply_of
  have hrel : ∀ r ∈ R, FreeGroup.lift s r = 1 := by
    intro r hr
    rw [hs]
    exact show r ∈ q.ker from hker.symm ▸ Subgroup.subset_normalClosure hr
  apply uniform_low_connectivity s R hrel hR
  · rwa [hs]
  · rw [hs]; exact hker.symm

def Represents {S T : Shapes G} (f : G →* G) (q : C(Stage G S,Stage G T)) : Prop :=
  ∀ x, (q x).1 = x.1.mapDomain (vertexMap f id)

lemma uniform_diagram_sphere_ghost (k : Index → G →* G) (hk : IsDiagram k)
    (S : Shapes G) (n : ℕ) :
    ∃ (T : Shapes G) (q : C(Stage G S,Stage G T)),
      Represents (k (.inl P₂.identity)) q ∧ KillsSpheres q n := by
  classical
  let f := k (.inl P₂.identity)
  obtain ⟨R,hSR,hR⟩ := uniform_low_fp S
  let e := stageIncl G S R hSR
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let T := imageShapes f id (basedShapes G R)
    let a := stageMap f id R T (image_stage_valid f id R Function.injective_id)
    refine ⟨T,a.comp e,fun _ => rfl,?_⟩
    intro b
    let : Nonempty (Stage G T) := ⟨stagePoint G T⟩
    obtain ⟨d,hd⟩ := SphereTopology.fill_zero (a.comp (e.comp b))
    exact ⟨d,hd⟩
  obtain hn | hn := (lt_or_ge n 3)
  · let T := imageShapes f id (basedShapes G R)
    let a := stageMap f id R T (image_stage_valid f id R Function.injective_id)
    refine ⟨T,a.comp e,fun _ => rfl,?_⟩
    exact (hR n (by omega)).post a
  · let m := n-1
    have hm : n = m+1 := by omega
    have hm2 : 2 ≤ m := by omega
    let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
    obtain ⟨T,hT,hzero⟩ := diagram_uniform_homotopy_killing (Fin m) k hk R
    let a := (stageIncl G _ T hT).comp
      (stageMap f id R _ (image_stage_valid f id R Function.injective_id))
    have ha : a (stagePoint G R) = stagePoint G T := by
      change stageIncl G _ T hT (stageMap f id R _ _ (stagePoint G R)) = _
      rw [stageMap_point f id R _ _ rfl]
      rfl
    have hz : ∀ z : HomotopyGroup (Fin m) (Stage G R) (stagePoint G R),
        HomotopyFunctor.map a ha z = 1 := by
      intro z
      have hz := DFunLike.congr_fun hzero z
      change HomotopyFunctor.map (stageIncl G _ T hT) rfl
        (HomotopyFunctor.map (stageMap f id R _ _) (stageMap_point f id R _ _ rfl) z) = 1 at hz
      rw [HomotopyFunctor.map_comp] at hz
      exact hz
    refine ⟨T,a.comp e,fun _ => rfl,?_⟩
    rw [hm]
    apply SphereCube.killsSpheres_of_connected_image e (stagePoint G R) ?_ a (stagePoint G T) ha hz
    intro x
    exact joined_of_killsSpheres_one e (hR 1 (Or.inl rfl)) x (stagePoint G S)
end
open Set Metric Topology Cellular UniversalFInfinity.Simplicial ConcreteEnvelopes
variable {G : Type} [Group G] [Group.IsFinitelyPresented G]
  [TopologicalSpace G] [DiscreteTopology G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

omit [Group.IsFinitelyPresented G] [TopologicalSpace G] [DiscreteTopology G] in
lemma stage_bounded_dimension (S : Shapes G) :
    ∃ d : ℕ, Skeleton (univ : Set (Stage G S)) d = univ := by
  classical
  let d := (basedShapes G S).sup Finset.card
  refine ⟨d,Set.eq_univ_of_forall (fun x => ?_)⟩
  have hx : x ∈ (univ : Set (Stage G S)) := Set.mem_univ _
  rw [←CWComplex.iUnion_openCell_eq_complex (C := (univ : Set (Stage G S)))] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨n,i,hi⟩ := hx
  obtain ⟨g,s,hs,his⟩ := i.1.2.2
  have hn : n < d := by
    have hcard := Finset.card_le_card his
    rw [translate_card] at hcard
    rw [i.2] at hcard
    have hd := Finset.le_sup (f := Finset.card) hs
    omega
  exact CWComplex.skeletonLT_mono (C := (univ : Set (Stage G S)))
    (m := (n : ℕ∞)+1) (n := (d : ℕ∞)) (by exact_mod_cast Nat.succ_le_of_lt hn)
    (CWComplex.closedCell_subset_skeletonLT n i (CWComplex.openCell_subset_closedCell n i hi))

omit [Group.IsFinitelyPresented G] [TopologicalSpace G] [DiscreteTopology G] in
lemma Represents.comp {S T R : Shapes G} {f g : G →* G}
    {q : C(Stage G S,Stage G T)} {r : C(Stage G T,Stage G R)}
    (hr : Represents g r) (hq : Represents f q) : Represents (g.comp f) (r.comp q) := by
  intro x
  rw [show (r.comp q) x = r (q x) from rfl,hr,hq,←Finsupp.mapDomain_comp]
  rfl

omit [Group.IsFinitelyPresented G] [TopologicalSpace G] [DiscreteTopology G] in
lemma Represents.id (S : Shapes G) : Represents (MonoidHom.id G) (ContinuousMap.id (Stage G S)) := by
  intro x
  change x.1 = x.1.mapDomain _root_.id
  exact (Finsupp.mapDomain_id).symm

def iterateHom {G : Type*} [Group G] (f : G →* G) : ℕ → G →* G
  | 0 => MonoidHom.id G
  | n+1 => f.comp (iterateHom f n)

variable (k : Index → G →* G) (hk : IsDiagram k)
def ghostShapes (S : Shapes G) : ℕ → Shapes G
  | 0 => S
  | n+1 => (uniform_diagram_sphere_ghost k hk (ghostShapes S n) (n+1)).choose

def ghostMap (S : Shapes G) (n : ℕ) :
    C(Stage G (ghostShapes k hk S n),Stage G (ghostShapes k hk S (n+1))) :=
  (uniform_diagram_sphere_ghost k hk (ghostShapes k hk S n) (n+1)).choose_spec.choose
lemma ghostMap_represents (S : Shapes G) (n : ℕ) :
    Represents (k (.inl P₂.identity)) (ghostMap k hk S n) :=
  (uniform_diagram_sphere_ghost k hk (ghostShapes k hk S n) (n+1)).choose_spec.choose_spec.1
lemma ghostMap_kills (S : Shapes G) (n : ℕ) : KillsSpheres (ghostMap k hk S n) (n+1) :=
  (uniform_diagram_sphere_ghost k hk (ghostShapes k hk S n) (n+1)).choose_spec.choose_spec.2

lemma ghostComposite_represents (S : Shapes G) (n : ℕ) :
    Represents (iterateHom (k (.inl P₂.identity)) n)
      (towerComposite (fun i => Stage G (ghostShapes k hk S i)) (ghostMap k hk S)
        (ContinuousMap.id (Stage G S)) n) := by
  induction n with
  | zero => exact Represents.id S
  | succ n ih =>
    exact (ghostMap_represents k hk S n).comp ih

include hk in

theorem diagram_uniform_stage_nullhomotopy (S : Shapes G) :
    ∃ (d : ℕ) (T : Shapes G) (q : C(Stage G S,Stage G T)) (z : Stage G T),
      Represents (iterateHom (k (.inl P₂.identity)) d) q ∧
      Nonempty (q.Homotopy (ContinuousMap.const _ z)) := by
  obtain ⟨d,hd⟩ := stage_bounded_dimension S
  let Y : ℕ → Type := fun i => Stage G (ghostShapes k hk S i)
  let q := ghostMap k hk S
  let a := towerComposite Y q (ContinuousMap.id (Stage G S)) d
  let b := towerComposite Y q (ContinuousMap.const (Stage G S) (stagePoint G S)) d
  have hb : ∀ x,b x = a (stagePoint G S) := by
    intro x
    change towerComposite Y q (ContinuousMap.const (Stage G S) (stagePoint G S)) d x =
      towerComposite Y q (ContinuousMap.id (Stage G S)) d (stagePoint G S)
    clear hd a b
    induction d with
    | zero => rfl
    | succ d ih => exact congrArg (q d) ih
  refine ⟨d,ghostShapes k hk S d,a,a (stagePoint G S),ghostComposite_represents k hk S d,?_⟩
  have H := towerHomotopy Y q (ContinuousMap.id (Stage G S))
    (ContinuousMap.const (Stage G S) (stagePoint G S)) (ghostMap_kills k hk S) d hd
  exact ⟨H.cast rfl (ContinuousMap.ext hb)⟩
end UniversalFInfinity.Milnor

end

end OAI
