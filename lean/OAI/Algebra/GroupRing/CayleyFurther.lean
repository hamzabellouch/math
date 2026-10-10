import Mathlib
import OAI.Algebra.GroupRing.LoopSphere

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Cayley

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
    erw [←hf,smul_cell _ (equivariantFamily_smul (attaching s))]
    change f (cell _ (g*1,i) (edgeParam t)) = _
    rw [_root_.mul_one]

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
end GroupRingTopology.Cayley
namespace GroupRingTopology.Attachment
open Set Metric Topology
universe u v w z
variable {G : Type u} [Group G]
variable {X : Type v} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
variable {Y : Type w} [TopologicalSpace Y] [MulAction G Y] [ContinuousConstSMul G Y]
variable {ι : Type z} {n : ℕ} (a : ι → C(Sphere n,X))

/-- Fill one disk per orbit and translate the fillings, preserving the action. -/
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

/-- Finitely many free cell orbits preserve existence of a compact fundamental set. -/
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
    · erw [smul_cell _ (equivariantFamily_smul a)]
      change Sum.inr p = cell b (p.1.1*1,p.1.2) (interior n p.2)
      erw [mul_one,cell_interior]
      rfl
end GroupRingTopology.Attachment

namespace GroupRingTopology.Milnor
open Set Metric Topology Attachment
universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable {A : Type u} (s : A → G)

omit [DiscreteTopology G] in
lemma group_compactFundamentalSet : CompactFundamentalSet G (X := G) := by
  refine ⟨{1},isCompact_singleton,?_⟩
  intro g
  exact ⟨g,1,Set.mem_singleton _,by simp only [smul_eq_mul,mul_one]⟩

lemma graph_compactFundamentalSet [Finite A] : CompactFundamentalSet G (X := Cayley.Graph s) :=
  Attachment.compactFundamentalSet (Cayley.attaching s) group_compactFundamentalSet

variable (rels : Set (FreeGroup A)) (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)
lemma presentation_compactFundamentalSet [Finite A] (hrels : rels.Finite) :
    CompactFundamentalSet G (X := Cayley.PresentationCover s rels hrel) := by
  let := hrels.to_subtype
  exact Attachment.compactFundamentalSet (Cayley.relatorAttaching s rels hrel)
    (graph_compactFundamentalSet s)

lemma presentation_equivariant_map :
    ∃ f : C(Cayley.PresentationCover s rels hrel,Space G),
      ∀ (g : G) x, f (g • x) = g • f x := by
  let f₀ : C(G,Space G) := ⟨fun g => g • vertex (0,1),continuous_of_discreteTopology⟩
  have hf₀ (g h : G) : f₀ (g • h) = g • f₀ h := mul_smul g h _
  obtain ⟨f₁,_,hf₁⟩ := Attachment.exists_equivariant_extension (Cayley.attaching s) f₀ hf₀
    (sphereFillable (1:G))
  obtain ⟨f₂,_,hf₂⟩ := Attachment.exists_equivariant_extension (Cayley.relatorAttaching s rels hrel)
    f₁ hf₁ (sphereFillable (1:G))
  exact ⟨f₂,hf₂⟩

include hrel in
/-- Finite presentability supplies a coherent group section in ONE Milnor stage.
This is genuine low-dimensional control, not a simply-connected-stage assumption. -/
lemma exists_stage_section [Finite A] (hrels : rels.Finite)
    (hs : Function.Surjective (FreeGroup.lift s))
    (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels) :
    ∃ (S : Shapes G) (x : Stage G S) (τ : G →* PathExtension.Extension G x), ∀ g, (τ g).1 = g := by
  obtain ⟨f,hf⟩ := presentation_equivariant_map s rels hrel
  obtain ⟨S,hS⟩ := equivariant_controlled G (presentation_compactFundamentalSet s rels hrel hrels) f hf
  let F := factorStage G f S hS
  have hF : ∀ (g : G) x, F (g • x) = g • F x := factorStage_smul G f S hS hf
  let x := Cayley.presentationBase s rels hrel (Cayley.vertex s 1)
  let τ := (PathExtension.map F hF x).comp (Cayley.presentationSection s rels hrel hs hker)
  refine ⟨S,F x,τ,?_⟩
  intro g
  exact Cayley.presentationSection_fst s rels hrel hs hker g
end GroupRingTopology.Milnor

namespace GroupRingTopology.Attachment
open Set Metric Topology
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}
variable (a : ι → C(Sphere n,X))

def cellCenter (i : ι) : Space a := openCell a i ⟨0,by simp⟩
def punctured : Set (Space a) := (Set.range (cellCenter a))ᶜ

def rawCoordinate : Space a → (Fin n → ℝ)
  | Sum.inl _ => 0 | Sum.inr p => p.2.1

lemma base_mem_punctured (x : X) : base a x ∈ punctured a := by
  rintro ⟨i,h⟩
  cases h

lemma cell_mem_punctured (i : ι) (d : Disk n) : cell a i d ∈ punctured a ↔ d.1 ≠ 0 := by
  classical
  constructor
  · intro hd hzero
    apply hd
    refine ⟨i,?_⟩
    have heq : d = interior n ⟨0,by simp⟩ := Subtype.ext hzero
    rw [heq,cell_interior]
    rfl
  · intro hzero
    rintro ⟨j,hj⟩
    by_cases h : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d = interior n ⟨d.1,h⟩ := rfl
      rw [heq,cell_interior] at hj
      exact hzero (congrArg (rawCoordinate a) hj).symm
    · let s : Sphere n := ⟨d.1,by
        have hd := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hd (le_of_not_gt h)⟩
      have heq : d = boundary n s := rfl
      rw [heq,cell_boundary] at hj
      cases hj

lemma punctured_open : IsOpen (punctured a) := by
  change IsOpen (Set.range (cellCenter a))ᶜ
  rw [isOpen_compl_iff]
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' Set.range (cellCenter a) = ∅ := by
      ext x
      simp only [mem_preimage,mem_empty_iff_false,iff_false]
      exact base_mem_punctured a x
    rw [h]
    exact isClosed_empty
  · intro i
    have h : cell a i ⁻¹' Set.range (cellCenter a) = {d : Disk n | d.1 = 0} := by
      ext d
      exact not_iff_not.mp (cell_mem_punctured a i d)
    rw [h]
    exact isClosed_eq continuous_subtype_val continuous_const

lemma continuous_punctured {Y : Type*} [TopologicalSpace Y] (F : punctured a → Y)
    (hb : Continuous (fun x : X => F ⟨base a x,base_mem_punctured a x⟩))
    (hc : ∀ i, Continuous (fun d : {d : Disk n // d.1 ≠ 0} =>
      F ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩)) : Continuous F := by
  let q := quotient a
  have hq : IsQuotientMap q := ⟨⟨rfl⟩,quotient_surjective a⟩
  have hp := hq.restrictPreimage_isOpen (punctured_open a)
  apply hp.continuous_iff.mpr
  apply continuous_iff_continuousAt.mpr
  rintro ⟨z,hz⟩
  cases z with
  | inl x =>
    let e : X → q ⁻¹' punctured a := fun x => ⟨Sum.inl x,base_mem_punctured a x⟩
    have he : IsOpenEmbedding e := by
      have hi : IsOpenEmbedding (Sum.inl : X → X ⊕ (Σ _ : ι, Disk n)) := .inl
      exact ⟨hi.isEmbedding.codRestrict (q ⁻¹' punctured a) (fun x => base_mem_punctured a x),by
        have hr : Set.range e = Subtype.val ⁻¹' Set.range Sum.inl := by
          ext z
          simp only [mem_range,mem_preimage,e]
          constructor
          · rintro ⟨x,rfl⟩; exact ⟨x,rfl⟩
          · rintro ⟨x,hx⟩; exact ⟨x,Subtype.ext hx⟩
        rw [hr]
        exact hi.isOpen_range.preimage continuous_subtype_val⟩
    exact (he.continuousAt_iff (g := F ∘ (punctured a).restrictPreimage q)).mp (hb.continuousAt (x := x))
  | inr p =>
    rcases p with ⟨i,d⟩
    have hd : d.1 ≠ 0 := (cell_mem_punctured a i d).mp hz
    let e : {d : Disk n // d.1 ≠ 0} → q ⁻¹' punctured a :=
      fun d => ⟨Sum.inr ⟨i,d.1⟩,(cell_mem_punctured a i d.1).mpr d.2⟩
    have he : IsOpenEmbedding e := by
      have hi : IsOpenEmbedding (fun d : Disk n => (Sum.inr ⟨i,d⟩ : X ⊕ (Σ _ : ι, Disk n))) :=
        IsOpenEmbedding.inr.comp IsOpenEmbedding.sigmaMk
      exact hi.restrict (fun d hd => (cell_mem_punctured a i d).mpr hd)
        (isClosed_eq continuous_subtype_val continuous_const).isOpen_compl
    have hc' : ContinuousAt ((F ∘ (punctured a).restrictPreimage q) ∘ e) ⟨d,hd⟩ := by
      change ContinuousAt (fun d : {d : Disk n // d.1 ≠ 0} =>
        F ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩) ⟨d,hd⟩
      exact (hc i).continuousAt
    have result := (he.continuousAt_iff (g := F ∘ (punctured a).restrictPreimage q)).mp hc'
    exact result

abbrev PuncturedDisk (n : ℕ) := {d : Disk n // d.1 ≠ 0}

def puncturedBoundary (x : Sphere n) : PuncturedDisk n :=
  ⟨boundary n x,by
    intro h
    change x.1 = 0 at h
    have hx := x.2
    simp only [mem_sphere,dist_zero_right] at hx
    rw [h,norm_zero] at hx
    norm_num at hx⟩

def puncturedCell (i : ι) (d : PuncturedDisk n) : punctured a :=
  ⟨cell a i d.1,(cell_mem_punctured a i d.1).mpr d.2⟩

def puncturedBase (x : X) : punctured a := ⟨base a x,base_mem_punctured a x⟩

lemma puncturedCell_boundary (i : ι) (x : Sphere n) :
    puncturedCell a i (puncturedBoundary x) = puncturedBase a (a i x) :=
  Subtype.ext (cell_boundary a i x)

noncomputable def puncturedLift {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x)) : C(punctured a,Y) := by
  classical
  let F : punctured a → Y := fun z => match heq : z.1 with
    | Sum.inl x => f x
    | Sum.inr p => g p.1 ⟨interior n p.2,by
        exact (cell_mem_punctured a p.1 (interior n p.2)).mp
          (by simpa only [cell_interior,← heq] using z.2)⟩
  have hcell (i : ι) : F ∘ puncturedCell a i = g i := by
    funext d
    by_cases hd : d.1.1 ∈ ball (0 : Fin n → ℝ) 1
    · have heq : d.1 = interior n ⟨d.1.1,hd⟩ := rfl
      change F ⟨cell a i d.1,_⟩ = g i d
      have hc : cell a i d.1 = Sum.inr ⟨i,⟨d.1.1,hd⟩⟩ := (congrArg (cell a i) heq).trans (cell_interior a i ⟨d.1.1,hd⟩)
      simp only [hc,F]
      exact congrArg (g i) (Subtype.ext (Subtype.ext rfl))
    · let x : Sphere n := ⟨d.1.1,by
        have hm := d.1.2
        simp only [mem_closedBall,mem_ball,mem_sphere] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have heq : d.1 = boundary n x := rfl
      change F ⟨cell a i d.1,_⟩ = g i d
      have hc : cell a i d.1 = base a (a i x) := (congrArg (cell a i) heq).trans (cell_boundary a i x)
      simp only [hc,base,F]
      exact (h i x).symm.trans (congrArg (g i) (Subtype.ext (Subtype.ext rfl)))
  exact ⟨F,continuous_punctured a F f.continuous (fun i => by
    change Continuous (F ∘ puncturedCell a i)
    rw [hcell]
    exact (g i).continuous)⟩

@[simp] lemma puncturedLift_base {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x)) (x : X) :
    puncturedLift a f g h (puncturedBase a x) = f x := rfl

@[simp] lemma puncturedLift_cell {Y : Type*} [TopologicalSpace Y] (f : C(X,Y))
    (g : ι → C(PuncturedDisk n,Y))
    (h : ∀ i x, g i (puncturedBoundary x) = f (a i x))
    (i : ι) (d : PuncturedDisk n) :
    puncturedLift a f g h (puncturedCell a i d) = g i d := by
  classical
  by_cases hd : d.1.1 ∈ ball (0 : Fin n → ℝ) 1
  · have heq : d.1 = interior n ⟨d.1.1,hd⟩ := rfl
    change puncturedLift a f g h ⟨cell a i d.1,_⟩ = _
    have hc : cell a i d.1 = Sum.inr ⟨i,⟨d.1.1,hd⟩⟩ := (congrArg (cell a i) heq).trans (cell_interior a i ⟨d.1.1,hd⟩)
    simp only [hc,puncturedLift,ContinuousMap.coe_mk]
    exact congrArg (g i) (Subtype.ext (Subtype.ext rfl))
  · let x : Sphere n := ⟨d.1.1,by
      have hm := d.1.2
      simp only [mem_closedBall,mem_ball,mem_sphere] at *
      exact le_antisymm hm (le_of_not_gt hd)⟩
    have hd : d = puncturedBoundary x := rfl
    rw [hd,puncturedCell_boundary,puncturedLift_base,h]

lemma punctured_surjective (z : punctured a) :
    (∃ x, z = puncturedBase a x) ∨ ∃ i d, z = puncturedCell a i d := by
  cases heq : z.1 with
  | inl x => exact Or.inl ⟨x,Subtype.ext heq⟩
  | inr p =>
    have hd : p.2.1 ≠ 0 := (cell_mem_punctured a p.1 (interior n p.2)).mp
      (by simpa only [cell_interior,← heq] using z.2)
    exact Or.inr ⟨p.1,⟨interior n p.2,hd⟩,Subtype.ext (heq.trans (cell_interior a p.1 p.2).symm)⟩

/-- Radial projection of a nonzero disk point onto its sphere. -/
def radialSphere : C(PuncturedDisk n,Sphere n) := by
  have hm (d : PuncturedDisk n) : ‖d.1.1‖⁻¹ • d.1.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,
      abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr d.2)]
  refine ⟨fun d => ⟨‖d.1.1‖⁻¹ • d.1.1,hm d⟩,?_⟩
  exact (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
    (fun d : PuncturedDisk n => norm_ne_zero_iff.mpr d.2)).smul
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk hm

@[simp] lemma radialSphere_boundary (x : Sphere n) : radialSphere (puncturedBoundary x) = x := by
  apply Subtype.ext
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  change ‖x.1‖⁻¹ • x.1 = x.1
  rw [hx,inv_one,one_smul]

/-- Radial straight-line deformation, in the full disk. -/
def radialDisk : C(unitInterval × PuncturedDisk n,Disk n) := by
  let f (p : unitInterval × PuncturedDisk n) :=
    (1-(p.1:ℝ)) • p.2.1.1 + (p.1:ℝ) • (radialSphere p.2).1
  have hm (p : unitInterval × PuncturedDisk n) : f p ∈ closedBall (0 : Fin n → ℝ) 1 :=
    (convex_closedBall (0 : Fin n → ℝ) 1) p.2.1.2
      (sphere_subset_closedBall (radialSphere p.2).2)
      (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)
  have hc : Continuous f :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (radialSphere.continuous.comp continuous_snd)))
  exact ⟨fun p => ⟨f p,hm p⟩,hc.subtype_mk hm⟩

@[simp] lemma radialDisk_zero (d : PuncturedDisk n) : radialDisk (0,d) = d.1 := by
  apply Subtype.ext
  simp [radialDisk]
@[simp] lemma radialDisk_one (d : PuncturedDisk n) : radialDisk (1,d) = boundary n (radialSphere d) := by
  apply Subtype.ext
  simp [radialDisk,boundary]
@[simp] lemma radialDisk_boundary (t : unitInterval) (x : Sphere n) :
    radialDisk (t,puncturedBoundary x) = boundary n x := by
  apply Subtype.ext
  simp only [radialDisk,ContinuousMap.coe_mk,radialSphere_boundary]
  change (1-(t:ℝ)) • x.1 + (t:ℝ) • x.1 = x.1
  rw [← add_smul,sub_add_cancel,one_smul]

end GroupRingTopology.Attachment

end

end OAI
