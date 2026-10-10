import OAI.GroupTheory.UniversalGroup.PathExtensions

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace UniversalFInfinity.Milnor
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
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Attachment
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

def radialRetraction : C(punctured a,X) :=
  puncturedLift a (.id X) (fun i => (a i).comp radialSphere)
    (fun i x => by simp only [ContinuousMap.comp_apply,radialSphere_boundary,ContinuousMap.id_apply])

@[simp] lemma radialRetraction_base (x : X) : radialRetraction a (puncturedBase a x) = x := rfl
@[simp] lemma radialRetraction_cell (i : ι) (d : PuncturedDisk n) :
    radialRetraction a (puncturedCell a i d) = a i (radialSphere d) := by
  exact puncturedLift_cell _ _ _ _ _ _

def radialPaths : C(punctured a,C(unitInterval,Space a)) := by
  let f : C(X × unitInterval,Space a) := ⟨fun p => base a p.1,(continuous_base a).comp continuous_fst⟩
  let g (i : ι) : C(PuncturedDisk n × unitInterval,Space a) :=
    (cell a i).comp (radialDisk.comp ⟨Prod.swap,continuous_swap⟩)
  have h (i : ι) (x : Sphere n) : (g i).curry (puncturedBoundary x) = f.curry (a i x) := by
    ext t
    change cell a i (radialDisk (t,puncturedBoundary x)) = base a (a i x)
    rw [radialDisk_boundary,cell_boundary]
  exact puncturedLift a f.curry (fun i => (g i).curry) h

@[simp] lemma radialPaths_base (x : X) (t : unitInterval) :
    radialPaths a (puncturedBase a x) t = base a x := rfl
@[simp] lemma radialPaths_cell (i : ι) (d : PuncturedDisk n) (t : unitInterval) :
    radialPaths a (puncturedCell a i d) t = cell a i (radialDisk (t,d)) := by
  unfold radialPaths
  rw [puncturedLift_cell]
  rfl

def puncturedInclusion : C(punctured a,Space a) := ⟨Subtype.val,continuous_subtype_val⟩
def radialEnd : C(punctured a,Space a) := (⟨base a,continuous_base a⟩ : C(X,Space a)).comp (radialRetraction a)

def radialHomotopy : (puncturedInclusion a).Homotopy (radialEnd a) where
  toFun p := radialPaths a p.2 p.1
  continuous_toFun := (radialPaths a).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_zero]
      rfl
  map_one_left z := by
    rcases punctured_surjective a z with ⟨x,rfl⟩ | ⟨i,d,rfl⟩
    · rfl
    · rw [radialPaths_cell,radialDisk_one,cell_boundary]
      change base a (a i (radialSphere d)) = base a (radialRetraction a (puncturedCell a i d))
      rw [radialRetraction_cell]

@[simp] lemma radialHomotopy_base (x : X) (t : unitInterval) :
    radialHomotopy a (t,puncturedBase a x) = base a x := rfl

lemma cell_eq_openCell_iff (i j : ι) (d : Disk n) (x : OpenDisk n) :
    cell a i d = openCell a j x ↔ i = j ∧ d.1 = x.1 := by
  classical
  constructor
  · intro h
    by_cases hd : d.1 ∈ ball (0 : Fin n → ℝ) 1
    · have hi : cell a i d = Sum.inr ⟨i,⟨d.1,hd⟩⟩ :=
        cell_interior a i ⟨d.1,hd⟩
      rw [hi] at h
      have hh : (⟨i,⟨d.1,hd⟩⟩ : Σ _ : ι, OpenDisk n) = ⟨j,x⟩ := Sum.inr_injective h
      exact ⟨congrArg Sigma.fst hh,congrArg (fun p : Σ _ : ι, OpenDisk n => p.2.1) hh⟩
    · let s : Sphere n := ⟨d.1,by
        have hm := d.2
        simp only [mem_sphere,mem_ball,mem_closedBall] at *
        exact le_antisymm hm (le_of_not_gt hd)⟩
      have hi : cell a i d = base a (a i s) := cell_boundary a i s
      rw [hi] at h
      cases h
  · rintro ⟨rfl,h⟩
    have hd : d = interior n x := Subtype.ext h
    rw [hd,cell_interior]
    rfl

lemma openCell_disjoint (i j : ι) (hij : i ≠ j) :
    Disjoint (Set.range (openCell a i)) (Set.range (openCell a j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,rfl⟩ ⟨y,h⟩
  exact hij (congrArg Sigma.fst (Sum.inr_injective h)).symm

lemma openCell_selection_closed {I : Type*} (c : I → ι) (hc : Function.Injective c)
    (x : I → OpenDisk n) (S : Set (Space a))
    (hS : S ⊆ Set.range (fun i => openCell a (c i) (x i))) : IsClosed S := by
  rw [isClosed_iff]
  constructor
  · have h : base a ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨i,hi⟩ := hS hy
      cases hi
    rw [h]
    exact isClosed_empty
  · intro j
    suffices (cell a j ⁻¹' S).Subsingleton from this.finite.isClosed
    intro d hd e he
    obtain ⟨i,hi⟩ := hS hd
    obtain ⟨k,hk⟩ := hS he
    have hdi := (cell_eq_openCell_iff a j (c i) d (x i)).mp hi.symm
    have hek := (cell_eq_openCell_iff a j (c k) e (x k)).mp hk.symm
    have hik : i = k := hc (hdi.1.symm.trans hek.1)
    subst k
    exact Subtype.ext (hdi.2.trans hek.2.symm)

lemma compact_finitely_many_openCells {K : Set (Space a)} (hK : IsCompact K) :
    {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}.Finite := by
  classical
  let I := {i : ι | (K ∩ Set.range (openCell a i)).Nonempty}
  have hchoice (i : I) : ∃ x : OpenDisk n, openCell a i.1 x ∈ K := by
    obtain ⟨z,hz,⟨x,hx⟩⟩ := i.2
    exact ⟨x,hx ▸ hz⟩
  choose x hx using hchoice
  let y : I → Space a := fun i => openCell a i.1 (x i)
  have hyinj : Function.Injective y := by
    intro i j h
    apply Subtype.ext
    exact congrArg Sigma.fst (Sum.inr_injective h)
  have hclosed : ∀ S ⊆ Set.range y, IsClosed S :=
    openCell_selection_closed a Subtype.val Subtype.val_injective x
  have hcompact : IsCompact (Set.range y) := hK.of_isClosed_subset
    (hclosed _ subset_rfl) (Set.range_subset_iff.mpr hx)
  have hdisc : IsDiscrete (Set.range y) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hclosed S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdisc
  have : Finite I := (Set.finite_range_iff hyinj).mp hrange
  exact Set.toFinite I

end UniversalFInfinity.Attachment

open Set Topology
namespace UniversalFInfinity.Cellular
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def patchFun (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : X) : Y := by
  classical
  exact if hx : x ∈ A then g ⟨x,hx⟩ else f x

lemma patchFun_on (A : Set X) (f : C(X,Y)) (g : C(A,Y)) (x : A) :
    patchFun A f g x = g x := by simp only [patchFun,dite_eq_left x.2]

lemma patchFun_off (A : Set X) (f : C(X,Y)) (g : C(A,Y)) {x : X} (hx : x ∉ A) :
    patchFun A f g x = f x := by simp only [patchFun,dite_eq_right hx]

lemma continuous_patchFun {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) :
    Continuous (patchFun A f g) := by
  classical
  have hOn : ContinuousOn (patchFun A f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : A.domRestrict (patchFun A f g) = g := funext (patchFun_on A f g)
    rw [heq]
    exact g.continuous
  have h := continuous_if (p := fun x => x ∈ A) (f := patchFun A f g) (g := f)
    (fun x hx => by
      have hxa : x ∈ A := hA.closure_eq ▸ hx.1
      exact (patchFun_on A f g ⟨x,hxa⟩).trans (hboundary ⟨x,hxa⟩ hx))
    (by simpa only [Set.ofPred_mem_eq,hA.closure_eq] using hOn) f.continuous.continuousOn
  convert h using 1
  ext x
  by_cases hx : x ∈ A
  · simp only [ite_eq_left hx]
  · simp only [ite_eq_right hx,patchFun_off A f g hx]

def patch {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) : C(X,Y) :=
  ⟨patchFun A f g,continuous_patchFun hA f g hboundary⟩

lemma patch_on {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) (x : A) :
    patch hA f g hboundary x = g x := patchFun_on A f g x

lemma patch_off {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (hboundary : ∀ (x : A), (x:X) ∈ frontier A → g x = f x) {x : X} (hx : x ∉ A) :
    patch hA f g hboundary x = f x := patchFun_off A f g hx

def patchHomotopy {A : Set X} (hA : IsClosed A) (f : C(X,Y)) (g : C(A,Y))
    (H : (f.restrict A).Homotopy g)
    (hboundary : ∀ (t : unitInterval) (x : A), (x:X) ∈ frontier A → H (t,x) = f x) :
    f.Homotopy (patch hA f g (fun x hx => by simpa using hboundary 1 x hx)) := by
  let B : Set (unitInterval × X) := Prod.snd ⁻¹' A
  let H' : C(B,Y) := ⟨fun z => H (z.1.1,⟨z.1.2,z.2⟩),
    H.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))⟩
  let hB : IsClosed B := hA.preimage continuous_snd
  let F : C(unitInterval × X,Y) := f.comp ⟨Prod.snd,continuous_snd⟩
  have hb : ∀ z : B, (z : unitInterval × X) ∈ frontier B → H' z = F z := by
    intro z hz
    exact hboundary z.1.1 ⟨z.1.2,z.2⟩ (continuous_snd.frontier_preimage_subset A hz)
  refine ⟨patch hB F H' hb,?_,?_⟩
  · intro x
    change patch hB F H' hb (0,x) = f x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(0,x),hx⟩]
      exact H.apply_zero ⟨x,hx⟩
    · exact patch_off hB F H' hb (x := (_,x)) hx
  · intro x
    change patch hB F H' hb (1,x) = patch hA f g _ x
    by_cases hx : x ∈ A
    · rw [patch_on hB F H' hb ⟨(1,x),hx⟩,patch_on hA f g _ ⟨x,hx⟩]
      exact H.apply_one ⟨x,hx⟩
    · rw [patch_off hB F H' hb (x := (_,x)) hx,patch_off hA f g _ hx]
      rfl

end UniversalFInfinity.Cellular

end

end OAI
