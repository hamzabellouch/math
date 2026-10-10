import OAI.GroupTheory.BooneHigman.TwistedSimplicity

namespace OAI

noncomputable section

/-!
Coordinate grids, binary trees, and tree-pair representatives.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma count_flatMap_ge {I : Type*} (f : I → List X) (l : List I) {i : I}
    (hi : i∈l) (x : X) : (f i).count x≤(l.flatMap f).count x := by
  classical
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.flatMap_cons,List.count_append]
    rcases List.mem_cons.mp hi with rfl|hi
    · omega
    · exact (ih hi).trans (Nat.le_add_left _ _)

lemma extends_of_compatible_of_length_le {p q : Prefix X} (h : p.Compatible q)
    (hl : ∀ x,(p.word x).length≤(q.word x).length) : p.Extends q := by
  intro x
  have hp := (mem_range_iff p _).mp (commonPoint_mem_left h) x
  have hq := (mem_range_iff q _).mp (commonPoint_mem_right h) x
  rw [← hp,← hq]
  exact Stream'.take_prefix_take_left _ _ _ (hl x)

/-- A finite list of splitting coordinates can dominate any finite prefix. -/
lemma exists_length_bound (p : Prefix X) :
    ∃ l : List X, ∀ x,(p.word x).length≤l.count x := by
  classical
  let S := p.finite_support.toFinset
  let l := S.toList.flatMap (fun x => List.replicate (p.word x).length x)
  refine ⟨l,?_⟩
  intro x
  by_cases hx : p.word x=[]
  · simp [hx]
  · have hxS : x∈S.toList := by simpa [S] using hx
    have hc := count_flatMap_ge (fun x => List.replicate (p.word x).length x) S.toList hxS x
    simpa using hc

end Prefix
namespace Partition
variable {X : Type v}

/-- Repeated simultaneous bisections, recording all colours with multiplicity.
This is a genuine finite forest partition, not an assumed normal form. -/
abbrev grid : List X → Partition X
  | [] => trivial
  | x::l => (bit x).allRefine (grid l)

@[simp] lemma grid_length (l : List X) (i : (grid l).index) (x : X) :
    (((grid l).brick i).word x).length = l.count x := by
  classical
  induction l with
  | nil => simp [grid,trivial,Prefix.empty]
  | cons y l ih =>
      change ((Prefix.oneBit y i.1).word x ++ ((grid l).brick i.2).word x).length = _
      rw [List.length_append,ih]
      by_cases hxy : x=y
      · subst y; simp [Nat.add_comm]
      · simp [hxy,Ne.symm hxy]

/-- Any finite collection of bricks has a single grid fine enough for every
nonempty intersection to be an entire grid cell. -/
lemma exists_grid_bound {I : Type} [Fintype I] (p : I → Prefix X) :
    ∃ l : List X,∀ i j,p i |>.Compatible ((grid l).brick j) →
      (p i).Extends ((grid l).brick j) := by
  classical
  choose l hl using fun i => (p i).exists_length_bound
  let L := (Finset.univ.toList.flatMap l)
  refine ⟨L,?_⟩
  intro i j hij
  apply Prefix.extends_of_compatible_of_length_le hij
  intro x
  rw [grid_length]
  exact (hl i x).trans (Prefix.count_flatMap_ge l Finset.univ.toList (by simp) x)

/-- Every dyadic partition admits an actual iterated-bisection grid refinement. -/
lemma exists_grid_refinement (P : Partition X) :
    ∃ l : List X,∀ j : (grid l).index,∃! i : P.index,(P.brick i).Extends ((grid l).brick j) := by
  let := P.finite
  obtain ⟨l,hl⟩ := exists_grid_bound P.brick
  refine ⟨l,?_⟩
  intro j
  let z := ((grid l).brick j).attach (fun _ _ => false)
  obtain ⟨i,hi,hu⟩ := P.cover z
  refine ⟨i,hl i j ⟨z,hi,⟨_,rfl⟩⟩,?_⟩
  intro k hk
  exact hu k (Prefix.mem_range_of_extends hk ⟨_,rfl⟩)

end Partition
end

section
universe u v
attribute [local instance] Classical.propDecidable

/-- A finite coloured binary splitting forest with one root. -/
inductive Tree (X : Type v) : Type v
  | leaf : Tree X
  | split : X → Tree X → Tree X → Tree X

namespace Prefix
variable {X : Type v}
@[simp] lemma empty_comp (p : Prefix X) : empty.comp p=p := by ext x; simp [empty]
@[simp] lemma comp_empty (p : Prefix X) : p.comp empty=p := by ext x; simp [empty]
lemma comp_assoc (p q r : Prefix X) : (p.comp q).comp r=p.comp (q.comp r) := by
  ext x; simp [List.append_assoc]
end Prefix
namespace Tree
variable {X : Type v}

/-- Leaf indices stay in the small universe, even for large colour sets. -/
abbrev Leaves : Tree X → Type
  | .leaf => PUnit
  | .split _ a b => Leaves a ⊕ Leaves b

instance leaves_fintype (t : Tree X) : Fintype t.Leaves := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype PUnit)
  | split x a b ha hb =>
    letI : Fintype a.Leaves := ha
    letI : Fintype b.Leaves := hb
    exact inferInstanceAs (Fintype (a.Leaves ⊕ b.Leaves))

def brick : (t : Tree X) → t.Leaves → Prefix X
  | .leaf,_ => Prefix.empty
  | .split x a _,Sum.inl i => (Prefix.oneBit x false).comp (brick a i)
  | .split x _ b,Sum.inr j => (Prefix.oneBit x true).comp (brick b j)

lemma cover (t : Tree X) : ∀ z : Cube X,∃! i : t.Leaves, ∃ w,(t.brick i).attach w=z := by
  induction t with
  | leaf => exact Partition.trivial.cover
  | split x a b ha hb =>
    intro z
    obtain ⟨c,⟨w,hw⟩,hc⟩ := (Partition.bit x).cover z
    cases c with
    | false =>
      obtain ⟨i,⟨v,hv⟩,hi⟩ := ha w
      refine ⟨Sum.inl i,⟨v,?_⟩,?_⟩
      · change ((Prefix.oneBit x false).comp (a.brick i)).attach v=z
        rw [Prefix.comp_attach,hv,hw]
      · intro j hj
        cases j with
        | inl j =>
          obtain ⟨r,hr⟩ := hj
          rw [brick,Prefix.comp_attach] at hr
          exact congrArg Sum.inl (hi j ⟨r,(Prefix.oneBit x false).attach_injective (hr.trans hw.symm)⟩)
        | inr j =>
          obtain ⟨r,hr⟩ := hj
          have he : true=false := hc true ⟨(b.brick j).attach r,(Prefix.comp_attach _ _ _).symm.trans hr⟩
          cases he
    | true =>
      obtain ⟨i,⟨v,hv⟩,hi⟩ := hb w
      refine ⟨Sum.inr i,⟨v,?_⟩,?_⟩
      · change ((Prefix.oneBit x true).comp (b.brick i)).attach v=z
        rw [Prefix.comp_attach,hv,hw]
      · intro j hj
        cases j with
        | inl j =>
          obtain ⟨r,hr⟩ := hj
          have he : false=true := hc false ⟨(a.brick j).attach r,(Prefix.comp_attach _ _ _).symm.trans hr⟩
          cases he
        | inr j =>
          obtain ⟨r,hr⟩ := hj
          rw [brick,Prefix.comp_attach] at hr
          exact congrArg Sum.inr (hi j ⟨r,(Prefix.oneBit x true).attach_injective (hr.trans hw.symm)⟩)

abbrev partition (t : Tree X) : Partition X where
  index := t.Leaves
  finite := leaves_fintype t
  brick := t.brick
  cover := t.cover

def grid : List X → Tree X
  | [] => .leaf
  | x::l => .split x (grid l) (grid l)

@[simp] lemma grid_length (l : List X) (i : (grid l).Leaves) (x : X) :
    (((grid l).brick i).word x).length=l.count x := by
  classical
  induction l with
  | nil => simp [grid,brick,Prefix.empty]
  | cons y l ih =>
    cases i with
    | inl i =>
      change ((Prefix.oneBit y false).word x ++ ((grid l).brick i).word x).length=_
      rw [List.length_append,ih]
      by_cases hxy : x=y
      · subst y; simp [Nat.add_comm]
      · simp [hxy,Ne.symm hxy]
    | inr i =>
      change ((Prefix.oneBit y true).word x ++ ((grid l).brick i).word x).length=_
      rw [List.length_append,ih]
      by_cases hxy : x=y
      · subst y; simp [Nat.add_comm]
      · simp [hxy,Ne.symm hxy]

def graft : (t : Tree X) → (t.Leaves → Tree X) → Tree X
  | .leaf,f => f PUnit.unit
  | .split x a b,f => .split x (graft a (fun i => f (Sum.inl i))) (graft b (fun i => f (Sum.inr i)))

def graftLeaves : (t : Tree X) → (f : t.Leaves → Tree X) →
    (t.graft f).Leaves ≃ (i : t.Leaves) × (f i).Leaves
  | .leaf,f => {
      toFun := fun j => ⟨PUnit.unit,j⟩
      invFun := fun ⟨PUnit.unit,j⟩ => j
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨i,j⟩; cases i; rfl }
  | .split x a b,f => {
      toFun := fun j => match j with
        | Sum.inl j => ⟨Sum.inl (((graftLeaves a (fun i => f (Sum.inl i))).toFun j).1),((graftLeaves a (fun i => f (Sum.inl i))).toFun j).2⟩
        | Sum.inr j => ⟨Sum.inr (((graftLeaves b (fun i => f (Sum.inr i))).toFun j).1),((graftLeaves b (fun i => f (Sum.inr i))).toFun j).2⟩
      invFun := fun ⟨i,j⟩ => match i with
        | Sum.inl i => Sum.inl ((graftLeaves a (fun i => f (Sum.inl i))).invFun ⟨i,j⟩)
        | Sum.inr i => Sum.inr ((graftLeaves b (fun i => f (Sum.inr i))).invFun ⟨i,j⟩)
      left_inv := by
        rintro (j|j)
        · exact congrArg Sum.inl ((graftLeaves a (fun i => f (Sum.inl i))).left_inv j)
        · exact congrArg Sum.inr ((graftLeaves b (fun i => f (Sum.inr i))).left_inv j)
      right_inv := by
        rintro ⟨i,j⟩
        cases i with
        | inl i =>
          exact congrArg (fun z : (i : a.Leaves) × (f (Sum.inl i)).Leaves =>
            (⟨Sum.inl z.1,z.2⟩ : (i : (split x a b).Leaves) × (f i).Leaves))
            ((graftLeaves a (fun i => f (Sum.inl i))).right_inv ⟨i,j⟩)
        | inr i =>
          exact congrArg (fun z : (i : b.Leaves) × (f (Sum.inr i)).Leaves =>
            (⟨Sum.inr z.1,z.2⟩ : (i : (split x a b).Leaves) × (f i).Leaves))
            ((graftLeaves b (fun i => f (Sum.inr i))).right_inv ⟨i,j⟩) }

lemma graft_prefix (t : Tree X) (f : t.Leaves → Tree X) (j : (t.graft f).Leaves) :
    (t.graft f).brick j=(t.brick (t.graftLeaves f j).1).comp ((f (t.graftLeaves f j).1).brick (t.graftLeaves f j).2) := by
  induction t with
  | leaf =>
      change (f PUnit.unit).brick j=Prefix.empty.comp ((f PUnit.unit).brick j)
      exact (Prefix.empty_comp _).symm
  | split x a b ha hb =>
    cases j with
    | inl j =>
      change (Prefix.oneBit x false).comp ((a.graft _).brick j)=_
      rw [ha]
      exact (Prefix.comp_assoc _ _ _).symm
    | inr j =>
      change (Prefix.oneBit x true).comp ((b.graft _).brick j)=_
      rw [hb]
      exact (Prefix.comp_assoc _ _ _).symm

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma eq_of_compatible_of_length_eq {p q : Prefix X} (h : p.Compatible q)
    (hl : ∀ x,(p.word x).length=(q.word x).length) : p=q := by
  apply ext
  intro x
  exact (((extends_of_compatible_of_length_le h (fun x => (hl x).le)) x)).eq_of_length (hl x)

lemma count_repeated_nodup (l : List X) (hl : l.Nodup) (n : X → ℕ) (x : X) :
    (l.flatMap (fun y => List.replicate (n y) y)).count x=if x∈l then n x else 0 := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    rw [List.flatMap_cons,List.count_append,ih hl]
    by_cases hxa : x=a
    · subst x; simp [ha]
    · simp [hxa,Ne.symm hxa,List.count_replicate]

def schedule (p : Prefix X) : List X :=
  p.finite_support.toFinset.toList.flatMap (fun x => List.replicate (p.word x).length x)

@[simp] lemma schedule_count (p : Prefix X) (x : X) :
    p.schedule.count x=(p.word x).length := by
  classical
  rw [schedule,count_repeated_nodup _ (Finset.nodup_toList _)]
  by_cases hx : p.word x=[] <;> simp [hx]

end Prefix
namespace Partition
variable {X : Type v}

lemma brick_injective (P : Partition X) : Function.Injective P.brick := by
  intro i j he
  let z := (P.brick i).attach (fun _ _ => false)
  obtain ⟨k,hk,hu⟩ := P.cover z
  exact (hu i ⟨(fun _ _ => false),rfl⟩).trans
    (hu j ⟨(fun _ _ => false),by rw [← he]⟩).symm

def indexEquivOfBricks (P Q : Partition X)
    (h : ∀ i,∃ j,P.brick i=Q.brick j) : P.index ≃ Q.index :=
  Equiv.ofBijective (fun i => (h i).choose) (by
    constructor
    · intro i j hij
      apply P.brick_injective
      exact (h i).choose_spec.trans ((congrArg Q.brick hij).trans (h j).choose_spec.symm)
    · intro j
      let z := (Q.brick j).attach (fun _ _ => false)
      obtain ⟨i,hi,hu⟩ := P.cover z
      have hk : ∃ w,(Q.brick (h i).choose).attach w=z := by
        rw [← (h i).choose_spec]; exact hi
      obtain ⟨k,hk',hu'⟩ := Q.cover z
      exact ⟨i,(hu' _ hk).trans (hu' j ⟨_,rfl⟩).symm⟩)

lemma indexEquivOfBricks_spec (P Q : Partition X) (h : ∀ i,∃ j,P.brick i=Q.brick j) (i : P.index) :
    P.brick i=Q.brick (P.indexEquivOfBricks Q h i) := (h i).choose_spec

lemma exists_tree_grid_bound {I : Type} [Fintype I] (p : I → Prefix X) :
    ∃ l : List X,∀ i x,((p i).word x).length≤l.count x := by
  classical
  choose l hl using fun i => (p i).exists_length_bound
  refine ⟨Finset.univ.toList.flatMap l,?_⟩
  intro i x
  exact (hl i x).trans (Prefix.count_flatMap_ge l Finset.univ.toList (by simp) x)

lemma grid_bricks_of_lengths (P : Partition X) (l : List X)
    (hl : ∀ i x,((P.brick i).word x).length=l.count x) :
    ∀ i,∃ j,P.brick i=(Tree.grid l).brick j := by
  intro i
  let z := (P.brick i).attach (fun _ _ => false)
  obtain ⟨j,hj,_⟩ := (Tree.grid l).cover z
  refine ⟨j,Prefix.eq_of_compatible_of_length_eq ⟨z,⟨_,rfl⟩,hj⟩ ?_⟩
  intro x
  rw [hl,Tree.grid_length]

end Partition
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f : Equiv.Perm (Cube X)}

def reindex (A : Table (Γ:=Γ) f) {I : Type} [Fintype I] (e : I ≃ A.index) : Table (Γ:=Γ) f where
  index := I
  finite := inferInstance
  source i := A.source (e i)
  target i := A.target (e i)
  label i := A.label (e i)
  source_cover := by
    intro z
    obtain ⟨i,hi,hu⟩ := A.source_cover z
    refine ⟨e.symm i,by simpa using hi,?_⟩
    intro j hj
    apply e.injective
    simpa using hu (e j) hj
  target_cover := by
    intro z
    obtain ⟨i,hi,hu⟩ := A.target_cover z
    refine ⟨e.symm i,by simpa using hi,?_⟩
    intro j hj
    apply e.injective
    simpa using hu (e j) hj
  chart i z := A.chart (e i) z

abbrev FamilyIndex (A : Table (Γ:=Γ) f) (P : A.index → Partition X) := (i : A.index) × (P i).index

instance familyIndex_fintype (A : Table (Γ:=Γ) f) (P : A.index → Partition X) :
    Fintype (FamilyIndex A P) := by
  letI := A.finite
  letI (i : A.index) := (P i).finite
  exact inferInstanceAs (Fintype ((i : A.index) × (P i).index))

lemma family_source_cover (A : Table (Γ:=Γ) f) (P : A.index → Partition X) :
    ∀ z : Cube X,∃! ij : FamilyIndex A P,
      ∃ w,((A.source ij.1).comp ((P ij.1).brick ij.2)).attach w=z := by
  intro z
  obtain ⟨i,⟨w,hw⟩,hi⟩ := A.source_cover z
  obtain ⟨j,⟨r,hr⟩,hj⟩ := (P i).cover w
  refine ⟨⟨i,j⟩,⟨r,?_⟩,?_⟩
  · rw [Prefix.comp_attach,hr,hw]
  · rintro ⟨k,l⟩ ⟨a,ha⟩
    rw [Prefix.comp_attach] at ha
    have hki : k=i := hi k ⟨(P k).brick l |>.attach a,ha⟩
    subst k
    have hlj := hj l ⟨a,(A.source i).attach_injective (ha.trans hw.symm)⟩
    subst l
    rfl

/-- Refining each chart by an independently chosen finite partition preserves
its actual cube permutation and transports the tail with the original label. -/
def refineFamily (A : Table (Γ:=Γ) f) (P : A.index → Partition X) : Table (Γ:=Γ) f where
  index := FamilyIndex A P
  finite := familyIndex_fintype A P
  source ij := (A.source ij.1).comp ((P ij.1).brick ij.2)
  target ij := (A.target ij.1).comp (twistPrefix (A.label ij.1) ((P ij.1).brick ij.2))
  label ij := A.label ij.1
  source_cover := family_source_cover A P
  target_cover := transport_partition _ _ _ _ (family_source_cover A P) (by
    intro ij z
    exact A.refined_chart ij.1 ((P ij.1).brick ij.2) z)
  chart ij z := A.refined_chart ij.1 ((P ij.1).brick ij.2) z

lemma exists_source_tree (A : Table (Γ:=Γ) f) :
    ∃ (t : Tree X) (B : Table (Γ:=Γ) f) (e : B.index ≃ t.Leaves),
      ∀ i,B.source i=t.brick (e i) := by
  classical
  let := A.finite
  obtain ⟨l,hl⟩ := Partition.exists_tree_grid_bound A.source
  let P (i : A.index) := (Tree.grid (l.diff (A.source i).schedule)).partition
  let B := A.refineFamily P
  have hb (ij : B.index) (x : X) : ((B.source ij).word x).length=l.count x := by
    change ((A.source ij.1).word x ++ ((Tree.grid (l.diff (A.source ij.1).schedule)).brick ij.2).word x).length=_
    rw [List.length_append,Tree.grid_length,List.count_diff,Prefix.schedule_count]
    exact Nat.add_sub_of_le (hl ij.1 x)
  have he := B.sourcePartition.grid_bricks_of_lengths l hb
  exact ⟨Tree.grid l,B,B.sourcePartition.indexEquivOfBricks (Tree.grid l).partition he,
    fun i => (he i).choose_spec⟩

end Table
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f : Equiv.Perm (Cube X)}

/-- Every actual finite labelled table admits a coloured tree-pair model.
This is the normal form needed for a forest presentation; it does not by itself
prove finite presentation. -/
lemma exists_tree_pair (A : Table (Γ:=Γ) f) :
    ∃ (s t : Tree X) (B : Table (Γ:=Γ) f)
      (es : B.index ≃ s.Leaves) (et : B.index ≃ t.Leaves),
      (∀ i,B.source i=s.brick (es i)) ∧ (∀ i,B.target i=t.brick (et i)) := by
  classical
  obtain ⟨s,B,e,he⟩ := A.exists_source_tree
  let C := B.reindex e.symm
  have hc (i : s.Leaves) : C.source i=s.brick i := by
    exact (he (e.symm i)).trans (by simp)
  let := C.finite
  obtain ⟨l,hl⟩ := Partition.exists_tree_grid_bound C.target
  let Q (i : s.Leaves) : Tree X :=
    Tree.grid ((l.diff (C.target i).schedule).map (fun x => (C.label i)⁻¹ • x))
  let D := C.refineFamily (fun i => (Q i).partition)
  have hd (ij : D.index) (x : X) : ((D.target ij).word x).length=l.count x := by
    change ((C.target ij.1).word x ++
      ((Q ij.1).brick ij.2).word ((C.label ij.1)⁻¹ • x)).length=_
    rw [List.length_append,Tree.grid_length]
    rw [List.count_map_of_injective _ _ (MulAction.injective _),List.count_diff,Prefix.schedule_count]
    exact Nat.add_sub_of_le (hl ij.1 x)
  have ht := D.targetPartition.grid_bricks_of_lengths l hd
  refine ⟨s.graft Q,Tree.grid l,D,(s.graftLeaves Q).symm,
    D.targetPartition.indexEquivOfBricks (Tree.grid l).partition ht,?_,fun i => (ht i).choose_spec⟩
  intro ij
  change (C.source ij.1).comp ((Q ij.1).brick ij.2)=
    (s.graft Q).brick ((s.graftLeaves Q).symm ⟨ij.1,ij.2⟩)
  rw [Tree.graft_prefix,Equiv.apply_symm_apply]
  exact congrArg (fun p => p.comp ((Q ij.1).brick ij.2)) (hc ij.1)

end Table
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
