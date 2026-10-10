import OAI.GroupTheory.BooneHigman.CantorBricks

namespace OAI

noncomputable section

/-!
Partition refinement, simplicity, faithful group embedding, and countability.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Partition
variable {X : Type v}

/-- The chart coordinates of a finite dyadic partition. -/
def coordinateEquiv (P : Partition X) : P.index × Cube X ≃ Cube X :=
  Equiv.ofBijective (fun a => (P.brick a.1).attach a.2) (by
    constructor
    · rintro ⟨i,z⟩ ⟨j,w⟩ he
      obtain ⟨k,hk,huniq⟩ := P.cover ((P.brick i).attach z)
      have hij : i=j := (huniq i ⟨z,rfl⟩).trans (huniq j ⟨w,he.symm⟩).symm
      subst j
      exact Prod.ext rfl ((P.brick i).attach_injective he)
    · intro z
      obtain ⟨i,⟨w,hw⟩,_⟩ := P.cover z
      exact ⟨(i,w),hw⟩)

@[simp] lemma coordinateEquiv_apply (P : Partition X) (i : P.index) (z : Cube X) :
    P.coordinateEquiv (i,z)=(P.brick i).attach z := rfl

@[simp] lemma coordinateEquiv_symm_attach (P : Partition X) (i : P.index) (z : Cube X) :
    P.coordinateEquiv.symm ((P.brick i).attach z)=(i,z) :=
  P.coordinateEquiv.symm_apply_apply (i,z)

/-- Untwisted chart bijection between any two equally sized dyadic partitions. -/
def mapPerm (P Q : Partition X) (e : P.index ≃ Q.index) : Equiv.Perm (Cube X) :=
  (P.coordinateEquiv.symm.trans (Equiv.prodCongr e (Equiv.refl (Cube X)))).trans Q.coordinateEquiv

@[simp] lemma mapPerm_attach (P Q : Partition X) (e : P.index ≃ Q.index)
    (i : P.index) (z : Cube X) :
    P.mapPerm Q e ((P.brick i).attach z)=(Q.brick (e i)).attach z := by
  simp [mapPerm]

variable {Γ : Type u} [Group Γ] [MulAction Γ X]

def mapTable (P Q : Partition X) (e : P.index ≃ Q.index) :
    Table (Γ:=Γ) (P.mapPerm Q e) where
  index := P.index
  finite := P.finite
  source := P.brick
  target i := Q.brick (e i)
  label _ := 1
  source_cover := P.cover
  target_cover := by
    intro z
    obtain ⟨i,hi,huniq⟩ := Q.cover z
    refine ⟨e.symm i,?_,?_⟩
    · simpa using hi
    · intro j hj
      apply e.injective
      simpa using huniq (e j) hj
  chart := by intro i z; simp

def changeChart (P Q : Partition X) (e : P.index ≃ Q.index) : group (Γ:=Γ) (X:=X) :=
  ⟨P.mapPerm Q e,(mem_group_iff_table _).mpr ⟨P.mapTable Q e⟩⟩

@[simp] lemma changeChart_apply (P Q : Partition X) (e : P.index ≃ Q.index)
    (i : P.index) (z : Cube X) :
    (P.changeChart (Γ:=Γ) Q e).val ((P.brick i).attach z)=(Q.brick (e i)).attach z :=
  P.mapPerm_attach Q e i z

end Partition

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Separate coordinate twists on the components of a disjoint union of cubes. -/
def componentTwist {I : Type} : (I → Γ) →* Equiv.Perm (I × Cube X) where
  toFun a := {
    toFun := fun iz => (iz.1,twist (a iz.1) iz.2)
    invFun := fun iz => (iz.1,twist (a iz.1)⁻¹ iz.2)
    left_inv := by intro ⟨i,z⟩; simp
    right_inv := by intro ⟨i,z⟩; simp }
  map_one' := by
    apply Equiv.ext
    intro ⟨i,z⟩
    change (i,twist (1 : Γ) z)=(i,z)
    simp
  map_mul' a b := by
    apply Equiv.ext
    intro ⟨i,z⟩
    exact Prod.ext rfl (twist_twist _ _ _).symm

def decoratePerm (P : Partition X) : (P.index → Γ) →* Equiv.Perm (Cube X) :=
  P.coordinateEquiv.permCongrHom.toMonoidHom.comp componentTwist

@[simp] lemma decoratePerm_attach (P : Partition X) (a : P.index → Γ) (i : P.index)
    (z : Cube X) :
    decoratePerm P a ((P.brick i).attach z)=(P.brick i).attach (twist (a i) z) := by
  change P.coordinateEquiv.permCongr (componentTwist a) ((P.brick i).attach z)=_
  simp [Equiv.permCongr,Equiv.equivCongr,componentTwist]

def decorateTable (P : Partition X) (a : P.index → Γ) : Table (Γ:=Γ) (decoratePerm P a) where
  index := P.index
  finite := P.finite
  source := P.brick
  target := P.brick
  label := a
  source_cover := P.cover
  target_cover := P.cover
  chart := decoratePerm_attach P a

/-- A direct product of local coordinate copies of the acting group. -/
def decorate (P : Partition X) : (P.index → Γ) →* group (Γ:=Γ) (X:=X) :=
  (decoratePerm P).codRestrict _ (fun a => (mem_group_iff_table _).mpr ⟨decorateTable P a⟩)

@[simp] lemma decorate_val (P : Partition X) (a : P.index → Γ) :
    (decorate P a).val=decoratePerm P a := rfl

lemma decorate_injective [FaithfulSMul Γ X] (P : Partition X) :
    Function.Injective (decorate (Γ:=Γ) P) := by
  intro a b he
  funext i
  apply twist_injective (X:=X)
  apply Equiv.ext
  intro z
  change twist (a i) z=twist (b i) z
  apply (P.brick i).attach_injective
  simpa only [decorate_val,decoratePerm_attach] using
    Equiv.congr_fun (congrArg Subtype.val he) ((P.brick i).attach z)

namespace Table
variable {f : Equiv.Perm (Cube X)}

/-- Every table is an untwisted prefix rearrangement followed by finitely many
independent local coordinate twists. -/
lemma decomposition (A : Table (Γ:=Γ) f) :
    f = A.sourcePartition.mapPerm A.targetPartition (Equiv.refl A.index) *
      decoratePerm A.sourcePartition A.label := by
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := A.source_cover z
  rw [Equiv.Perm.mul_apply]
  change f ((A.sourcePartition.brick i).attach w)=
    A.sourcePartition.mapPerm A.targetPartition (Equiv.refl A.index)
      (decoratePerm A.sourcePartition A.label ((A.sourcePartition.brick i).attach w))
  rw [decoratePerm_attach,Partition.mapPerm_attach]
  exact A.chart i w

end Table

end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma eq_of_range_eq {p q : Prefix X} (h : Set.range p.attach=Set.range q.attach) : p=q := by
  have hpq : p.Extends q := extends_of_ranges (by
    intro z hz
    change z∈Set.range p.attach
    rw [h]
    exact hz)
  have hqp : q.Extends p := extends_of_ranges (by
    intro z hz
    change z∈Set.range q.attach
    rw [← h]
    exact hz)
  apply Prefix.ext
  intro x
  exact List.Sublist.antisymm (hpq x).sublist (hqp x).sublist

end Prefix

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma chart_prefix_rigidity {p q : Prefix X} {a b : Γ}
    (h : ∀ z : Cube X,p.attach (twist a z)=q.attach (twist b z)) : p=q := by
  apply Prefix.eq_of_range_eq
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨twist b (twist a⁻¹ w),?_⟩
    rw [← h,twist_twist_inv]
  · rintro ⟨w,rfl⟩
    refine ⟨twist a (twist b⁻¹ w),?_⟩
    rw [h,twist_twist_inv]

lemma chart_rigidity [FaithfulSMul Γ X] {p q : Prefix X} {a b : Γ}
    (h : ∀ z : Cube X,p.attach (twist a z)=q.attach (twist b z)) : p=q ∧ a=b := by
  have hp := chart_prefix_rigidity h
  refine ⟨hp,?_⟩
  subst q
  apply twist_injective (X:=X)
  apply Equiv.ext
  intro z
  exact p.attach_injective (h z)

namespace Table
variable {f : Equiv.Perm (Cube X)}

/-- A literal chart refinement: attach a finite prefix to each tail, then
transport it with the original coordinate label. -/
structure Refines (A B : Table (Γ:=Γ) f) where
  parent : B.index → A.index
  tail : B.index → Prefix X
  source_eq : ∀ j,B.source j=(A.source (parent j)).comp (tail j)
  target_eq : ∀ j,B.target j=(A.target (parent j)).comp
    (twistPrefix (A.label (parent j)) (tail j))
  label_eq : ∀ j,B.label j=A.label (parent j)

abbrev CommonIndex (A B : Table (Γ:=Γ) f) :=
  {ij : A.index × B.index // (A.source ij.1).Compatible (B.source ij.2)}

instance commonIndex_finite (A B : Table (Γ:=Γ) f) : Fintype (CommonIndex A B) := by
  letI := A.finite
  letI := B.finite
  exact inferInstanceAs (Fintype {ij : A.index × B.index //
    (A.source ij.1).Compatible (B.source ij.2)})

def commonSource (A B : Table (Γ:=Γ) f) (ij : CommonIndex A B) : Prefix X :=
  Prefix.meet ij.property

def commonTargetLeft (A B : Table (Γ:=Γ) f) (ij : CommonIndex A B) : Prefix X :=
  (A.target ij.val.1).comp
    (twistPrefix (A.label ij.val.1) ((A.source ij.val.1).remainder (commonSource A B ij)))

def commonTargetRight (A B : Table (Γ:=Γ) f) (ij : CommonIndex A B) : Prefix X :=
  (B.target ij.val.2).comp
    (twistPrefix (B.label ij.val.2) ((B.source ij.val.2).remainder (commonSource A B ij)))

lemma common_chart_left (A B : Table (Γ:=Γ) f) (ij : CommonIndex A B) (z : Cube X) :
    f ((commonSource A B ij).attach z)=
      (commonTargetLeft A B ij).attach (twist (A.label ij.val.1) z) := by
  have he : (A.source ij.val.1).comp
      ((A.source ij.val.1).remainder (commonSource A B ij))=commonSource A B ij :=
    Prefix.comp_remainder (Prefix.meet_extends_left ij.property)
  calc
    _ = f (((A.source ij.val.1).comp
        ((A.source ij.val.1).remainder (commonSource A B ij))).attach z) :=
      congrArg (fun p : Prefix X => f (p.attach z)) he.symm
    _ = _ := A.refined_chart ij.val.1 _ z

lemma common_chart_right (A B : Table (Γ:=Γ) f) (ij : CommonIndex A B) (z : Cube X) :
    f ((commonSource A B ij).attach z)=
      (commonTargetRight A B ij).attach (twist (B.label ij.val.2) z) := by
  have he : (B.source ij.val.2).comp
      ((B.source ij.val.2).remainder (commonSource A B ij))=commonSource A B ij :=
    Prefix.comp_remainder (Prefix.meet_extends_right ij.property)
  calc
    _ = f (((B.source ij.val.2).comp
        ((B.source ij.val.2).remainder (commonSource A B ij))).attach z) :=
      congrArg (fun p : Prefix X => f (p.attach z)) he.symm
    _ = _ := B.refined_chart ij.val.2 _ z

lemma common_source_cover (A B : Table (Γ:=Γ) f) :
    ∀ z : Cube X,∃! ij : CommonIndex A B, ∃ w,(commonSource A B ij).attach w=z := by
  intro z
  obtain ⟨i,hi,huniq⟩ := A.source_cover z
  obtain ⟨j,hj,huniq'⟩ := B.source_cover z
  let ij : CommonIndex A B := ⟨(i,j),⟨z,hi,hj⟩⟩
  refine ⟨ij,(Prefix.mem_meet_iff ij.property z).mpr ⟨hi,hj⟩,?_⟩
  intro kl hkl
  obtain ⟨hk,hl⟩ := (Prefix.mem_meet_iff kl.property z).mp hkl
  apply Subtype.ext
  exact Prod.ext (huniq _ hk) (huniq' _ hl)

/-- Source-intersection table, retaining the left-hand transported charts. -/
def common (A B : Table (Γ:=Γ) f) : Table (Γ:=Γ) f where
  index := CommonIndex A B
  finite := commonIndex_finite A B
  source := commonSource A B
  target := commonTargetLeft A B
  label ij := A.label ij.val.1
  source_cover := common_source_cover A B
  target_cover := transport_partition f _ _ _ (common_source_cover A B) (common_chart_left A B)
  chart := common_chart_left A B

def common_refines_left (A B : Table (Γ:=Γ) f) : Refines A (common A B) where
  parent ij := ij.val.1
  tail ij := (A.source ij.val.1).remainder (commonSource A B ij)
  source_eq ij := (Prefix.comp_remainder (Prefix.meet_extends_left ij.property)).symm
  target_eq _ := rfl
  label_eq _ := rfl

lemma common_chart_rigidity [FaithfulSMul Γ X] (A B : Table (Γ:=Γ) f)
    (ij : CommonIndex A B) :
    commonTargetLeft A B ij=commonTargetRight A B ij ∧ A.label ij.val.1=B.label ij.val.2 := by
  apply chart_rigidity
  intro z
  exact (common_chart_left A B ij z).symm.trans (common_chart_right A B ij z)

def common_refines_right [FaithfulSMul Γ X] (A B : Table (Γ:=Γ) f) : Refines B (common A B) where
  parent ij := ij.val.2
  tail ij := (B.source ij.val.2).remainder (commonSource A B ij)
  source_eq ij := (Prefix.comp_remainder (Prefix.meet_extends_right ij.property)).symm
  target_eq ij := (common_chart_rigidity A B ij).1
  label_eq ij := (common_chart_rigidity A B ij).2

/-- Completeness of the finite table equivalence: two tables for the same
permutation have an actual simultaneous chart refinement, including labels. -/
theorem common_refinement [FaithfulSMul Γ X] (A B : Table (Γ:=Γ) f) :
    ∃ C : Table (Γ:=Γ) f, Nonempty (Refines A C) ∧ Nonempty (Refines B C) :=
  ⟨common A B,⟨common_refines_left A B⟩,⟨common_refines_right A B⟩⟩

end Table

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma localizePerm_conj {p q : Prefix X} (h : Equiv.Perm (Cube X))
    (hh : ∀ z,h (p.attach z)=q.attach z) (f : Equiv.Perm (Cube X)) :
    h * localizePerm p f * h⁻¹=localizePerm q f := by
  apply Equiv.ext
  intro z
  change h (localizePerm p f (h.symm z))=localizePerm q f z
  by_cases hz : z∈Set.range q.attach
  · obtain ⟨w,rfl⟩ := hz
    have hi : h.symm (q.attach w)=p.attach w := by rw [← hh,h.symm_apply_apply]
    rw [hi,localizePerm_attach,hh,localizePerm_attach]
  · have hp : h.symm z∉Set.range p.attach := by
      rintro ⟨w,hw⟩
      apply hz
      refine ⟨w,?_⟩
      rw [← hh,hw,h.apply_symm_apply]
    rw [localizePerm_outside _ _ hp,localizePerm_outside _ _ hz,h.apply_symm_apply]

lemma localize_conj {p q : Prefix X} (h : group (Γ:=Γ) (X:=X))
    (hh : ∀ z,h.val (p.attach z)=q.attach z) (f : group (Γ:=Γ) (X:=X)) :
    h * localize p f * h⁻¹=localize q f :=
  Subtype.ext (localizePerm_conj h.val hh f.val)

namespace Partition

lemma exists_other (P : Partition X) (i : P.index) (hi : P.brick i≠Prefix.empty) :
    ∃ j : P.index,j≠i := by
  by_contra hn
  apply hi
  apply Prefix.eq_of_range_eq
  ext z
  constructor
  · intro _; exact ⟨z,Prefix.empty_attach z⟩
  · intro _
    obtain ⟨j,hj,_⟩ := P.cover z
    have hji : j=i := by by_contra hh; exact hn ⟨j,hh⟩
    simpa [hji] using hj

/-- Shift a split from an exterior brick to the selected one. -/
def splitShift (P : Partition X) (i j : P.index) :
    ({k : P.index // k≠j} ⊕ Bool) ≃ ({k : P.index // k≠i} ⊕ Bool) :=
  Equiv.sumCongr (Equiv.subtypeEquiv (Equiv.swap i j) (by
    intro k
    constructor
    · intro hk he
      apply hk
      have h := congrArg (Equiv.swap i j) he
      simpa using h
    · intro hk he
      subst k
      simp at hk)) (Equiv.refl Bool)

def compressIndex (P : Partition X) (i j : P.index) (hji : j≠i) (b : Bool) :
    ({k : P.index // k≠j} ⊕ Bool) ≃ ({k : P.index // k≠i} ⊕ Bool) :=
  (splitShift P i j).trans
    (Equiv.swap (Sum.inl (⟨j,hji⟩ : {k : P.index // k≠i})) (Sum.inr b))

lemma compressIndex_apply (P : Partition X) (i j : P.index) (hji : j≠i) (b : Bool) :
    compressIndex P i j hji b (Sum.inl ⟨i,Ne.symm hji⟩)=Sum.inr b := by
  unfold compressIndex splitShift
  simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl]
  change Equiv.swap (Sum.inl (⟨j,hji⟩ : {k : P.index // k≠i})) (Sum.inr b)
    (Sum.inl ⟨Equiv.swap i j i,_⟩)=Sum.inr b
  have he : (⟨Equiv.swap i j i,by simpa using hji⟩ : {k : P.index // k≠i})=⟨j,hji⟩ := by
    apply Subtype.ext
    simp
  rw [he,Equiv.swap_apply_left]

end Partition

/-- Every proper brick can be compressed into either dyadic half by an element
of the actual finite-table group. -/
theorem exists_compressor (p : Prefix X) (hp : p≠Prefix.empty) (x : X) (b : Bool) :
    ∃ h : group (Γ:=Γ) (X:=X), ∀ z,
      h.val (p.attach z)=(p.comp (Prefix.oneBit x b)).attach z := by
  obtain ⟨P,i,hi⟩ := p.hasPartition
  obtain ⟨j,hji⟩ := P.exists_other i (by rwa [hi])
  let Q := P.refinement (Partition.bit x) j
  let R := P.refinement (Partition.bit x) i
  let e := P.compressIndex i j hji b
  refine ⟨Q.changeChart R e,fun z => ?_⟩
  have he := Q.changeChart_apply (Γ:=Γ) R e (Sum.inl ⟨i,Ne.symm hji⟩) z
  change (Q.changeChart R e).val ((P.brick i).attach z)=
    (R.brick (e (Sum.inl ⟨i,Ne.symm hji⟩))).attach z at he
  rw [Partition.compressIndex_apply] at he
  change (Q.changeChart R e).val ((P.brick i).attach z)=
    ((P.brick i).comp (Prefix.oneBit x b)).attach z at he
  simpa [hi] using he

/-- Uniform conjugacy of a proper local copy with either half-copy. -/
theorem exists_localize_half_conjugacy (p : Prefix X) (hp : p≠Prefix.empty)
    (x : X) (b : Bool) : ∃ h : group (Γ:=Γ) (X:=X), ∀ f,
      h * localize p f * h⁻¹=localize (p.comp (Prefix.oneBit x b)) f := by
  obtain ⟨h,hh⟩ := exists_compressor (Γ:=Γ) p hp x b
  exact ⟨h,fun f => localize_conj h hh f⟩

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma Prefix.comp_oneBit_comm {p : Prefix X} {x : X} (hx : p.word x=[]) (b : Bool) :
    p.comp (Prefix.oneBit x b)=(Prefix.oneBit x b).comp p := by
  apply Prefix.ext
  intro y
  by_cases hy : y=x
  · subst y; simp [hx]
  · simp [hy]

lemma Prefix.oneBit_ne_empty (x : X) (b : Bool) : Prefix.oneBit x b≠Prefix.empty := by
  intro he
  have hh := congrArg (fun p : Prefix X => p.word x) he
  simp [Prefix.empty] at hh

lemma localizePerm_comp (p q : Prefix X) (f : Equiv.Perm (Cube X)) :
    localizePerm (p.comp q) f=localizePerm p (localizePerm q f) := by
  apply Equiv.ext
  intro z
  by_cases hz : z∈Set.range p.attach
  · obtain ⟨w,rfl⟩ := hz
    rw [localizePerm_attach]
    by_cases hw : w∈Set.range q.attach
    · obtain ⟨a,rfl⟩ := hw
      rw [← Prefix.comp_attach,localizePerm_attach,localizePerm_attach,Prefix.comp_attach]
    · have hn : p.attach w∉Set.range (p.comp q).attach := by
        rintro ⟨a,ha⟩
        apply hw
        exact ⟨a,p.attach_injective ((Prefix.comp_attach _ _ _).symm.trans ha)⟩
      rw [localizePerm_outside _ _ hn,localizePerm_outside _ _ hw]
  · have hn : z∉Set.range (p.comp q).attach := by
      rintro ⟨a,rfl⟩
      exact hz ⟨q.attach a,Prefix.comp_attach _ _ _ |>.symm⟩
    rw [localizePerm_outside _ _ hn,localizePerm_outside _ _ hz]

lemma localize_comp (p q : Prefix X) (f : group (Γ:=Γ) (X:=X)) :
    localize (p.comp q) f=localize p (localize q f) :=
  Subtype.ext (localizePerm_comp p q f.val)

/-- Two equal local copies in the coordinate halves. -/
def diagonal (x : X) (f : group (Γ:=Γ) (X:=X)) : group (Γ:=Γ) (X:=X) :=
  localize (Prefix.oneBit x false) f * localize (Prefix.oneBit x true) f

lemma diagonal_attach (x : X) (f : group (Γ:=Γ) (X:=X)) (b : Bool) (z : Cube X) :
    (diagonal x f).val ((Prefix.oneBit x b).attach z)=
      (Prefix.oneBit x b).attach (f.val z) := by
  have hout (a c : Bool) (hac : a≠c) (w : Cube X) :
      (Prefix.oneBit x a).attach w∉Set.range (Prefix.oneBit x c).attach := by
    intro hh
    have hc := (Prefix.mem_oneBit x c _).mp hh
    have ha := (Prefix.mem_oneBit x a _).mp ⟨w,rfl⟩
    exact hac (ha.symm.trans hc)
  change localizePerm (Prefix.oneBit x false) f.val
    (localizePerm (Prefix.oneBit x true) f.val ((Prefix.oneBit x b).attach z))=_
  cases b
  · rw [localizePerm_outside _ _ (hout false true Bool.false_ne_true z),localizePerm_attach]
  · rw [localizePerm_attach,
      localizePerm_outside _ _ (hout true false (Ne.symm Bool.false_ne_true) (f.val z))]

namespace Table
variable {f : Equiv.Perm (Cube X)}

/-- A coordinate unused by the finite prefix data exists in the infinite cube. -/
lemma exists_fresh [Infinite X] (A : Table (Γ:=Γ) f) :
    ∃ x : X, ∀ i,(A.source i).word x=[] ∧ (A.target i).word x=[] := by
  let := A.finite
  have hs := Set.finite_iUnion (fun i => (A.source i).finite_support.union (A.target i).finite_support)
  obtain ⟨x,hx⟩ := hs.exists_notMem
  refine ⟨x,fun i => ?_⟩
  have hi : x∉{x | (A.source i).word x≠[]} ∪ {x | (A.target i).word x≠[]} := by
    intro h
    exact hx (Set.mem_iUnion.mpr ⟨i,h⟩)
  simpa using hi

lemma untwisted_commutes_attach (A : Table (Γ:=Γ) f) (hA : ∀ i,A.label i=1)
    (x : X) (hx : ∀ i,(A.source i).word x=[] ∧ (A.target i).word x=[])
    (b : Bool) (z : Cube X) :
    f ((Prefix.oneBit x b).attach z)=(Prefix.oneBit x b).attach (f z) := by
  obtain ⟨i,⟨w,rfl⟩,_⟩ := A.source_cover z
  rw [← Prefix.comp_attach,← Prefix.comp_oneBit_comm (hx i).1,Prefix.comp_attach,A.chart,
    hA i,twist_one]
  change (A.target i).attach ((Prefix.oneBit x b).attach w)=_
  rw [← Prefix.comp_attach,Prefix.comp_oneBit_comm (hx i).2,Prefix.comp_attach,A.chart,
    hA i,twist_one]
  rfl

end Table

/-- A table with no coordinate twisting on any chart. -/
def Untwisted (f : group (Γ:=Γ) (X:=X)) : Prop :=
  ∃ A : Table (Γ:=Γ) f.val, ∀ i,A.label i=1

lemma Untwisted.localize {f : group (Γ:=Γ) (X:=X)} (hf : Untwisted f) (p : Prefix X) :
    Untwisted (localize p f) := by
  obtain ⟨A,hA⟩ := hf
  obtain ⟨P,i,hi⟩ := p.hasPartition
  subst p
  refine ⟨A.localize P i,?_⟩
  intro j
  cases j with
  | inl j => rfl
  | inr j => exact hA j

lemma Untwisted.exists_diagonal [Infinite X] {f : group (Γ:=Γ) (X:=X)}
    (hf : Untwisted f) : ∃ x,f=diagonal x f := by
  obtain ⟨A,hA⟩ := hf
  obtain ⟨x,hx⟩ := A.exists_fresh
  refine ⟨x,Subtype.ext (Equiv.ext (fun z => ?_))⟩
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit x).cover z
  change f.val ((Prefix.oneBit x b).attach w)=
    (diagonal x f).val ((Prefix.oneBit x b).attach w)
  rw [diagonal_attach]
  exact A.untwisted_commutes_attach hA x hx b w

end

section
universe u v
attribute [local instance] Classical.propDecidable
open scoped commutatorElement
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Partition

/-- Simultaneously refine every brick by the same finite partition. -/
abbrev allRefine (P Q : Partition X) : Partition X where
  index := P.index × Q.index
  finite := by letI := P.finite; letI := Q.finite; exact inferInstance
  brick ij := (P.brick ij.1).comp (Q.brick ij.2)
  cover z := by
    obtain ⟨i,⟨w,hw⟩,hi⟩ := P.cover z
    obtain ⟨j,⟨a,ha⟩,hj⟩ := Q.cover w
    refine ⟨(i,j),⟨a,?_⟩,?_⟩
    · rw [Prefix.comp_attach,ha,hw]
    · rintro ⟨k,l⟩ ⟨b,hb⟩
      rw [Prefix.comp_attach] at hb
      have hki : k=i := hi k ⟨(Q.brick l).attach b,hb⟩
      subst k
      have hl : l=j := hj l ⟨b,(P.brick i).attach_injective (hb.trans hw.symm)⟩
      exact Prod.ext rfl hl

/-- Permute all members of a partition, preserving their cube tails. -/
def permute (P : Partition X) : Equiv.Perm P.index →* group (Γ:=Γ) (X:=X) where
  toFun e := P.changeChart P e
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := P.cover z
    exact P.changeChart_apply P 1 i w
  map_mul' e f := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := P.cover z
    change (P.changeChart (Γ:=Γ) P (e*f)).val ((P.brick i).attach w)=
      (P.changeChart (Γ:=Γ) P e).val ((P.changeChart (Γ:=Γ) P f).val ((P.brick i).attach w))
    simp only [changeChart_apply,Equiv.Perm.mul_apply]

@[simp] lemma permute_attach (P : Partition X) (e : Equiv.Perm P.index)
    (i : P.index) (z : Cube X) :
    (P.permute (Γ:=Γ) e).val ((P.brick i).attach z)=(P.brick (e i)).attach z :=
  P.changeChart_apply P e i z

lemma permute_allRefine (P Q : Partition X) (e : Equiv.Perm P.index) :
    (P.allRefine Q).permute (Γ:=Γ) (Equiv.prodCongr e (Equiv.refl Q.index))=P.permute e := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨⟨i,j⟩,⟨w,rfl⟩,_⟩ := (P.allRefine Q).cover z
  rw [permute_attach]
  change (((P.brick (e i)).comp (Q.brick j)).attach w)=
    (P.permute e).val (((P.brick i).comp (Q.brick j)).attach w)
  simp only [Prefix.comp_attach,permute_attach]

end Partition

lemma doubled_swap_commutator {I : Type} (i j : I) :
    ⁅(Equiv.prodCongr (Equiv.refl I) Equiv.boolNot : Equiv.Perm (I × Bool)),
      Equiv.swap (i,false) (j,false)⁆ =
      Equiv.prodCongr (Equiv.swap i j) (Equiv.refl Bool) := by
  classical
  apply Equiv.ext
  rintro ⟨k,b⟩
  cases b <;> by_cases hki : k=i <;> by_cases hkj : k=j <;>
    simp_all [commutatorElement_def,Equiv.Perm.mul_apply,Equiv.swap_apply_def,
      Equiv.prodCongr,Equiv.boolNot,Function.Involutive.toPerm]

/-- Bisection turns every finite brick transposition into a double transposition,
which is an actual commutator in the finite-table group. -/
lemma Partition.swap_mem_commutatorSet (P : Partition X) (x : X) (i j : P.index) :
    P.permute (Γ:=Γ) (Equiv.swap i j)∈commutatorSet (group (Γ:=Γ) (X:=X)) := by
  let Q := P.allRefine (Partition.bit x)
  have he := congrArg (Q.permute (Γ:=Γ)) (doubled_swap_commutator i j)
  rw [map_commutatorElement] at he
  have hr : Q.permute (Γ:=Γ) (Equiv.prodCongr (Equiv.swap i j) (Equiv.refl Bool))=
    P.permute (Equiv.swap i j) := P.permute_allRefine (Partition.bit x) (Equiv.swap i j)
  rw [hr] at he
  exact ⟨_,_,he⟩

/-- Every permutation of a finite dyadic partition has trivial abelianization. -/
theorem Partition.permute_mem_commutator (P : Partition X) (x : X)
    (e : Equiv.Perm P.index) : P.permute (Γ:=Γ) e∈commutator (group (Γ:=Γ) (X:=X)) := by
  let := P.finite
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j _ ih =>
      rw [map_mul]
      apply Subgroup.mul_mem _ _ ih
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (P.swap_mem_commutatorSet (Γ:=Γ) x i j)

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f : group (Γ:=Γ) (X:=X)}

abbrev CorrectionIndex (A : Table (Γ:=Γ) f.val) := Bool × A.index

instance correctionIndex_finite (A : Table (Γ:=Γ) f.val) : Fintype (CorrectionIndex A) := by
  letI := A.finite
  exact inferInstanceAs (Fintype (Bool × A.index))

def correctionSource (A : Table (Γ:=Γ) f.val) (x : X) (bi : CorrectionIndex A) : Prefix X :=
  (Prefix.oneBit x bi.1).comp (A.target bi.2)

def correctionTarget (A : Table (Γ:=Γ) f.val) (x : X) (bi : CorrectionIndex A) : Prefix X :=
  (A.target bi.2).comp (twistPrefix (A.label bi.2) (Prefix.oneBit x bi.1))

lemma correction_chart (A : Table (Γ:=Γ) f.val) (x : X)
    (hx : ∀ i,(A.source i).word x=[]) (bi : CorrectionIndex A) (z : Cube X) :
    (f * (diagonal x f)⁻¹).val ((correctionSource A x bi).attach z)=
      (correctionTarget A x bi).attach (twist (1 : Γ) z) := by
  obtain ⟨b,i⟩ := bi
  have hd : (diagonal x f).val
      (((Prefix.oneBit x b).comp (A.source i)).attach (twist (A.label i)⁻¹ z))=
      ((Prefix.oneBit x b).comp (A.target i)).attach z := by
    rw [Prefix.comp_attach,diagonal_attach,A.chart,twist_twist_inv,Prefix.comp_attach]
  have hi : (diagonal x f).val.symm
      (((Prefix.oneBit x b).comp (A.target i)).attach z)=
      ((Prefix.oneBit x b).comp (A.source i)).attach (twist (A.label i)⁻¹ z) := by
    apply (diagonal x f).val.injective
    rw [Equiv.apply_symm_apply,hd]
  change f.val ((diagonal x f).val.symm
    (((Prefix.oneBit x b).comp (A.target i)).attach z))=
    ((A.target i).comp (twistPrefix (A.label i) (Prefix.oneBit x b))).attach (twist (1 : Γ) z)
  rw [hi,← Prefix.comp_oneBit_comm (hx i),A.refined_chart,twist_twist_inv,twist_one]
  rfl

/-- All coordinate labels cancel when a table is compared with its double along
a coordinate unused by its source prefixes. -/
def correction (A : Table (Γ:=Γ) f.val) (x : X)
    (hx : ∀ i,(A.source i).word x=[]) : Table (Γ:=Γ) (f * (diagonal x f)⁻¹).val where
  index := CorrectionIndex A
  finite := correctionIndex_finite A
  source := correctionSource A x
  target := correctionTarget A x
  label _ := 1
  source_cover := (Partition.allRefine (Partition.bit x) A.targetPartition).cover
  target_cover := transport_partition _ _ _ _
    (Partition.allRefine (Partition.bit x) A.targetPartition).cover
    (correction_chart A x hx)
  chart := correction_chart A x hx

end Table

/-- Every twisted table differs from two half-copies of itself by an untwisted
finite table. This is a literal table construction, not an abelianized identity. -/
theorem exists_untwisted_correction [Infinite X] (f : group (Γ:=Γ) (X:=X)) :
    ∃ x : X, Untwisted (f * (diagonal x f)⁻¹) := by
  obtain ⟨A⟩ := (mem_group_iff_table _).mp f.property
  obtain ⟨x,hx⟩ := A.exists_fresh
  exact ⟨x,A.correction x (fun i => (hx i).1),fun _ => rfl⟩

end

section
universe u v w
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
variable {H : Type w} [CommGroup H]

lemma map_localize_half (h : group (Γ:=Γ) (X:=X) →* H) (p : Prefix X)
    (hp : p≠Prefix.empty) (x : X) (b : Bool) (f : group (Γ:=Γ) (X:=X)) :
    h (localize (p.comp (Prefix.oneBit x b)) f)=h (localize p f) := by
  obtain ⟨a,ha⟩ := exists_localize_half_conjugacy (Γ:=Γ) p hp x b
  have hh := congrArg h (ha f)
  simpa [map_mul,map_inv,mul_comm,mul_left_comm,mul_assoc] using hh.symm

lemma map_localize_diagonal (h : group (Γ:=Γ) (X:=X) →* H) (p : Prefix X)
    (hp : p≠Prefix.empty) (x : X) (f : group (Γ:=Γ) (X:=X)) :
    h (localize p (diagonal x f))=h (localize p f)*h (localize p f) := by
  rw [diagonal,map_mul,map_mul,← localize_comp,← localize_comp,
    map_localize_half h p hp,map_localize_half h p hp]

lemma eq_one_of_square_eq_self {a : H} (ha : a=a*a) : a=1 := by
  have he := congrArg (fun b => a⁻¹*b) ha
  simpa [mul_assoc] using he.symm

lemma map_localize_untwisted_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    (p : Prefix X) (hp : p≠Prefix.empty) {f : group (Γ:=Γ) (X:=X)} (hf : Untwisted f) :
    h (localize p f)=1 := by
  obtain ⟨x,hx⟩ := hf.exists_diagonal
  apply eq_one_of_square_eq_self
  calc
    _ = h (localize p (diagonal x f)) := congrArg (fun g => h (localize p g)) hx
    _ = _ := map_localize_diagonal h p hp x f

lemma map_untwisted_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    {f : group (Γ:=Γ) (X:=X)} (hf : Untwisted f) : h f=1 := by
  obtain ⟨x,hx⟩ := hf.exists_diagonal
  calc
    _ = h (diagonal x f) := congrArg h hx
    _ = 1 := by
      rw [diagonal,map_mul,
        map_localize_untwisted_eq_one h _ (Prefix.oneBit_ne_empty x false) hf,
        map_localize_untwisted_eq_one h _ (Prefix.oneBit_ne_empty x true) hf,one_mul]

lemma map_localize_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    (p : Prefix X) (hp : p≠Prefix.empty) (f : group (Γ:=Γ) (X:=X)) :
    h (localize p f)=1 := by
  obtain ⟨x,hx⟩ := exists_untwisted_correction f
  have hh := map_localize_untwisted_eq_one h p hp hx
  simp only [map_mul,map_inv] at hh
  rw [map_localize_diagonal h p hp x f] at hh
  exact eq_one_of_square_eq_self (mul_inv_eq_one.mp hh)

/-- Every commutative image of the infinite-coordinate twisted table group is
trivial. The proof uses actual finite table label cancellation and compression. -/
theorem map_eq_one [Infinite X] (h : group (Γ:=Γ) (X:=X) →* H)
    (f : group (Γ:=Γ) (X:=X)) : h f=1 := by
  obtain ⟨x,hx⟩ := exists_untwisted_correction f
  have hh := map_untwisted_eq_one h hx
  have hd : h (diagonal x f)=1 := by
    rw [diagonal,map_mul,
      map_localize_eq_one h _ (Prefix.oneBit_ne_empty x false),
      map_localize_eq_one h _ (Prefix.oneBit_ne_empty x true),one_mul]
  simpa only [map_mul,map_inv,hd,inv_one,mul_one] using hh

instance infinite_group_perfect [Infinite X] : Group.IsPerfect (group (Γ:=Γ) (X:=X)) where
  commutator_eq_top := by
    apply top_unique
    intro f _
    rw [← Abelianization.ker_of]
    exact map_eq_one Abelianization.of f

end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Partition

abbrev size (P : Partition X) : ℕ := @Fintype.card P.index P.finite

lemma size_refinement_bit (P : Partition X) (j : P.index) (x : X) :
    (P.refinement (bit x) j).size=P.size+1 := by
  let := P.finite
  have hp : 0<Fintype.card P.index := Fintype.card_pos_iff.mpr ⟨j⟩
  change Fintype.card ({k : P.index // k≠j} ⊕ Bool)=Fintype.card P.index+1
  rw [Fintype.card_sum,Fintype.card_subtype_compl (fun k => k=j),Fintype.card_subtype_eq,
    Fintype.card_bool]
  omega

/-- Add arbitrarily many complement bricks while leaving a proper selected brick
unchanged. -/
lemma pad (P : Partition X) (i : P.index) (hi : P.brick i≠Prefix.empty) (x : X) (n : ℕ) :
    ∃ Q : Partition X, ∃ j : Q.index, Q.brick j=P.brick i ∧ Q.size=P.size+n := by
  induction n with
  | zero => exact ⟨P,i,rfl,by omega⟩
  | succ n ih =>
      obtain ⟨Q,j,hj,hn⟩ := ih
      obtain ⟨k,hkj⟩ := Q.exists_other j (by rwa [hj])
      refine ⟨Q.refinement (bit x) k,Sum.inl ⟨j,Ne.symm hkj⟩,hj,?_⟩
      rw [size_refinement_bit,hn]
      omega

end Partition

/-- Any two proper finite dyadic bricks are related by an actual untwisted finite
table chart, with no equal-volume or equal-depth restriction. -/
theorem exists_brick_extension [Nonempty X] (p q : Prefix X)
    (hp : p≠Prefix.empty) (hq : q≠Prefix.empty) :
    ∃ h : group (Γ:=Γ) (X:=X), ∀ z,h.val (p.attach z)=q.attach z := by
  obtain ⟨P,i,hi⟩ := p.hasPartition
  obtain ⟨Q,j,hj⟩ := q.hasPartition
  let x : X := Classical.choice inferInstance
  obtain ⟨P',i',hi',hP'⟩ := P.pad i (by rwa [hi]) x Q.size
  obtain ⟨Q',j',hj',hQ'⟩ := Q.pad j (by rwa [hj]) x P.size
  let := P'.finite
  let := Q'.finite
  have hc : Fintype.card P'.index=Fintype.card Q'.index := by
    change P'.size=Q'.size
    omega
  let e : P'.index ≃ Q'.index := Fintype.equivOfCardEq hc
  let e' : P'.index ≃ Q'.index := e.trans (Equiv.swap (e i') j')
  have he : e' i'=j' := by simp [e']
  refine ⟨P'.changeChart Q' e',fun z => ?_⟩
  have hh := P'.changeChart_apply (Γ:=Γ) Q' e' i' z
  rwa [he,hi',hj',hi,hj] at hh

lemma normal_transport_localize [Nonempty X]
    (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal]
    (p q : Prefix X) (hp : p≠Prefix.empty) (hq : q≠Prefix.empty)
    (f : group (Γ:=Γ) (X:=X)) (hf : localize p f∈N) : localize q f∈N := by
  obtain ⟨h,hh⟩ := exists_brick_extension (Γ:=Γ) p q hp hq
  rw [← localize_conj h hh f]
  exact (inferInstance : N.Normal).conj_mem _ hf h

end

section
universe u v
attribute [local instance] Classical.propDecidable
open scoped commutatorElement
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

@[simp] lemma localize_empty (f : group (Γ:=Γ) (X:=X)) : localize Prefix.empty f=f := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change localizePerm Prefix.empty f.val z=f.val z
  simpa only [Prefix.empty_attach] using localizePerm_attach Prefix.empty f.val z

/-- Perfection upgrades the localized double-commutator conclusion to a full
local copy inside every nontrivial normal subgroup. -/
lemma normal_contains_local_copy [Infinite X]
    (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal] (hN : N≠⊥) :
    ∃ p : Prefix X, ∀ f : group (Γ:=Γ) (X:=X),localize p f∈N := by
  obtain ⟨p,hp⟩ := normal_contains_local_commutators N hN
  have hc : commutator (group (Γ:=Γ) (X:=X))≤N.comap (localize p) := by
    rw [commutator_eq_closure,Subgroup.closure_le]
    rintro f ⟨a,b,rfl⟩
    exact hp a b
  exact ⟨p,fun f => hc (Group.IsPerfect.mem_commutator (g:=f))⟩

/-- Simplicity of the actual twisted finite-table permutation group on an
infinite coordinate set. No finite-presentation or simplicity endpoint is
assumed. -/
theorem normal_eq_top [Infinite X]
    (N : Subgroup (group (Γ:=Γ) (X:=X))) [N.Normal] (hN : N≠⊥) : N=⊤ := by
  obtain ⟨p,hp⟩ := normal_contains_local_copy N hN
  by_cases he : p=Prefix.empty
  · apply top_unique
    intro f _
    simpa [he] using hp f
  have hloc (q : Prefix X) (hq : q≠Prefix.empty) (f : group (Γ:=Γ) (X:=X)) :
      localize q f∈N := normal_transport_localize N p q he hq f (hp f)
  have hdiag (x : X) (f : group (Γ:=Γ) (X:=X)) : diagonal x f∈N :=
    N.mul_mem (hloc _ (Prefix.oneBit_ne_empty x false) f)
      (hloc _ (Prefix.oneBit_ne_empty x true) f)
  have hunt (f : group (Γ:=Γ) (X:=X)) (hf : Untwisted f) : f∈N := by
    obtain ⟨x,hx⟩ := hf.exists_diagonal
    rw [hx]
    exact hdiag x f
  apply top_unique
  intro f _
  obtain ⟨x,hx⟩ := exists_untwisted_correction f
  have hr := hunt _ hx
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using N.mul_mem hr (hdiag x f)

instance infinite_group_simple [Infinite X] : IsSimpleGroup (group (Γ:=Γ) (X:=X)) where
  eq_bot_or_eq_top_of_normal N hnormal := by
    let := hnormal
    by_cases hN : N=⊥
    · exact Or.inl hN
    · exact Or.inr (normal_eq_top N hN)

end

universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

instance [Countable X] : Countable (Prefix X) := by
  let : Zero (List Bool) := ⟨[]⟩
  let encode (p : Prefix X) : X →₀ List Bool := Finsupp.ofSupportFinite p.word p.finite_support
  apply Function.Injective.countable (f:=encode)
  intro p q hpq
  apply Prefix.ext
  intro x
  exact congrArg (fun f : X →₀ List Bool => f x) hpq

end Prefix
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Table
variable {f g : Equiv.Perm (Cube X)}

/-- A finite code for all chart data, not a code for arbitrary cube points. -/
def code (A : Table (Γ:=Γ) f) : List (Prefix X × Prefix X × Γ) := by
  letI := A.finite
  exact List.ofFn (fun i : Fin (Fintype.card A.index) =>
    let j := (Fintype.equivFin A.index).symm i
    (A.source j,A.target j,A.label j))

lemma mem_code (A : Table (Γ:=Γ) f) (p q : Prefix X) (a : Γ) :
    (p,q,a)∈A.code ↔ ∃ i,A.source i=p ∧ A.target i=q ∧ A.label i=a := by
  let := A.finite
  simp only [code,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨(Fintype.equivFin A.index).symm i,
      congrArg Prod.fst hi,congrArg (fun t => t.2.1) hi,congrArg (fun t => t.2.2) hi⟩
  · rintro ⟨i,hi,hj,hk⟩
    refine ⟨(Fintype.equivFin A.index) i,?_⟩
    simp [hi,hj,hk]

lemma eq_of_code_eq (A : Table (Γ:=Γ) f) (B : Table (Γ:=Γ) g) (h : A.code=B.code) : f=g := by
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := A.source_cover z
  have hi : (A.source i,A.target i,A.label i)∈B.code := by
    rw [← h]
    exact (A.mem_code _ _ _).mpr ⟨i,rfl,rfl,rfl⟩
  obtain ⟨j,hj,hk,hl⟩ := (B.mem_code _ _ _).mp hi
  rw [A.chart,← hj,B.chart,hk,hl]

end Table

/-- The concrete twisted group is countable under the standing countability
hypotheses, although the Cantor cube itself is uncountable. -/
instance group_countable [Countable Γ] [Countable X] : Countable (group (Γ:=Γ) (X:=X)) := by
  let A (f : group (Γ:=Γ) (X:=X)) : Table (Γ:=Γ) f.val :=
    Classical.choice ((mem_group_iff_table f.val).mp f.property)
  apply Function.Injective.countable (f:=fun f => (A f).code)
  intro f g he
  exact Subtype.ext ((A f).eq_of_code_eq (A g) he)

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
