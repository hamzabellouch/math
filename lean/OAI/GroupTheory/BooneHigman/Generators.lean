import OAI.GroupTheory.BooneHigman.Trees

namespace OAI

noncomputable section

/-!
Concrete finite generators of the twisted group.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

abbrev left (x : X) := Prefix.oneBit x false
abbrev right (x : X) := Prefix.oneBit x true

def associator (x : X) : group (Γ:=Γ) (X:=X) :=
  (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition.changeChart
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm

lemma associator_left (x : X) (z : Cube X) :
    (associator (Γ:=Γ) x).val ((left x).attach z)=
      ((left x).comp (left x)).attach z := by
  have h := Partition.changeChart_apply (Γ:=Γ)
    (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm (Sum.inl PUnit.unit) z
  simpa only [associator,left,Equiv.sumAssoc_symm_apply_inl,Tree.partition,Tree.brick,Prefix.comp_empty] using h

def flip (x : X) : group (Γ:=Γ) (X:=X) :=
  (Partition.bit x).permute Equiv.boolNot

lemma flip_left (x : X) (z : Cube X) :
    (flip (Γ:=Γ) x).val ((left x).attach z)=(right x).attach z :=
  (Partition.bit x).permute_attach Equiv.boolNot false z

/-- Four untwisted elements, together with the root and one half-copy of the
acting group. This is an explicitly finitely generated subgroup when Γ is FG. -/
def finiteSet (x : X) : Finset (group (Γ:=Γ) (X:=X)) :=
  {associator x,localize (left x) (associator x),flip x,localize (left x) (flip x)}

def subgroup (x : X) : Subgroup (group (Γ:=Γ) (X:=X)) :=
  (embedding (Γ:=Γ) (X:=X)).range ⊔ ((localize (left x)).comp embedding).range ⊔
    Subgroup.closure (↑(finiteSet (Γ:=Γ) x) : Set (group (Γ:=Γ) (X:=X)))

lemma root_mem (x : X) (g : Γ) : embedding g∈subgroup (Γ:=Γ) x :=
  (show (embedding (Γ:=Γ) (X:=X)).range ≤ subgroup (Γ:=Γ) x from (le_sup_left.trans le_sup_left)) ⟨g,rfl⟩

lemma half_root_mem (x : X) (g : Γ) : localize (left x) (embedding g)∈subgroup (Γ:=Γ) x :=
  (show ((localize (left x)).comp (embedding (Γ:=Γ) (X:=X))).range ≤ subgroup (Γ:=Γ) x from (le_sup_right.trans le_sup_left)) ⟨g,rfl⟩

lemma finite_mem (x : X) {g : group (Γ:=Γ) (X:=X)} (hg : g∈finiteSet x) : g∈subgroup x :=
by
  change g∈(embedding (Γ:=Γ) (X:=X)).range ⊔ ((localize (left x)).comp embedding).range ⊔
    Subgroup.closure (↑(finiteSet (Γ:=Γ) x) : Set (group (Γ:=Γ) (X:=X)))
  exact Subgroup.mem_sup_right (Subgroup.subset_closure hg)

lemma associator_mem (x : X) : associator (Γ:=Γ) x∈subgroup x :=
  finite_mem x (by simp [finiteSet])
lemma flip_mem (x : X) : flip (Γ:=Γ) x∈subgroup x :=
  finite_mem x (by simp [finiteSet])
lemma half_associator_mem (x : X) : localize (left x) (associator (Γ:=Γ) x)∈subgroup x :=
  finite_mem x (by simp [finiteSet])
lemma half_flip_mem (x : X) : localize (left x) (flip (Γ:=Γ) x)∈subgroup x :=
  finite_mem x (by simp [finiteSet])

lemma double_local_mem (x : X) (g : group (Γ:=Γ) (X:=X))
    (hg : localize (left x) g∈subgroup x) :
    localize (left x) (localize (left x) g)∈subgroup x := by
  rw [← localize_comp,← localize_conj (associator x) (associator_left x)]
  exact (subgroup x).mul_mem ((subgroup x).mul_mem (associator_mem x) hg)
    ((subgroup x).inv_mem (associator_mem x))

lemma left_local_mem (x : X) {g : group (Γ:=Γ) (X:=X)} (hg : g∈subgroup x) :
    localize (left x) g∈subgroup x := by
  have h : subgroup (Γ:=Γ) x≤(subgroup x).comap (localize (left x)) := by
    refine sup_le (sup_le ?_ ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro g ⟨a,rfl⟩
      exact half_root_mem x a
    · rintro g ⟨a,rfl⟩
      exact double_local_mem x (embedding a) (half_root_mem x a)
    · intro a ha
      simp only [finiteSet,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha
      rcases ha with rfl|rfl|rfl|rfl
      · exact half_associator_mem x
      · exact double_local_mem x _ (half_associator_mem x)
      · exact half_flip_mem x
      · exact double_local_mem x _ (half_flip_mem x)
  exact h hg

lemma right_local_mem (x : X) {g : group (Γ:=Γ) (X:=X)} (hg : g∈subgroup x) :
    localize (right x) g∈subgroup x := by
  rw [← localize_conj (flip x) (flip_left x)]
  exact (subgroup x).mul_mem ((subgroup x).mul_mem (flip_mem x) (left_local_mem x hg))
    ((subgroup x).inv_mem (flip_mem x))

lemma subgroup_fg (x : X) [Group.FG Γ] : (subgroup (Γ:=Γ) x).FG := by
  have h₁ : (embedding (Γ:=Γ) (X:=X)).range.FG :=
    (Group.fg_iff_subgroup_fg _).mp inferInstance
  have h₂ : ((localize (left x)).comp (embedding (Γ:=Γ) (X:=X))).range.FG :=
    (Group.fg_iff_subgroup_fg _).mp inferInstance
  have h₃ : (Subgroup.closure (finiteSet (Γ:=Γ) x : Set (group (Γ:=Γ) (X:=X)))).FG :=
    (Group.fg_iff_subgroup_fg _).mp inferInstance
  exact (h₁.sup h₂).sup h₃

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

@[simp] lemma twistPrefix_oneBit (g : Γ) (x : X) (b : Bool) :
    twistPrefix g (Prefix.oneBit x b)=Prefix.oneBit (g • x) b := by
  ext y
  simp only [twistPrefix_word,Prefix.oneBit_word,inv_smul_eq_iff]

namespace Generators
/-- The untwisted coordinate baker: move a leading bit from x to y. -/
def baker (x y : X) : group (Γ:=Γ) (X:=X) :=
  (Partition.bit x).changeChart (Partition.bit y) (Equiv.refl Bool)

@[simp] lemma baker_attach (x y : X) (b : Bool) (z : Cube X) :
    (baker (Γ:=Γ) x y).val ((Prefix.oneBit x b).attach z)=
      (Prefix.oneBit y b).attach z :=
  (Partition.bit x).changeChart_apply (Partition.bit y) (Equiv.refl Bool) b z

lemma baker_inverse (x y : X) : (baker (Γ:=Γ) x y)⁻¹=baker y x := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit y).cover z
  apply (baker (Γ:=Γ) x y).val.injective
  change (baker (Γ:=Γ) x y).val ((baker (Γ:=Γ) x y).val.symm
    ((Prefix.oneBit y b).attach w))=_
  rw [Equiv.apply_symm_apply,baker_attach,baker_attach]

lemma baker_smul (x : X) (g : Γ) :
    baker (g • x) x=diagonal x (embedding g) * (embedding g)⁻¹ := by
  rw [← map_inv]
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨b,⟨w,rfl⟩,_⟩ := (Partition.bit (g • x)).cover z
  rw [baker_attach]
  change _=(diagonal x (embedding g)).val (twist g⁻¹ ((Prefix.oneBit (g • x) b).attach w))
  rw [twist_attach,twistPrefix_oneBit,inv_smul_smul,diagonal_attach]
  change _=(Prefix.oneBit x b).attach (twist g (twist g⁻¹ w))
  rw [twist_twist_inv]

lemma baker_smul_mem (x : X) (g : Γ) : baker (g • x) x∈subgroup (Γ:=Γ) x := by
  rw [baker_smul]
  exact (subgroup x).mul_mem
    ((subgroup x).mul_mem (left_local_mem x (root_mem x g)) (right_local_mem x (root_mem x g)))
    ((subgroup x).inv_mem (root_mem x g))

variable [MulAction.IsPretransitive Γ X]

lemma baker_mem (x y : X) : baker (Γ:=Γ) x y∈subgroup x := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Γ x y
  have h := (subgroup (Γ:=Γ) x).inv_mem (baker_smul_mem x g)
  rwa [baker_inverse,hg] at h

lemma bit_local_mem (x y : X) (b : Bool) {g : group (Γ:=Γ) (X:=X)}
    (hg : g∈subgroup x) : localize (Prefix.oneBit y b) g∈subgroup x := by
  rw [← localize_conj (baker x y) (baker_attach x y b)]
  apply (subgroup x).mul_mem
  · apply (subgroup x).mul_mem (baker_mem x y)
    cases b
    · exact left_local_mem x hg
    · exact right_local_mem x hg
  · exact (subgroup x).inv_mem (baker_mem x y)

lemma word_local_mem (x y : X) (w : List Bool) {g : group (Γ:=Γ) (X:=X)}
    (hg : g∈subgroup x) : localize (Prefix.atWord y w) g∈subgroup x := by
  induction w with
  | nil => simpa only [Prefix.atWord_nil,localize_empty] using hg
  | cons b w ih =>
    rw [Prefix.atWord_cons,localize_comp]
    exact bit_local_mem x y b ih

lemma prefix_local_mem (x : X) (p : Prefix X) {g : group (Γ:=Γ) (X:=X)}
    (hg : g∈subgroup x) : localize p g∈subgroup x := by
  suffices ∀ (s : Finset X) (q : Prefix X),
      (∀ y,q.word y≠[] → y∈s) → localize q g∈subgroup x by
    exact this p.finite_support.toFinset p (by intro y hy; simpa using hy)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    have he : q=Prefix.empty := by
      apply Prefix.ext
      intro y
      by_contra hn
      exact Finset.notMem_empty y (hq y hn)
    simpa only [he,localize_empty] using hg
  | @insert y s hys ih =>
    intro q hq
    have hq' : localize (q.erase y) g∈subgroup x := ih _ (by
      intro z hz
      have hzy : z≠y := by intro he; subst z; exact hz (by simp)
      have hqz : q.word z≠[] := by simpa [hzy] using hz
      exact (Finset.mem_insert.mp (hq z hqz)).resolve_left hzy)
    rw [← q.atWord_comp_erase y,localize_comp]
    exact word_local_mem x y (q.word y) hq'

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

lemma oneBit_outside (x : X) {a b : Bool} (hab : a≠b) (z : Cube X) :
    (Prefix.oneBit x a).attach z∉Set.range (Prefix.oneBit x b).attach := by
  intro h
  exact hab (((Prefix.mem_oneBit x a _).mp ⟨z,rfl⟩).symm.trans
    ((Prefix.mem_oneBit x b _).mp h))

def sumElement (y : X) (g h : group (Γ:=Γ) (X:=X)) : group (Γ:=Γ) (X:=X) :=
  localize (Prefix.oneBit y false) g * localize (Prefix.oneBit y true) h

@[simp] lemma sumElement_left (y : X) (g h : group (Γ:=Γ) (X:=X)) (z : Cube X) :
    (sumElement y g h).val ((Prefix.oneBit y false).attach z)=
      (Prefix.oneBit y false).attach (g.val z) := by
  change localizePerm (Prefix.oneBit y false) g.val
    (localizePerm (Prefix.oneBit y true) h.val ((Prefix.oneBit y false).attach z))=_
  rw [localizePerm_outside _ _ (oneBit_outside y Bool.false_ne_true z),localizePerm_attach]

@[simp] lemma sumElement_right (y : X) (g h : group (Γ:=Γ) (X:=X)) (z : Cube X) :
    (sumElement y g h).val ((Prefix.oneBit y true).attach z)=
      (Prefix.oneBit y true).attach (h.val z) := by
  change localizePerm (Prefix.oneBit y false) g.val
    (localizePerm (Prefix.oneBit y true) h.val ((Prefix.oneBit y true).attach z))=_
  rw [localizePerm_attach,localizePerm_outside _ _ (oneBit_outside y (Ne.symm Bool.false_ne_true) (h.val z))]

namespace Generators
variable (x : X)
/-- A complete chart change between coloured splitting trees, already lying in
the proposed finite-generator subgroup. Leaf order is not imposed. -/
structure Move (s t : Tree X) where
  leaves : s.Leaves ≃ t.Leaves
  element : group (Γ:=Γ) (X:=X)
  mem_subgroup : element∈subgroup (Γ:=Γ) x
  chart : ∀ i z,element.val ((s.brick i).attach z)=(t.brick (leaves i)).attach z

namespace Move
variable {x : X} {s t r : Tree X}

def refl (s : Tree X) : Move (Γ:=Γ) x s s where
  leaves := Equiv.refl _
  element := 1
  mem_subgroup := (subgroup x).one_mem
  chart _ _ := rfl

def trans (h : Move (Γ:=Γ) x s t) (k : Move (Γ:=Γ) x t r) : Move (Γ:=Γ) x s r where
  leaves := h.leaves.trans k.leaves
  element := k.element*h.element
  mem_subgroup := (subgroup x).mul_mem k.mem_subgroup h.mem_subgroup
  chart i z := by
    change k.element.val (h.element.val ((s.brick i).attach z))=_
    rw [h.chart,k.chart]
    rfl

def symm (h : Move (Γ:=Γ) x s t) : Move (Γ:=Γ) x t s where
  leaves := h.leaves.symm
  element := h.element⁻¹
  mem_subgroup := (subgroup x).inv_mem h.mem_subgroup
  chart i z := by
    apply h.element.val.injective
    change h.element.val (h.element.val.symm ((t.brick i).attach z))=_
    rw [Equiv.apply_symm_apply,h.chart,Equiv.apply_symm_apply]

lemma element_eq_chart (h : Move (Γ:=Γ) x s t) :
    h.element=s.partition.changeChart t.partition h.leaves := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := s.cover z
  exact (h.chart i w).trans (s.partition.changeChart_apply t.partition h.leaves i w).symm

variable [MulAction.IsPretransitive Γ X]

def join {s₁ s₂ t₁ t₂ : Tree X} (h : Move (Γ:=Γ) x s₁ t₁)
    (k : Move (Γ:=Γ) x s₂ t₂) (y : X) :
    Move (Γ:=Γ) x (Tree.split y s₁ s₂) (Tree.split y t₁ t₂) where
  leaves := Equiv.sumCongr h.leaves k.leaves
  element := sumElement y h.element k.element
  mem_subgroup := (subgroup x).mul_mem (bit_local_mem x y false h.mem_subgroup)
    (bit_local_mem x y true k.mem_subgroup)
  chart i z := by
    cases i with
    | inl i =>
      change (sumElement y h.element k.element).val
        (((Prefix.oneBit y false).comp (s₁.brick i)).attach z)=
        ((Prefix.oneBit y false).comp (t₁.brick (h.leaves i))).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_left,h.chart]
    | inr i =>
      change (sumElement y h.element k.element).val
        (((Prefix.oneBit y true).comp (s₂.brick i)).attach z)=
        ((Prefix.oneBit y true).comp (t₂.brick (k.leaves i))).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_right,k.chart]

def recolor (y : X) (a b : Tree X) :
    Move (Γ:=Γ) x (Tree.split y a b) (Tree.split x a b) where
  leaves := Equiv.refl _
  element := baker y x
  mem_subgroup := by
    rw [← baker_inverse]
    exact (subgroup x).inv_mem (baker_mem x y)
  chart i z := by
    cases i with
    | inl i =>
      change (baker (Γ:=Γ) y x).val (((Prefix.oneBit y false).comp (a.brick i)).attach z)=
        ((Prefix.oneBit x false).comp (a.brick i)).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,baker_attach]
    | inr i =>
      change (baker (Γ:=Γ) y x).val (((Prefix.oneBit y true).comp (b.brick i)).attach z)=
        ((Prefix.oneBit x true).comp (b.brick i)).attach z
      rw [Prefix.comp_attach,Prefix.comp_attach,baker_attach]

end Move

lemma associator_middle (x : X) (z : Cube X) :
    (associator (Γ:=Γ) x).val (((right x).comp (left x)).attach z)=
      ((left x).comp (right x)).attach z := by
  have h := Partition.changeChart_apply (Γ:=Γ)
    (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm (Sum.inr (Sum.inl PUnit.unit)) z
  simpa only [associator,left,right,Equiv.sumAssoc_symm_apply_inr_inl,Tree.partition,
    Tree.brick,Prefix.comp_empty] using h

lemma associator_right (x : X) (z : Cube X) :
    (associator (Γ:=Γ) x).val (((right x).comp (right x)).attach z)=
      (right x).attach z := by
  have h := Partition.changeChart_apply (Γ:=Γ)
    (Tree.split x Tree.leaf (Tree.split x Tree.leaf Tree.leaf)).partition
    (Tree.split x (Tree.split x Tree.leaf Tree.leaf) Tree.leaf).partition
    (Equiv.sumAssoc PUnit PUnit PUnit).symm (Sum.inr (Sum.inr PUnit.unit)) z
  simpa only [associator,left,right,Equiv.sumAssoc_symm_apply_inr_inr,Tree.partition,
    Tree.brick,Prefix.comp_empty] using h

namespace Move

def rotate (a b c : Tree X) :
    Move (Γ:=Γ) x (Tree.split x a (Tree.split x b c)) (Tree.split x (Tree.split x a b) c) where
  leaves := (Equiv.sumAssoc a.Leaves b.Leaves c.Leaves).symm
  element := associator x
  mem_subgroup := associator_mem x
  chart i z := by
    cases i with
    | inl i =>
      change (associator (Γ:=Γ) x).val (((left x).comp (a.brick i)).attach z)=
        ((left x).comp ((left x).comp (a.brick i))).attach z
      simp only [Prefix.comp_attach]
      simpa only [Prefix.comp_attach] using associator_left (Γ:=Γ) x ((a.brick i).attach z)
    | inr i =>
      cases i with
      | inl i =>
        change (associator (Γ:=Γ) x).val (((right x).comp ((left x).comp (b.brick i))).attach z)=
          ((left x).comp ((right x).comp (b.brick i))).attach z
        simpa only [Prefix.comp_attach] using associator_middle (Γ:=Γ) x ((b.brick i).attach z)
      | inr i =>
        change (associator (Γ:=Γ) x).val (((right x).comp ((right x).comp (c.brick i))).attach z)=
          ((right x).comp (c.brick i)).attach z
        simpa only [Prefix.comp_attach] using associator_right (Γ:=Γ) x ((c.brick i).attach z)

end Move

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Tree

abbrev linear (x : X) : ℕ → Tree X
  | 0 => .leaf
  | n+1 => .split x .leaf (linear x n)

lemma linear_card (x : X) (n : ℕ) : Fintype.card (linear x n).Leaves=n+1 := by
  induction n with
  | zero => exact Fintype.card_punit
  | succ n ih =>
    change Fintype.card (PUnit ⊕ (linear x n).Leaves)=n+1+1
    rw [Fintype.card_sum,Fintype.card_punit,ih]
    omega

end Tree
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

/-- Binary associativity reduces two right combs to one right comb. -/
def linearJoin (m n : ℕ) :
    Move (Γ:=Γ) x (Tree.split x (Tree.linear x m) (Tree.linear x n))
      (Tree.linear x (m+n+1)) := by
  induction m with
  | zero =>
    simpa only [Nat.zero_add,Tree.linear] using
      (Move.refl (Γ:=Γ) (x:=x) (Tree.split x Tree.leaf (Tree.linear x n)))
  | succ m ih =>
    have h := (Move.rotate (Γ:=Γ) x Tree.leaf (Tree.linear x m) (Tree.linear x n)).symm
    have k := (Move.refl (Γ:=Γ) (x:=x) Tree.leaf).join ih x
    simpa only [Tree.linear,Nat.succ_add,Nat.add_succ] using h.trans k

lemma exists_linear (t : Tree X) :
    ∃ n : ℕ,Nonempty (Move (Γ:=Γ) x t (Tree.linear x n)) := by
  induction t with
  | leaf => exact ⟨0,⟨Move.refl Tree.leaf⟩⟩
  | split y a b ha hb =>
    obtain ⟨m,⟨h⟩⟩ := ha
    obtain ⟨n,⟨k⟩⟩ := hb
    exact ⟨m+n+1,⟨((h.join k y).trans (Move.recolor y _ _)).trans (linearJoin x m n)⟩⟩

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

/-- Use one fixed equality decision so dependent comb induction does not change
which decision procedure is stored in a transposition. The permutation is the
usual Mathlib transposition. -/
abbrev fixedSwap {A : Type*} (a b : A) : Equiv.Perm A :=
  @Equiv.swap A (Classical.decEq A) a b

variable (x : X) [MulAction.IsPretransitive Γ X]

lemma join_permute_mem {a b : Tree X} (e : Equiv.Perm a.Leaves) (f : Equiv.Perm b.Leaves)
    (he : a.partition.permute (Γ:=Γ) e∈subgroup x)
    (hf : b.partition.permute (Γ:=Γ) f∈subgroup x) (y : X) :
    (Tree.split y a b).partition.permute (Γ:=Γ) (Equiv.sumCongr e f)∈subgroup x := by
  let h : Move (Γ:=Γ) x a a := ⟨e,a.partition.permute e,he,a.partition.permute_attach e⟩
  let k : Move (Γ:=Γ) x b b := ⟨f,b.partition.permute f,hf,b.partition.permute_attach f⟩
  have hh := (h.join k y).mem_subgroup
  rw [(h.join k y).element_eq_chart] at hh
  exact hh

omit [MulAction.IsPretransitive Γ X] in
@[simp] lemma flip_attach (x : X) (b : Bool) (z : Cube X) :
    (flip (Γ:=Γ) x).val ((Prefix.oneBit x b).attach z)=
      (Prefix.oneBit x (!b)).attach z :=
  (Partition.bit x).permute_attach Equiv.boolNot b z

omit [MulAction.IsPretransitive Γ X] in
lemma linear_two_swap :
    (Tree.linear x 1).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr PUnit.unit))=flip x := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := (Tree.linear x 1).cover z
  rw [Partition.permute_attach]
  cases i with
  | inl i =>
    cases i
    simp only [Equiv.swap_apply_left,Tree.partition,Tree.linear,Tree.brick,
      Prefix.comp_empty,flip_attach,Bool.not_false]
  | inr i =>
    cases i
    simp only [Equiv.swap_apply_right,Tree.partition,Tree.linear,Tree.brick,
      Prefix.comp_empty,flip_attach,Bool.not_true]

omit [MulAction.IsPretransitive Γ X] in
/-- The first two leaves of every nontrivial right comb can be interchanged
using the associator and a half-flip. -/
lemma linear_front_swap (n : ℕ) :
    (Tree.linear x (n+2)).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)))=
      (associator x)⁻¹ * localize (left x) (flip x) * associator x := by
  classical
  apply (mul_left_cancel_iff (a:=associator (Γ:=Γ) x)).mp
  rw [← mul_assoc,← mul_assoc,mul_inv_cancel,one_mul]
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨i,⟨w,rfl⟩,_⟩ := (Tree.linear x (n+2)).cover z
  change (associator (Γ:=Γ) x).val
    (((Tree.linear x (n+2)).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)))).val
      (((Tree.linear x (n+2)).brick i).attach w))=
    localizePerm (left x) (flip (Γ:=Γ) x).val
      ((associator (Γ:=Γ) x).val (((Tree.linear x (n+2)).brick i).attach w))
  rw [Partition.permute_attach]
  cases i with
  | inl i =>
    cases i
    simp only [Equiv.swap_apply_left,Tree.partition,Tree.linear,Tree.brick,Prefix.comp_empty]
    rw [associator_middle,associator_left]
    simp only [Prefix.comp_attach,localizePerm_attach,flip_attach,Bool.not_false]
  | inr i =>
    cases i with
    | inl i =>
      cases i
      simp only [Equiv.swap_apply_right,Tree.partition,Tree.linear,Tree.brick,Prefix.comp_empty]
      rw [associator_left,associator_middle]
      simp only [Prefix.comp_attach,localizePerm_attach,flip_attach,Bool.not_true]
    | inr j =>
      simp only [Equiv.swap_apply_def,Sum.inr.injEq,Sum.inr_ne_inl,
        ↓reduceIte,Tree.partition]
      change (associator (Γ:=Γ) x).val
        (((right x).comp ((right x).comp ((Tree.linear x n).brick j))).attach w)=_
      simp only [Tree.brick,Prefix.comp_attach]
      have h := associator_right (Γ:=Γ) x (((Tree.linear x n).brick j).attach w)
      rw [Prefix.comp_attach] at h
      rw [h,localizePerm_outside _ _ (oneBit_outside x (Ne.symm Bool.false_ne_true) _)]

omit [MulAction.IsPretransitive Γ X] in
lemma linear_front_mem (n : ℕ) :
    (Tree.linear x (n+2)).partition.permute (Γ:=Γ)
      (fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)))∈subgroup x := by
  rw [linear_front_swap]
  exact (subgroup x).mul_mem
    ((subgroup x).mul_mem ((subgroup x).inv_mem (associator_mem x)) (half_flip_mem x))
    (associator_mem x)

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

lemma swap_eq_fixedSwap {A : Type*} [DecidableEq A] (a b : A) :
    Equiv.swap a b = fixedSwap a b := by
  ext z
  by_cases h : z=a <;> by_cases k : z=b <;> simp [fixedSwap, Equiv.swap_apply_def,h,k]

lemma fixedSwap_self {A : Type*} (a : A) : fixedSwap a a = 1 := by
  simp only [fixedSwap, Equiv.swap_self]
  rfl

lemma fixedSwap_comm {A : Type*} (a b : A) : fixedSwap a b = fixedSwap b a := by
  exact Equiv.swap_comm a b

lemma sum_swap_right {A B : Type} (i j : B) :
    Equiv.sumCongr (Equiv.refl A) (fixedSwap i j)=
      fixedSwap (Sum.inr i) (Sum.inr j) := by
  classical
  apply Equiv.ext
  intro z
  cases z with
  | inl z => simp [Equiv.swap_apply_def]
  | inr z => simp only [Equiv.sumCongr_apply,Equiv.swap_apply_def]; split_ifs <;> simp_all [Equiv.swap_apply_def]

lemma linear_permute_mem (n : ℕ) (e : Equiv.Perm (Tree.linear x n).Leaves) :
    (Tree.linear x n).partition.permute (Γ:=Γ) e∈subgroup x := by
  induction n with
  | zero =>
    have he : e=1 := Subsingleton.elim _ _
    rw [he,map_one]
    exact (subgroup x).one_mem
  | succ n ih =>
    have hcross (j : (Tree.linear x n).Leaves) :
        (Tree.linear x (n+1)).partition.permute (Γ:=Γ)
          (fixedSwap (Sum.inl PUnit.unit) (Sum.inr j))∈subgroup x := by
      cases n with
      | zero =>
        cases j
        have hh := flip_mem (Γ:=Γ) x
        rw [← linear_two_swap] at hh
        exact hh
      | succ k =>
        let E : Equiv.Perm (Tree.linear x (k+2)).Leaves :=
          Equiv.sumCongr (Equiv.refl PUnit.{1}) (fixedSwap (Sum.inl PUnit.unit) j)
        have hE : (Tree.linear x (k+2)).partition.permute (Γ:=Γ) E∈subgroup x :=
          join_permute_mem x (a:=Tree.leaf) (b:=Tree.linear x (k+1))
            (1 : Equiv.Perm PUnit.{1}) (fixedSwap (Sum.inl PUnit.unit) j)
            (by rw [map_one]; exact (subgroup x).one_mem) (ih _) x
        have heq : fixedSwap (Sum.inl PUnit.unit) (Sum.inr j)=
            E * fixedSwap (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit)) * E⁻¹ := by
          have hleft : E (Sum.inl PUnit.unit) = Sum.inl PUnit.unit := rfl
          have hright : E (Sum.inr (Sum.inl PUnit.unit)) = Sum.inr j := by
            simp [E]
          have hh := Equiv.swap_apply_apply E (Sum.inl PUnit.unit) (Sum.inr (Sum.inl PUnit.unit))
          rw [hleft, hright] at hh
          simpa only [swap_eq_fixedSwap] using hh
        rw [heq,map_mul,map_mul,map_inv]
        exact (subgroup x).mul_mem ((subgroup x).mul_mem hE (linear_front_mem x k))
          ((subgroup x).inv_mem hE)
    have hswap (i j : (Tree.linear x (n+1)).Leaves) :
        (Tree.linear x (n+1)).partition.permute (Γ:=Γ) (fixedSwap i j)∈subgroup x := by
      cases i with
      | inl i =>
        cases i
        cases j with
        | inl j =>
          cases j
          rw [fixedSwap_self,map_one]; exact (subgroup x).one_mem
        | inr j => exact hcross j
      | inr i =>
        cases j with
        | inl j =>
          cases j
          rw [fixedSwap_comm]; exact hcross i
        | inr j =>
          rw [← sum_swap_right]
          exact join_permute_mem x (a:=Tree.leaf) (b:=Tree.linear x n)
            (1 : Equiv.Perm PUnit.{1}) (fixedSwap i j)
            (by rw [map_one]; exact (subgroup x).one_mem) (ih _) x
    induction e using Equiv.Perm.swap_induction_on with
    | one => rw [map_one]; exact (subgroup x).one_mem
    | swap_mul e i j _ he =>
      rw [map_mul]
      exact (subgroup x).mul_mem (by simpa only [swap_eq_fixedSwap] using hswap i j) he

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

lemma tree_chart_mem (s t : Tree X) (e : s.Leaves ≃ t.Leaves) :
    s.partition.changeChart (Γ:=Γ) t.partition e∈subgroup x := by
  obtain ⟨m,⟨h⟩⟩ := exists_linear (Γ:=Γ) x s
  obtain ⟨n,⟨k⟩⟩ := exists_linear (Γ:=Γ) x t
  have hmn : m=n := by
    have hc := Fintype.card_congr (h.leaves.symm.trans (e.trans k.leaves))
    rw [Tree.linear_card,Tree.linear_card] at hc
    omega
  subst n
  let E : Equiv.Perm (Tree.linear x m).Leaves := h.leaves.symm.trans (e.trans k.leaves)
  let g := (Tree.linear x m).partition.permute (Γ:=Γ) E
  have heq : s.partition.changeChart (Γ:=Γ) t.partition e=k.element⁻¹*g*h.element := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := s.cover z
    rw [Partition.changeChart_apply]
    change (t.brick (e i)).attach w=k.element.val.symm (g.val (h.element.val ((s.brick i).attach w)))
    rw [h.chart]
    change (t.brick (e i)).attach w=k.element.val.symm
      (((Tree.linear x m).partition.permute (Γ:=Γ) E).val (((Tree.linear x m).brick (h.leaves i)).attach w))
    rw [Partition.permute_attach]
    apply k.element.val.injective
    rw [Equiv.apply_symm_apply,k.chart]
    simp [E]
  rw [heq]
  exact (subgroup x).mul_mem ((subgroup x).mul_mem ((subgroup x).inv_mem k.mem_subgroup)
    (linear_permute_mem x m E)) h.mem_subgroup

lemma tree_decorate_mem (s : Tree X) (a : s.Leaves → Γ) :
    decorate s.partition a∈subgroup x := by
  induction s with
  | leaf =>
    have heq : decorate (Tree.leaf (X:=X)).partition a=embedding (a PUnit.unit) := by
      apply Subtype.ext
      apply Equiv.ext
      intro z
      change decoratePerm (Tree.leaf (X:=X)).partition a z=twist (a PUnit.unit) z
      have h := decoratePerm_attach (Γ:=Γ) (Tree.leaf (X:=X)).partition a PUnit.unit z
      simpa only [Tree.partition,Tree.brick,Prefix.empty_attach] using h
    rw [heq]
    exact root_mem x _
  | split y s t hs ht =>
    have heq : decorate (Tree.split y s t).partition a=
        sumElement y (decorate s.partition (fun i => a (Sum.inl i)))
          (decorate t.partition (fun i => a (Sum.inr i))) := by
      apply Subtype.ext
      apply Equiv.ext
      intro z
      obtain ⟨i,⟨w,rfl⟩,_⟩ := (Tree.split y s t).cover z
      change (decoratePerm (Tree.split y s t).partition a) (((Tree.split y s t).brick i).attach w)=_
      rw [decoratePerm_attach]
      cases i with
      | inl i =>
        change (((Prefix.oneBit y false).comp (s.brick i)).attach (twist (a (Sum.inl i)) w))=
          (sumElement y (decorate s.partition (fun i => a (Sum.inl i)))
            (decorate t.partition (fun i => a (Sum.inr i)))).val
              (((Prefix.oneBit y false).comp (s.brick i)).attach w)
        rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_left,decorate_val,decoratePerm_attach]
      | inr i =>
        change (((Prefix.oneBit y true).comp (t.brick i)).attach (twist (a (Sum.inr i)) w))=
          (sumElement y (decorate s.partition (fun i => a (Sum.inl i)))
            (decorate t.partition (fun i => a (Sum.inr i)))).val
              (((Prefix.oneBit y true).comp (t.brick i)).attach w)
        rw [Prefix.comp_attach,Prefix.comp_attach,sumElement_right,decorate_val,decoratePerm_attach]
    rw [heq]
    exact (subgroup x).mul_mem (bit_local_mem x y false (hs _))
      (bit_local_mem x y true (ht _))

lemma all_mem (f : group (Γ:=Γ) (X:=X)) : f∈subgroup x := by
  obtain ⟨A⟩ := (mem_group_iff_table f.val).mp f.property
  obtain ⟨s,t,B,es,et,hs,ht⟩ := A.exists_tree_pair
  let e := es.symm.trans et
  let a : s.Leaves → Γ := fun i => B.label (es.symm i)
  have heq : f=s.partition.changeChart t.partition e * decorate s.partition a := by
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨i,⟨w,rfl⟩,_⟩ := B.source_cover z
    change f.val ((B.source i).attach w)=
      (s.partition.changeChart (Γ:=Γ) t.partition e).val
        (decoratePerm s.partition a ((B.source i).attach w))
    rw [B.chart,hs i,decoratePerm_attach,Partition.changeChart_apply,ht i]
    simp [e,a]
  rw [heq]
  exact (subgroup x).mul_mem (tree_chart_mem x s t e) (tree_decorate_mem x s a)

lemma subgroup_eq_top : subgroup (Γ:=Γ) x=⊤ := by
  apply top_unique
  intro f _
  exact all_mem x f

include x in
/-- Finite generation is proved for the concrete finite-table group. This is
not the finite-presentation theorem still required at the main endpoint. -/
theorem finite_generation [Group.FG Γ] : Group.FG (group (Γ:=Γ) (X:=X)) := by
  apply Group.fg_def.mpr
  rw [← subgroup_eq_top (Γ:=Γ) x]
  exact subgroup_fg x

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
