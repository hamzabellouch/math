import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BoundaryCycles

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
variable {V F : Type} {kind : V → VertexTable.Kind}

/-- A finite open template is given by explicit enumerations of all vertex ports. Internal wires match equal indices; the remaining ports are the interface. -/
structure PortPatch (kind : V → VertexTable.Kind) (I A B : Type) where
  plus : I ⊕ A ≃ PortAt kind true
  minus : I ⊕ B ≃ PortAt kind false
  internalArity : ∀ i, (kind (minus (.inl i)).val.1).arity (minus (.inl i)).val.2 =
    (kind (plus (.inl i)).val.1).arity (plus (.inl i)).val.2

namespace PortPatch
variable {I A B : Type} (P : PortPatch kind I A B)

/-- Closing the interface uses only an whole-port matching, never a matching of independent child germs. -/
def complete (e : A ≃ B)
    (h : ∀ a, (kind (P.minus (.inr (e a))).val.1).arity (P.minus (.inr (e a))).val.2 =
      (kind (P.plus (.inr a)).val.1).arity (P.plus (.inr a)).val.2) : PortWiring kind where
  wire := P.plus.symm |>.trans (Equiv.sumCongr (Equiv.refl I) e) |>.trans P.minus
  arity p := by
    obtain ⟨z,rfl⟩ := P.plus.surjective p
    have he : ((P.plus.symm.trans (Equiv.sumCongr (Equiv.refl I) e)).trans P.minus) (P.plus z)=
        P.minus ((Equiv.sumCongr (Equiv.refl I) e) z) := by simp
    have hg := congrArg (fun p : PortAt kind false => (kind p.val.1).arity p.val.2) he
    cases z with
    | inl i => exact hg.trans (P.internalArity i)
    | inr a => exact hg.trans (h a)

lemma complete_internal (e : A ≃ B)
    (h : ∀ a, (kind (P.minus (.inr (e a))).val.1).arity (P.minus (.inr (e a))).val.2 =
      (kind (P.plus (.inr a)).val.1).arity (P.plus (.inr a)).val.2) (i : I) :
    (P.complete e h).wire (P.plus (.inl i))=P.minus (.inl i) := by
  simp [complete]

lemma complete_external (e : A ≃ B)
    (h : ∀ a, (kind (P.minus (.inr (e a))).val.1).arity (P.minus (.inr (e a))).val.2 =
      (kind (P.plus (.inr a)).val.1).arity (P.plus (.inr a)).val.2) (a : A) :
    (P.complete e h).wire (P.plus (.inr a))=P.minus (.inr (e a)) := by
  simp [complete]

/-- Every port is accounted for exactly once already in the template. -/
theorem port_exhaustive (p : PortAt kind true) :
    (∃ i, P.plus (.inl i)=p) ∨ (∃ a, P.plus (.inr a)=p) := by
  obtain ⟨z,rfl⟩ := P.plus.surjective p
  cases z with
  | inl i => exact .inl ⟨i,rfl⟩
  | inr a => exact .inr ⟨a,rfl⟩

end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {k : Kind}

/-- Ordered list form of a local decoration; none is still the parent. -/
def Decoration.portColor (d : Decoration k F) (p : k.table.Port)
    (j : Option (Fin (k.arity p))) : F := d.color ⟨p,j.map (k.childEnumeration p).symm⟩

lemma Decoration.portColor_child (d : Decoration k F) (p : k.table.Port)
    (j : k.table.Child p) : d.portColor p (some (k.childEnumeration p j))=d.color ⟨p,some j⟩ := by
  dsimp only [Decoration.portColor,Option.map_some]
  rw [Equiv.symm_apply_apply]

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical

/-- An embedding, together with all unconsumed objects, is an exact disjoint partition. This is used on whole ports, never on independent child germs. -/
noncomputable def includeComplement {I P : Type} (f : I ↪ P) :
    I ⊕ {p : P // p∉Set.range f} ≃ P :=
  (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

@[simp] lemma includeComplement_inl {I P : Type} (f : I ↪ P) (i : I) :
    includeComplement f (.inl i)=f i := rfl
@[simp] lemma includeComplement_inr {I P : Type} (f : I ↪ P)
    (p : {p : P // p∉Set.range f}) : includeComplement f (.inr p)=p.val := rfl

namespace PortPatch
variable {V I : Type} {k : V → VertexTable.Kind}
/-- A partial sewing, with every unused port left exposed exactly once. Injectivity prevents accidental multiple use of a repeated occurrence. -/
noncomputable def ofPartial (plus : I ↪ PortAt k true) (minus : I ↪ PortAt k false)
    (h : ∀ i, (k (minus i).val.1).arity (minus i).val.2=
      (k (plus i).val.1).arity (plus i).val.2) :
    PortPatch k I {p : PortAt k true // p∉Set.range plus}
      {p : PortAt k false // p∉Set.range minus} where
  plus := includeComplement plus
  minus := includeComplement minus
  internalArity := h
end PortPatch

namespace VertexTable
/-- The incoming/outgoing main ports at one allowed event. Every remaining port (the split branch) is still present in the original table. -/
def Kind.input : (k : Kind) → k.table.Port
  | .passage _ _ => false
  | .splitting _ _ _ false => .before
  | .splitting _ _ _ true => .after

def Kind.output : (k : Kind) → k.table.Port
  | .passage _ _ => true
  | .splitting _ _ _ false => .after
  | .splitting _ _ _ true => .before

@[simp] lemma Kind.input_endpoint (k : Kind) : k.table.endpoint k.input=true := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> rfl
@[simp] lemma Kind.output_endpoint (k : Kind) : k.table.endpoint k.output=false := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> rfl

lemma Kind.principal_corner (k : Kind) : k.table.mate ⟨k.input,none⟩=⟨k.output,none⟩ := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> rfl
end VertexTable

namespace VariableGallery
open VertexTable
variable {l : ℕ} (kind : Fin (l+1) → Kind)

def input (v : Fin (l+1)) : PortAt kind true :=
  ⟨⟨v,(kind v).input⟩,(kind v).input_endpoint⟩
def output (v : Fin (l+1)) : PortAt kind false :=
  ⟨⟨v,(kind v).output⟩,(kind v).output_endpoint⟩

def internalPlus : Fin l ↪ PortAt kind true where
  toFun j := input kind j.succ
  inj' _ _ h := Fin.succ_inj.mp (congrArg (fun p => p.val.1) h)
def internalMinus : Fin l ↪ PortAt kind false where
  toFun j := output kind j.castSucc
  inj' _ _ h := Fin.castSucc_injective _ (congrArg (fun p => p.val.1) h)

variable (ha : ∀ j : Fin l, (kind j.castSucc).arity (kind j.castSucc).output=
  (kind j.succ).arity (kind j.succ).input)
/-- Variable-length path of split/merge/adjacent events. All side branches are part of its explicit interface, not discarded by the path. -/
noncomputable def patch := PortPatch.ofPartial (internalPlus kind) (internalMinus kind) ha

lemma first_exposed : input kind 0∉Set.range (internalPlus kind) := by
  rintro ⟨j,hj⟩
  have hh := congrArg (fun p => p.val.1.val) hj
  change j.val+1=0 at hh
  omega
lemma last_exposed : output kind (Fin.last l)∉Set.range (internalMinus kind) := by
  rintro ⟨j,hj⟩
  have hh := congrArg (fun p => p.val.1.val) hj
  change j.val=l at hh
  exact (Nat.ne_of_lt j.isLt) hh

/-- Parent corners concatenate with the original orientation. -/
lemma parent_corner (v : Fin (l+1)) :
    localMate (⟨v,(kind v).input,none⟩ : LocalEnd _ kind)=⟨v,(kind v).output,none⟩ := by
  exact congrArg (fun z => (⟨v,z⟩ : LocalEnd _ kind)) ((kind v).principal_corner)

/-- Lists must match in their order, including repetitions. -/
def ColorChain {F : Type} (d : (v : Fin (l+1)) → Decoration (kind v) F) : Prop :=
  ∀ (j : Fin l) (i : Option (Fin ((kind j.castSucc).arity (kind j.castSucc).output))),
    (d j.castSucc).portColor (kind j.castSucc).output i=
      (d j.succ).portColor (kind j.succ).input (i.map (finCongr (ha j)))

end VariableGallery
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

def Decoration.children {k : Kind} (d : Decoration k F) (p : k.table.Port) : List F :=
  List.ofFn (fun j => d.portColor p (some j))

@[simp] lemma Decoration.children_length {k : Kind} (d : Decoration k F) (p : k.table.Port) :
    (d.children p).length=k.arity p := List.length_ofFn

lemma splitting_after_color_false {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (fun i => (splittingDecoration false main big left mid right).portColor .after (some i))=
      Fin.append left (Fin.append mid right) := by
  funext i
  obtain ⟨j,rfl⟩ := (Kind.childEnumeration (.splitting a b c false) .after).surjective i
  calc
    _ = (splittingDecoration false main big left mid right).color ⟨.after,some j⟩ :=
      Decoration.portColor_child (splittingDecoration false main big left mid right) .after j
    _ = _ := by
      change splitColor main big left mid right ⟨.after,some j⟩ =
        Fin.append left (Fin.append mid right) ((afterEnum a b c) j)
      rcases j with j|j|j <;>
        simp [splitColor,afterEnum,Fin.append_left,Fin.append_right]

lemma splitting_before_color_false {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (fun i => (splittingDecoration false main big left mid right).portColor .before (some i))=
      Fin.append left (Fin.append (fun _ : Fin 1 => big) right) := by
  funext i
  obtain ⟨j,rfl⟩ := (Kind.childEnumeration (.splitting a b c false) .before).surjective i
  calc
    _ = (splittingDecoration false main big left mid right).color ⟨.before,some j⟩ :=
      Decoration.portColor_child (splittingDecoration false main big left mid right) .before j
    _ = _ := by
      change splitColor main big left mid right ⟨.before,some j⟩ =
        Fin.append left (Fin.append (fun _ : Fin 1 => big) right) ((beforeEnum a c) j)
      rcases j with j|j|j <;>
        simp [splitColor,beforeEnum,Fin.append_left,Fin.append_right]

@[simp] lemma splitting_after_children_false {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (splittingDecoration false main big left mid right).children .after=
      List.ofFn left ++ (List.ofFn mid ++ List.ofFn right) := by
  calc
    _ = List.ofFn (Fin.append left (Fin.append mid right)) :=
      congrArg (@List.ofFn F (a+(b+c))) (splitting_after_color_false main big left mid right)
    _ = _ := by simp only [List.ofFn_fin_append]

@[simp] lemma splitting_before_children_false {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (splittingDecoration false main big left mid right).children .before=
      List.ofFn left ++ (big :: List.ofFn right) := by
  calc
    _ = List.ofFn (Fin.append left (Fin.append (fun _ : Fin 1 => big) right)) :=
      congrArg (@List.ofFn F (a+(1+c))) (splitting_before_color_false main big left mid right)
    _ = _ := by simp only [List.ofFn_fin_append]; simp

@[simp] lemma splitting_branch_children_false {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (splittingDecoration false main big left mid right).children .branch=List.ofFn mid := by
  rfl

lemma splitting_after_color_true {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (fun i => (splittingDecoration true main big left mid right).portColor .after (some i))=
      Fin.append left (Fin.append mid right) := by
  funext i
  obtain ⟨j,rfl⟩ := (Kind.childEnumeration (.splitting a b c true) .after).surjective i
  calc
    _ = (splittingDecoration true main big left mid right).color ⟨.after,some j⟩ :=
      Decoration.portColor_child (splittingDecoration true main big left mid right) .after j
    _ = _ := by
      change splitColor main big left mid right ⟨.after,some j⟩ =
        Fin.append left (Fin.append mid right) ((afterEnum a b c) j)
      rcases j with j|j|j <;>
        simp [splitColor,afterEnum,Fin.append_left,Fin.append_right]

lemma splitting_before_color_true {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (fun i => (splittingDecoration true main big left mid right).portColor .before (some i))=
      Fin.append left (Fin.append (fun _ : Fin 1 => big) right) := by
  funext i
  obtain ⟨j,rfl⟩ := (Kind.childEnumeration (.splitting a b c true) .before).surjective i
  calc
    _ = (splittingDecoration true main big left mid right).color ⟨.before,some j⟩ :=
      Decoration.portColor_child (splittingDecoration true main big left mid right) .before j
    _ = _ := by
      change splitColor main big left mid right ⟨.before,some j⟩ =
        Fin.append left (Fin.append (fun _ : Fin 1 => big) right) ((beforeEnum a c) j)
      rcases j with j|j|j <;>
        simp [splitColor,beforeEnum,Fin.append_left,Fin.append_right]

@[simp] lemma splitting_after_children_true {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (splittingDecoration true main big left mid right).children .after=
      List.ofFn left ++ (List.ofFn mid ++ List.ofFn right) := by
  calc
    _ = List.ofFn (Fin.append left (Fin.append mid right)) :=
      congrArg (@List.ofFn F (a+(b+c))) (splitting_after_color_true main big left mid right)
    _ = _ := by simp only [List.ofFn_fin_append]

@[simp] lemma splitting_before_children_true {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (splittingDecoration true main big left mid right).children .before=
      List.ofFn left ++ (big :: List.ofFn right) := by
  calc
    _ = List.ofFn (Fin.append left (Fin.append (fun _ : Fin 1 => big) right)) :=
      congrArg (@List.ofFn F (a+(1+c))) (splitting_before_color_true main big left mid right)
    _ = _ := by simp only [List.ofFn_fin_append]; simp

@[simp] lemma splitting_branch_children_true {a b c : ℕ} (main big : F)
    (left : Fin a → F) (mid : Fin b → F) (right : Fin c → F) :
    (splittingDecoration true main big left mid right).children .branch=List.ofFn mid := by
  rfl

/-- One split/merge slot in the source's ordered flag gallery. -/
def splitLists (rev : Bool) (main big : F) (left mid right : List F) :
    Decoration (.splitting left.length mid.length right.length rev) F :=
  splittingDecoration rev main big left.get mid.get right.get

@[simp] lemma splitLists_input (rev : Bool) (main big : F) (left mid right : List F) :
    (splitLists rev main big left mid right).children
      (Kind.splitting left.length mid.length right.length rev).input=
      if rev then left++(mid++right) else left++big::right := by
  cases rev <;> simp only [splitLists,Kind.input,Bool.false_eq_true,↓reduceIte,
    splitting_before_children_false,splitting_after_children_true,List.ofFn_get]
@[simp] lemma splitLists_output (rev : Bool) (main big : F) (left mid right : List F) :
    (splitLists rev main big left mid right).children
      (Kind.splitting left.length mid.length right.length rev).output=
      if rev then left++big::right else left++(mid++right) := by
  cases rev <;> simp only [splitLists,Kind.output,Bool.false_eq_true,↓reduceIte,
    splitting_after_children_false,splitting_before_children_true,List.ofFn_get]
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

/-- A step records the permitted vertex and all of its ports; the two lists only designate the main band through that vertex. Branch ports are not removed or identified. -/
structure OrderedStep (parent : F) (before after : List F) where
  kind : Kind
  decoration : Decoration kind F
  input_parent : decoration.portColor kind.input none=parent
  output_parent : decoration.portColor kind.output none=parent
  input_children : decoration.children kind.input=before
  output_children : decoration.children kind.output=after

inductive OrderedChain (parent : F) : List F → List F → Type
  | refl (l : List F) : OrderedChain parent l l
  | step {a b c : List F} : OrderedStep parent a b → OrderedChain parent b c →
      OrderedChain parent a c

namespace OrderedChain
variable {parent : F} {a b c : List F}
def single (s : OrderedStep parent a b) : OrderedChain parent a b := .step s (.refl _)
def trans : {a b c : List F} → OrderedChain parent a b → OrderedChain parent b c → OrderedChain parent a c
  | _,_,_,.refl _,q => q
  | _,_,_,.step s p,q => .step s (trans p q)
end OrderedChain

/-- An split vertex, retaining its branch with its fine ordered grades. -/
def OrderedStep.split (parent big : F) (left mid right : List F) :
    OrderedStep parent (left++big::right) (left++(mid++right)) where
  kind := .splitting left.length mid.length right.length false
  decoration := splitLists false parent big left mid right
  input_parent := rfl
  output_parent := rfl
  input_children := by simp
  output_children := by simp

/-- Reversal retains the same three whole ports, with all their orientations reversed according to the source merge convention. -/
def OrderedStep.merge (parent big : F) (left mid right : List F) :
    OrderedStep parent (left++(mid++right)) (left++big::right) where
  kind := .splitting left.length mid.length right.length true
  decoration := splitLists true parent big left mid right
  input_parent := rfl
  output_parent := rfl
  input_children := by simp
  output_children := by simp

def OrderedStep.passage (parent : F) {m : ℕ} (t : Passage m) (f : Fin m → F) :
    OrderedStep parent (List.ofFn f) (List.ofFn (f ∘ t.permutation.symm)) where
  kind := .passage m t
  decoration := passageDecoration t parent f
  input_parent := rfl
  output_parent := rfl
  input_children := rfl
  output_children := rfl

/-- The finite row refinement is produced one split at a time. Each named row branch stays in the template interface. No flag-factorization or geometric-bundle premise occurs in this construction. -/
theorem refine_rows (parent : F) (rows : List (F × List F)) (left right : List F) :
    Nonempty (OrderedChain parent (left++(rows.map Prod.fst++right))
      (left++(rows.flatMap Prod.snd++right))) ∧
    Nonempty (OrderedChain parent (left++(rows.flatMap Prod.snd++right))
      (left++(rows.map Prod.fst++right))) := by
  induction rows generalizing left with
  | nil => exact ⟨⟨.refl _⟩,⟨.refl _⟩⟩
  | cons r rows ih =>
    obtain ⟨⟨p⟩,⟨q⟩⟩ := ih (left++r.2)
    constructor
    · have h := (OrderedChain.single (OrderedStep.split parent r.1 left r.2
        (rows.map Prod.fst++right))).trans (by simpa [List.append_assoc] using p)
      exact ⟨by simpa [List.append_assoc] using h⟩
    · have h := q.trans (by simpa [List.append_assoc] using
        (OrderedChain.single (OrderedStep.merge parent r.1 left r.2
          (rows.map Prod.fst++right))))
      exact ⟨by simpa [List.append_assoc] using h⟩

/-- Every finite permutation of the common fine grades is produced entirely by the source's adjacent interchanges. Zero grades and repeated facet names are allowed; no distinctness condition is imposed on f. -/
theorem permutation_chain (parent : F) {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ∀ f : Fin m → F, Nonempty (OrderedChain parent (List.ofFn f)
      (List.ofFn (f ∘ σ.symm))) := by
  cases m with
  | zero =>
    intro f
    simpa using (show Nonempty (OrderedChain parent ([] : List F) []) from ⟨.refl _⟩)
  | succ n =>
    have hs : σ∈Submonoid.closure (Set.range (fun i : Fin n => Equiv.swap i.castSucc i.succ)) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i,rfl⟩
      intro f
      exact ⟨OrderedChain.single (OrderedStep.passage parent (.interchange (m:=n+1) i) f)⟩
    | one =>
      intro f
      exact ⟨OrderedChain.refl (parent:=parent) (List.ofFn f)⟩
    | mul x y hx hy ihx ihy =>
      intro f
      obtain ⟨p⟩ := ihy f
      obtain ⟨q⟩ := ihx (f ∘ y.symm)
      exact ⟨p.trans q⟩

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

end

end OAI
