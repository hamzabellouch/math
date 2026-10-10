import OAI.GroupTheory.BooneHigman.TreeCoherence

namespace OAI

noncomputable section

/-!
Represented diagrams and actual endpoint evaluation injectivity and equivalence.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v w
open BinaryGroupCategory

/-- A full finite decorated tree pair, including the entire leaf bijection. -/
structure Diagram (Γ:Type u) (X:Type v) where
  source : Tree X
  target : Tree X
  wires : source.Leaves ≃ target.Leaves
  label : source.Leaves → Γ

namespace Diagram
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H)

def value (A:Diagram Γ X) : H :=
  Tree.leafValue d q B A.wires*Tree.fold d B A.source (fun i=>R (A.label i))

def Realizes (A:Diagram Γ X) (f:Equiv.Perm (Cube X)) : Prop :=
  ∀ i z,f ((A.source.brick i).attach z)=(A.target.brick (A.wires i)).attach (twist (A.label i) z)

def root (g:Γ) : Diagram Γ X := ⟨.leaf,.leaf,Equiv.refl _,fun _=>g⟩
omit [MulAction Γ X] in
lemma value_root (g:Γ) : value d q B R (root (X:=X) g)=R g := by
  change Tree.leafValue d q B (a:=.leaf) (b:=.leaf) (Equiv.refl _)*R g=R g
  rw [Tree.leafValue_refl,one_mul]
lemma realizes_root (g:Γ) : Realizes (root (X:=X) g) (twist g) := by
  intro i z; simp only [root,Tree.brick,Prefix.empty_attach]

def inverse (A:Diagram Γ X) : Diagram Γ X :=
  ⟨A.target,A.source,A.wires.symm,fun i=>(A.label (A.wires.symm i))⁻¹⟩

omit [MulAction Γ X] in
lemma value_inverse (x:X) (A:Diagram Γ X) : value d q B R A.inverse=(value d q B R A)⁻¹ := by
  change Tree.leafValue d q B A.wires.symm*
      Tree.fold d B A.target (fun i=>R ((A.label (A.wires.symm i))⁻¹))=_
  simp only [map_inv]
  rw [Tree.leafValue_fold d q B x A.wires.symm _ (fun i=>(R (A.label i))⁻¹) (fun _=>rfl)]
  rw [Tree.fold_inv,Tree.leafValue_symm]
  exact (mul_inv_rev _ _).symm

lemma Realizes.inverse {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (h:Realizes A f) :
    Realizes A.inverse f⁻¹ := by
  change ∀ (i:A.target.Leaves) z, _
  intro i z
  change f.symm ((A.target.brick i).attach z)=
    (A.source.brick (A.wires.symm i)).attach (twist (A.label (A.wires.symm i))⁻¹ z)
  apply f.injective
  rw [f.apply_symm_apply,h,Equiv.apply_symm_apply,twist_twist_inv]

/-- Compose after identifying the two intermediate partitions. -/
def compose (A C:Diagram Γ X) (e:A.target.Leaves ≃ C.source.Leaves) : Diagram Γ X where
  source := A.source
  target := C.target
  wires := (A.wires.trans e).trans C.wires
  label i := C.label (e (A.wires i))*A.label i

omit [MulAction Γ X] in
lemma value_compose (x:X) (A C:Diagram Γ X) (e:A.target.Leaves ≃ C.source.Leaves) :
    value d q B R (compose A C e)=value d q B R C*Tree.leafValue d q B e*value d q B R A := by
  change Tree.leafValue d q B ((A.wires.trans e).trans C.wires)*
    Tree.fold d B A.source (fun i=>R (C.label (e (A.wires i))*A.label i))=_
  simp only [map_mul]
  rw [Tree.leafValue_trans,Tree.fold_mul]
  have hn := Tree.leafValue_fold d q B x (A.wires.trans e)
    (fun i=>R (C.label (e (A.wires i)))) (fun i=>R (C.label i)) (fun _=>rfl)
  calc
    _=Tree.leafValue d q B C.wires*
        (Tree.leafValue d q B (A.wires.trans e)*Tree.fold d B A.source (fun i=>R (C.label (e (A.wires i)))))*
        Tree.fold d B A.source (fun i=>R (A.label i)) := by group
    _=_ := by rw [hn,Tree.leafValue_trans]; dsimp only [value]; group

lemma Realizes.compose {A C:Diagram Γ X} {f g:Equiv.Perm (Cube X)}
    (ha:Realizes A f) (hc:Realizes C g) (e:A.target.Leaves ≃ C.source.Leaves)
    (he:Tree.SameBricks e) : Realizes (compose A C e) (g*f) := by
  change ∀ (i:A.source.Leaves) z, _
  intro i z
  change g (f ((A.source.brick i).attach z))=(C.target.brick (C.wires (e (A.wires i)))).attach
    (twist (C.label (e (A.wires i))*A.label i) z)
  rw [ha,he,hc,twist_twist]

lemma value_one_of_realizes_one (gl:Tree.GridLaw d q B) [FaithfulSMul Γ X]
    (A:Diagram Γ X) (h:Realizes A 1) : value d q B R A=1 := by
  have hr (i:A.source.Leaves) : A.source.brick i=A.target.brick (A.wires i) ∧ 1=A.label i := by
    apply chart_rigidity
    intro z
    simpa only [twist_one,Equiv.Perm.one_apply] using h i z
  rw [value,Tree.leafValue_of_sameBricks d q B gl A.wires (fun i=>(hr i).1),one_mul]
  have hl : (fun i=>R (A.label i))=fun _=>1 := by
    funext i; rw [← (hr i).2,map_one]
  rw [hl,Tree.fold_one]

end Diagram
end

section
universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Tree
lemma graft_brick_symm (a:Tree X) (F:a.Leaves → Tree X) (i:a.Leaves) (j:(F i).Leaves) :
    (a.graft F).brick ((a.graftLeaves F).symm ⟨i,j⟩)=(a.brick i).comp ((F i).brick j) := by
  rw [graft_prefix,Equiv.apply_symm_apply]
end Tree
namespace Diagram

abbrev expansionFamily (A:Diagram Γ X) (F:A.target.Leaves → Tree X) (i:A.source.Leaves) :=
  Tree.mapColors (fun x=>(A.label i)⁻¹ • x) (F (A.wires i))

/-- Expand the whole target and pull every fibre back through its true label. -/
def expand (A:Diagram Γ X) (F:A.target.Leaves → Tree X) : Diagram Γ X where
  source := A.source.graft (A.expansionFamily F)
  target := A.target.graft F
  wires := Tree.graftMap A.wires (A.expansionFamily F) F
    (fun i=>(Tree.colourLeaves (fun x=>(A.label i)⁻¹ • x) (F (A.wires i))).symm)
  label j := A.label ((A.source.graftLeaves (A.expansionFamily F)) j).1

lemma expand_label (A:Diagram Γ X) (F:A.target.Leaves → Tree X)
    (i:A.source.Leaves) (j:(A.expansionFamily F i).Leaves) :
    (A.expand F).label ((A.source.graftLeaves (A.expansionFamily F)).symm ⟨i,j⟩)=A.label i := by
  change A.label ((A.source.graftLeaves (A.expansionFamily F))
    ((A.source.graftLeaves (A.expansionFamily F)).symm ⟨i,j⟩)).1=A.label i
  rw [Equiv.apply_symm_apply]

lemma value_expand (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
    (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g))
    (A:Diagram Γ X) (F:A.target.Leaves → Tree X) : value d q B R (A.expand F)=value d q B R A := by
  change Tree.leafValue d q B (Tree.graftMap A.wires (A.expansionFamily F) F _)*
    Tree.fold d B (A.source.graft (A.expansionFamily F)) (fun i=>R ((A.expand F).label i))=_
  rw [Tree.leafValue_graftMap d q B x,Tree.fold_graft]
  simp only [expand_label]
  rw [mul_assoc,← Tree.fold_mul]
  apply congrArg (Tree.leafValue d q B A.wires * ·)
  exact Tree.fold_congr d B A.source (fun i=>
    Tree.leafValue_uncolour d q B x R hR (A.label i) (F (A.wires i)))

lemma Realizes.expand {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (h:Realizes A f)
    (F:A.target.Leaves → Tree X) : Realizes (A.expand F) f := by
  change ∀ (j:(A.source.graft (A.expansionFamily F)).Leaves) z, _
  intro j z
  obtain ⟨⟨i,k⟩,rfl⟩ := (A.source.graftLeaves (A.expansionFamily F)).symm.surjective j
  change f (((A.source.graft (A.expansionFamily F)).brick _).attach z)=
    ((A.target.graft F).brick (Tree.graftMap A.wires (A.expansionFamily F) F _ _)).attach
      (twist ((A.expand F).label _) z)
  rw [Tree.graftMap_apply,Tree.graft_brick_symm,Tree.graft_brick_symm,expand_label,
    Prefix.comp_attach,h,Prefix.comp_attach]
  congr 1
  have hb := Tree.colour_brick (A.label i)⁻¹ (F (A.wires i))
    ((Tree.colourLeaves (fun x=>(A.label i)⁻¹ • x) (F (A.wires i))).symm k)
  rw [Equiv.apply_symm_apply] at hb
  change twist (A.label i) (((A.expansionFamily F i).brick k).attach z)=_
  rw [hb,untwist_attach]

end Diagram
end

section
universe u v w
open BinaryGroupCategory
attribute [local instance] Classical.propDecidable
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Tree

abbrev gridFill (a:Tree X) (l:List X) (i:a.Leaves) := grid (l.diff (a.brick i).schedule)

lemma gridFill_length (a:Tree X) (l:List X)
    (h:∀ i x,((a.brick i).word x).length≤l.count x)
    (j:(a.graft (a.gridFill l)).Leaves) (x:X) :
    (((a.graft (a.gridFill l)).brick j).word x).length=l.count x := by
  classical
  obtain ⟨⟨i,k⟩,rfl⟩ := (a.graftLeaves (a.gridFill l)).symm.surjective j
  rw [graft_brick_symm]
  change ((a.brick i).word x ++ ((grid (l.diff (a.brick i).schedule)).brick k).word x).length=_
  rw [List.length_append,grid_length,List.count_diff,Prefix.schedule_count]
  exact Nat.add_sub_of_le (h i x)

lemma gridFill_equiv (a:Tree X) (l:List X)
    (h:∀ i x,((a.brick i).word x).length≤l.count x) :
    ∃ e:(a.graft (a.gridFill l)).Leaves ≃ (grid l).Leaves,SameBricks e := by
  let P := (a.graft (a.gridFill l)).partition
  have hh := P.grid_bricks_of_lengths l (a.gridFill_length l h)
  exact ⟨P.indexEquivOfBricks (grid l).partition hh,P.indexEquivOfBricks_spec (grid l).partition hh⟩
end Tree
namespace Diagram
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
variable (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g))
include x hR

lemma refine_target_grid {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (ha:Realizes A f)
    (l:List X) (h:∀ i x,((A.target.brick i).word x).length≤l.count x) :
    ∃ C:Diagram Γ X,Realizes C f ∧ value d q B R C=value d q B R A ∧
      ∃ e:C.target.Leaves ≃ (Tree.grid l).Leaves,Tree.SameBricks e := by
  refine ⟨A.expand (A.target.gridFill l),ha.expand _,value_expand d q B R x hR A _,?_⟩
  exact A.target.gridFill_equiv l h

lemma refine_source_grid {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (ha:Realizes A f)
    (l:List X) (h:∀ i x,((A.source.brick i).word x).length≤l.count x) :
    ∃ C:Diagram Γ X,Realizes C f ∧ value d q B R C=value d q B R A ∧
      ∃ e:C.source.Leaves ≃ (Tree.grid l).Leaves,Tree.SameBricks e := by
  obtain ⟨D,hd,hv,e,he⟩ := refine_target_grid d q B R x hR ha.inverse l h
  refine ⟨D.inverse,by simpa only [inv_inv] using hd.inverse,?_,e,he⟩
  rw [value_inverse d q B R x,hv,value_inverse d q B R x,inv_inv]

/-- The actual tree-pair value is closed under multiplication, synchronizing
all intermediate bricks by a finite grid; no patching assumption is used. -/
lemma product (gl:Tree.GridLaw d q B) {A C:Diagram Γ X} {f g:Equiv.Perm (Cube X)}
    (ha:Realizes A f) (hc:Realizes C g) :
    ∃ D:Diagram Γ X,Realizes D (g*f) ∧ value d q B R D=value d q B R C*value d q B R A := by
  obtain ⟨l,hl⟩ := Partition.exists_tree_grid_bound
    (Sum.elim A.target.brick C.source.brick)
  obtain ⟨A',ha',hvA,e,he⟩ := refine_target_grid d q B R x hR ha l (fun i=>hl (Sum.inl i))
  obtain ⟨C',hc',hvC,e',he'⟩ := refine_source_grid d q B R x hR hc l (fun i=>hl (Sum.inr i))
  refine ⟨compose A' C' (e.trans e'.symm),ha'.compose hc' _ (he.trans he'.symm),?_⟩
  rw [value_compose d q B R x,Tree.leafValue_of_sameBricks d q B gl _ (he.trans he'.symm),
    mul_one,hvC,hvA]

end Diagram
end

universe u v w
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} [Group Γ] [MulAction Γ X] [Group H]
namespace Diagram
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H)

/-- Undecorated full tree wiring. -/
def plain (a b:Tree X) (e:a.Leaves ≃ b.Leaves) : Diagram Γ X := ⟨a,b,e,fun _=>1⟩
omit [MulAction Γ X] in
lemma value_plain (a b:Tree X) (e:a.Leaves ≃ b.Leaves) :
    value d q B R (plain (Γ:=Γ) a b e)=Tree.leafValue d q B e := by
  change Tree.leafValue d q B e*Tree.fold d B a (fun _=>R 1)=_
  simp only [map_one,Tree.fold_one,mul_one]
lemma realizes_plain (a b:Tree X) (e:a.Leaves ≃ b.Leaves) :
    Realizes (plain (Γ:=Γ) a b e) (a.partition.changeChart (Γ:=Γ) b.partition e).val := by
  change ∀ (i:a.Leaves) z, _
  intro i z
  change (a.partition.changeChart (Γ:=Γ) b.partition e).val ((a.brick i).attach z)=
    (b.brick (e i)).attach (twist (1:Γ) z)
  rw [twist_one,Equiv.Perm.one_apply]
  exact Partition.changeChart_apply (Γ:=Γ) a.partition b.partition e i z

/-- Prefix-localize an entire diagram, including its bijection and labels. -/
def half (x:X) (A:Diagram Γ X) : Diagram Γ X where
  source := .split x A.source .leaf
  target := .split x A.target .leaf
  wires := Equiv.sumCongr A.wires (Equiv.refl _)
  label := Sum.elim A.label (fun _=>1)

omit [MulAction Γ X] in
lemma value_half (x:X) (A:Diagram Γ X) :
    value d q B R (half x A)=B x*d.tensor (value d q B R A,1)*(B x)⁻¹ := by
  change Tree.leafValue d q B (a:=.split x A.source .leaf) (b:=.split x A.target .leaf)
    (Equiv.sumCongr A.wires (Equiv.refl _))*
    (B x*d.tensor (Tree.fold d B A.source (fun i=>R (A.label i)),R 1)*(B x)⁻¹)=_
  rw [Tree.leafValue_sum,Tree.leafValue_refl,map_one]
  calc
    _=B x*(d.tensor (Tree.leafValue d q B A.wires,1)*
      d.tensor (Tree.fold d B A.source (fun i=>R (A.label i)),1))*(B x)⁻¹ := by group
    _=_ := by rw [← map_mul]; simp only [Prod.mk_mul_mk,mul_one]; rfl

lemma Realizes.half {A:Diagram Γ X} {f:Equiv.Perm (Cube X)} (ha:Realizes A f) (x:X) :
    Realizes (half x A) (localizePerm (Prefix.oneBit x false) f) := by
  change ∀ (i:A.source.Leaves ⊕ (Tree.leaf:Tree X).Leaves) z, _
  rintro (i|i) z
  · change localizePerm (Prefix.oneBit x false) f
      (((Prefix.oneBit x false).comp (A.source.brick i)).attach z)=
        (((Prefix.oneBit x false).comp (A.target.brick (A.wires i))).attach (twist (A.label i) z))
    rw [Prefix.comp_attach,localizePerm_attach,ha,Prefix.comp_attach]
  · change localizePerm (Prefix.oneBit x false) f
      (((Prefix.oneBit x true).comp Prefix.empty).attach z)=
        (((Prefix.oneBit x true).comp Prefix.empty).attach (twist (1:Γ) z))
    rw [Prefix.comp_empty,twist_one,Equiv.Perm.one_apply,localizePerm_outside _ _
      (oneBit_outside x (Ne.symm Bool.false_ne_true) z)]

abbrev rotation (x:X) : Diagram Γ X :=
  plain (.split x .leaf (.split x .leaf .leaf)) (.split x (.split x .leaf .leaf) .leaf)
    (Equiv.sumAssoc _ _ _).symm

omit [MulAction Γ X] in
lemma value_rotation (x:X) (hx:B x=1) : value d q B R (rotation (Γ:=Γ) x)=d.a := by
  rw [value_plain,Tree.leafValue_symm,Tree.leafValue_assoc,hx]
  simp only [show d.tensor (1,1)=1 from d.tensor.map_one,one_mul,mul_one,inv_one,inv_inv]
lemma realizes_rotation (x:X) : Realizes (rotation (Γ:=Γ) x) (Generators.associator (Γ:=Γ) x).val :=
  realizes_plain _ _ _

abbrev exchange (x:X) : Diagram Γ X :=
  plain (.split x .leaf .leaf) (.split x .leaf .leaf) (Equiv.sumComm _ _)
omit [MulAction Γ X] in
lemma value_exchange (x:X) (hx:B x=1) : value d q B R (exchange (Γ:=Γ) x)=q.c := by
  rw [value_plain,Tree.leafValue_exchange,hx,one_mul,inv_one,mul_one]
lemma realizes_exchange (x:X) : Realizes (exchange (Γ:=Γ) x) (Generators.flip (Γ:=Γ) x).val := by
  change ∀ (i:(Tree.leaf:Tree X).Leaves ⊕ (Tree.leaf:Tree X).Leaves) z, _
  rintro (i|i) z
  · change (Generators.flip (Γ:=Γ) x).val
      (((Prefix.oneBit x false).comp Prefix.empty).attach z)=
        (((Prefix.oneBit x true).comp Prefix.empty).attach (twist (1:Γ) z))
    rw [Prefix.comp_empty,Prefix.comp_empty,twist_one,Equiv.Perm.one_apply]
    exact Generators.flip_left x z
  · change (Generators.flip (Γ:=Γ) x).val
      (((Prefix.oneBit x true).comp Prefix.empty).attach z)=
        (((Prefix.oneBit x false).comp Prefix.empty).attach (twist (1:Γ) z))
    rw [Prefix.comp_empty,Prefix.comp_empty,twist_one,Equiv.Perm.one_apply]
    exact (Partition.bit x).permute_attach (Γ:=Γ) Equiv.boolNot true z

end Diagram
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson.Diagram
universe u v w k
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} {H:Type w} {K:Type k}
  [Group Γ] [MulAction Γ X] [Group H] [Group K]
variable (d:Data H) (q:SymmetryData d) (B:X → H) (R:Γ →* H) (x:X)
variable (hR:∀ g x,R g*B x=B (g • x)*d.tensor (R g,R g)) (gl:Tree.GridLaw d q B)
variable (P:K →* H) (E:K →* Equiv.Perm (Cube X))

/-- Elements with a genuine decorated-tree witness for both their algebraic
value and their actual cube action form a subgroup. -/
def represented : Subgroup K where
  carrier k := ∃ A:Diagram Γ X,value d q B R A=P k ∧ Realizes A (E k)
  one_mem' := by
    refine ⟨root 1,?_,?_⟩
    · rw [value_root,map_one,map_one]
    · rw [map_one]; simpa only [twist_one] using realizes_root (X:=X) (1:Γ)
  inv_mem' := by
    rintro a ⟨A,hv,ha⟩
    refine ⟨A.inverse,?_,?_⟩
    · rw [value_inverse d q B R x,hv,map_inv]
    · rw [map_inv]; exact ha.inverse
  mul_mem' := by
    rintro a b ⟨A,hvA,ha⟩ ⟨C,hvC,hc⟩
    obtain ⟨D,hd,hv⟩ := product d q B R x hR gl hc ha
    refine ⟨D,?_,?_⟩
    · rw [hv,hvA,hvC,map_mul]
    · rw [map_mul]; exact hd

lemma mem_represented (a:K) :
    a∈represented d q B R x hR gl P E ↔ ∃ A:Diagram Γ X,value d q B R A=P a ∧ Realizes A (E a) := Iff.rfl

end FiniteAlgebraicEnvelopes.TwistedBrinThompson.Diagram

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
open BinaryGroupCategory
attribute [local instance] Classical.propDecidable
variable {Γ:Type u} {X:Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x:X) [MulAction.IsPretransitive Γ X]
variable (s:Finset (Seed (Γ:=Γ) x)) (t:Finset (MulAction.stabilizer Γ x)) (y₀:X)
variable (hs:Subgroup.closure (s:Set (Seed (Γ:=Γ) x))=⊤)
variable (ht:Subgroup.closure (t:Set (MulAction.stabilizer Γ x))=⊤)
variable (hxy:x≠y₀) (htwo:∀ x₁ x₂ y₁ y₂:X,x₁≠x₂ → y₁≠y₂ → ∃ g:Γ,g • x₁=y₁ ∧ g • x₂=y₂)

local notation "D" => endpointData x s t y₀ hs
local notation "Q" => endpointSymmetryData x s t y₀ hs
local notation "B" => endpointBaker x s t y₀ hs
local notation "R" => endpointRoot x s t y₀
local notation "P" => endpointProject x s t y₀
local notation "E" => MonoidHom.comp (Subgroup.subtype (group (Γ:=Γ) (X:=X))) (evaluation x)

def seedRepresented : Subgroup (Seed (Γ:=Γ) x) :=
  Diagram.represented D Q B R x (endpointBaker_covariance x s t y₀ hs ht)
    (endpointGridLaw x s t y₀ hs ht hxy htwo) P E

lemma root_mem_seedRepresented (g:Γ) : rootWord x g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.root g,?_,?_⟩
  · exact Diagram.value_root D Q B R g
  · exact Diagram.realizes_root g

lemma half_mem_seedRepresented (g:Γ) : halfWord x g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.half x (Diagram.root g),?_,?_⟩
  · change Diagram.value D Q B R (Diagram.half x (Diagram.root g))=P (halfWord x g)
    rw [Diagram.value_half,Diagram.value_root,endpointBaker_base x s t y₀ hs ht]
    simp only [one_mul,inv_one,mul_one]
    change endpointTensor x s t y₀ hs (R g,1)=_
    rw [endpointTensor_apply,map_one,mul_one]
    rfl
  · exact (Diagram.realizes_root g).half x

lemma associator_mem_seedRepresented : associatorWord (Γ:=Γ) x∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.rotation x,?_,?_⟩
  · exact Diagram.value_rotation D Q B R x (endpointBaker_base x s t y₀ hs ht)
  · exact Diagram.realizes_rotation x

lemma flip_mem_seedRepresented : flipWord (Γ:=Γ) x∈seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.exchange x,?_,?_⟩
  · exact Diagram.value_exchange D Q B R x (endpointBaker_base x s t y₀ hs ht)
  · exact Diagram.realizes_exchange x

lemma half_associator_mem_seedRepresented :
    generatorWord x ⟨localize (left x) (associator (Γ:=Γ) x),by simp [finiteSet]⟩∈
      seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.half x (Diagram.rotation x),?_,?_⟩
  · change Diagram.value D Q B R (Diagram.half x (Diagram.rotation x))=P _
    rw [Diagram.value_half,Diagram.value_rotation D Q B R x (endpointBaker_base x s t y₀ hs ht),
      endpointBaker_base x s t y₀ hs ht]
    simp only [one_mul,inv_one,mul_one]
    change endpointTensor x s t y₀ hs (P (associatorWord x),1)=_
    rw [endpointTensor_apply,map_one,mul_one]
    exact (endpoint_halfAssociatorBinding x s t y₀).symm
  · exact (Diagram.realizes_rotation (Γ:=Γ) x).half x

lemma half_flip_mem_seedRepresented :
    generatorWord x ⟨localize (left x) (flip (Γ:=Γ) x),by simp [finiteSet]⟩∈
      seedRepresented x s t y₀ hs ht hxy htwo := by
  refine ⟨Diagram.half x (Diagram.exchange x),?_,?_⟩
  · change Diagram.value D Q B R (Diagram.half x (Diagram.exchange x))=P _
    rw [Diagram.value_half,Diagram.value_exchange D Q B R x (endpointBaker_base x s t y₀ hs ht),
      endpointBaker_base x s t y₀ hs ht]
    simp only [one_mul,inv_one,mul_one]
    change endpointTensor x s t y₀ hs (P (flipWord x),1)=_
    rw [endpointTensor_apply,map_one,mul_one]
    exact (endpoint_halfFlipBinding x s t y₀).symm
  · exact (Diagram.realizes_exchange (Γ:=Γ) x).half x

lemma generator_mem_seedRepresented (g:finiteSet (Γ:=Γ) x) :
    generatorWord x g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  rcases g with ⟨g,hg⟩
  simp only [finiteSet,Finset.mem_insert,Finset.mem_singleton] at hg
  rcases hg with rfl|rfl|rfl|rfl
  · exact associator_mem_seedRepresented x s t y₀ hs ht hxy htwo
  · exact half_associator_mem_seedRepresented x s t y₀ hs ht hxy htwo
  · exact flip_mem_seedRepresented x s t y₀ hs ht hxy htwo
  · exact half_flip_mem_seedRepresented x s t y₀ hs ht hxy htwo

/-- The entire finite presentation seed, not just its selected finite
subgenerators, is represented by genuine decorated diagrams. -/
lemma all_seedRepresented (g:Seed (Γ:=Γ) x) : g∈seedRepresented x s t y₀ hs ht hxy htwo := by
  let S := seedRepresented x s t y₀ hs ht hxy htwo
  change g∈S
  refine Monoid.Coprod.induction_on g ?_ ?_ (fun _ _ ha hb=>S.mul_mem ha hb)
  · intro a
    refine Monoid.Coprod.induction_on a ?_ ?_ ?_
    · intro a; exact root_mem_seedRepresented x s t y₀ hs ht hxy htwo a
    · intro a; exact half_mem_seedRepresented x s t y₀ hs ht hxy htwo a
    · intro a b ha hb; rw [map_mul]; exact S.mul_mem ha hb
  · intro a
    refine FreeGroup.induction_on a ?_ ?_ ?_ ?_
    · rw [map_one]; exact S.one_mem
    · intro a; exact generator_mem_seedRepresented x s t y₀ hs ht hxy htwo a
    · intro a ha; rw [map_inv]; exact S.inv_mem ha
    · intro a b ha hb; rw [map_mul]; exact S.mul_mem ha hb

end Generators
end

universe u v
open BinaryGroupCategory
variable {Γ:Type u} {X:Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x:X) [MulAction.IsPretransitive Γ X]
variable (s:Finset (Seed (Γ:=Γ) x)) (t:Finset (MulAction.stabilizer Γ x)) (y₀:X)
variable (hs:Subgroup.closure (s:Set (Seed (Γ:=Γ) x))=⊤)
variable (ht:Subgroup.closure (t:Set (MulAction.stabilizer Γ x))=⊤)
variable (hxy:x≠y₀) (htwo:∀ x₁ x₂ y₁ y₂:X,x₁≠x₂ → y₁≠y₂ → ∃ g:Γ,g • x₁=y₁ ∧ g • x₂=y₂)

lemma endpointProject_surjective : Function.Surjective (endpointProject (Γ:=Γ) x s t y₀) :=
  QuotientGroup.mk'_surjective _
lemma endpointEvaluation_project (g:Seed (Γ:=Γ) x) :
    endpointEvaluation x s t y₀ hxy (endpointProject x s t y₀ g)=evaluation x g := rfl

include hs ht htwo

/-- Every element of the actual finite endpoint presentation has a finite
coloured decorated tree-pair whose value and semantics agree with it. -/
lemma endpoint_diagram (z:EndpointQuotient (Γ:=Γ) x s t y₀) :
    ∃ A:Diagram Γ X,
      Diagram.value (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs)
        (endpointBaker x s t y₀ hs) (endpointRoot x s t y₀) A=z ∧
      Diagram.Realizes A (endpointEvaluation x s t y₀ hxy z).val := by
  obtain ⟨g,rfl⟩ := endpointProject_surjective x s t y₀ z
  exact all_seedRepresented x s t y₀ hs ht hxy htwo g

/-- Completeness of the explicit finite presentation via whole permutations and
decorated common refinement; semantic injectivity follows from the construction. -/

theorem endpointEvaluation_injective [FaithfulSMul Γ X] :
    Function.Injective (endpointEvaluation x s t y₀ hxy) := by
  apply (injective_iff_map_eq_one _).mpr
  intro z hz
  obtain ⟨A,hv,ha⟩ := endpoint_diagram x s t y₀ hs ht hxy htwo z
  rw [hz] at ha
  have hc := Diagram.value_one_of_realizes_one
    (endpointData x s t y₀ hs) (endpointSymmetryData x s t y₀ hs)
    (endpointBaker x s t y₀ hs) (endpointRoot x s t y₀)
    (endpointGridLaw x s t y₀ hs ht hxy htwo) A ha
  exact hv.symm.trans hc

def endpointEquivalence [FaithfulSMul Γ X] :
    EndpointQuotient (Γ:=Γ) x s t y₀ ≃* group (Γ:=Γ) (X:=X) :=
  MulEquiv.ofBijective (endpointEvaluation x s t y₀ hxy)
    ⟨endpointEvaluation_injective x s t y₀ hs ht hxy htwo,
      endpointEvaluation_surjective x s t y₀ hxy⟩

end Generators
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
