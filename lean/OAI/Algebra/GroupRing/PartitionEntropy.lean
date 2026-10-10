import Mathlib
import OAI.Algebra.GroupRing.RealizationTransport

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PartitionEntropy
open scoped Classical BigOperators
open StageEntropy BlockAlignment ComparedBlocks RepeatedBlocks ChainStageLabels WordEstimate StagePartition
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C E VA VB TA TB : Type} [Fintype C] [Fintype VA] [Fintype VB]
  [Fintype TA] [Fintype TB]
variable (s : ℝ) (hs : 0<s) (len m : C → ℕ) (side : C → Bool) (j : ℕ)
variable (firstA lastA : CA m side j → VA) (firstB lastB : CB m side j → VB)
  (outA : TA → Finset Types.Letter) (outB : TB → Finset Types.Letter)
  (pinA : VA → Option TA) (pinB : VB → Option TB)
local notation "SA" => sideA len m side j firstA lastA outA pinA
local notation "SB" => sideB len m side j firstB lastB outB pinB

/-- A complete literal-stage first moment, with its signed vertex exponent
and the source denominator, without stage independence. -/
theorem mean_bound (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (err K Q rep : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep) (hr : 0<StageDenominator.denominator K rep)
    (hA : TwoSideStage.Conditions SA (TypedGraphs.size rep) (129/16513)
      (3*GirthAsymptotics.L (TypedGraphs.size rep)) 132 (StageDenominator.denominator K rep))
    (hB : TwoSideStage.Conditions SB (TypedGraphs.size rep) (129/16513)
      (3*GirthAsymptotics.L (TypedGraphs.size rep)) 132 (StageDenominator.denominator K rep))
    (hlen : ∀ c,0<len c) (hQ : Fintype.card (CA m side j)+Fintype.card (CB m side j)≤Q)
    (hE : (SA).edges+(SB).edges ≤ K*GirthAsymptotics.L (TypedGraphs.size rep)) :
    TwoSideMean.mean (((SA).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))) ×ˢ
      ((SB).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))))
      (TwoSideStage.count SA SB (fullWords s len m j cmp d)
        (restrictA len m side j) (restrictB len m side j)) ≤
      Real.exp (((((SA).freeMarks+(SB).freeMarks:ℕ):ℝ)-
        (Fintype.card (CA m side j)+Fintype.card (CB m side j):ℕ))*Real.log (TypedGraphs.size rep) +
          labelCost s hs len m cmp err d j + looseCost s len err + StageDenominator.error K Q rep) := by
  have hm := StagePartition.mean_bound s hs len m side j firstA lastA firstB lastB
    outA outB pinA pinB cmp d err hlarge hscale hreduced
    (TypedGraphs.size rep) (129/16513) _ 132 _ hA hB
  have hc := StageDenominator.joint_cost_bound SA SB K Q rep hn hr
    (fun c => hlen c.val) (fun c => hlen c.val) hQ hE
  apply hm.trans
  apply (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq
  rw [← Real.exp_add]
  congr 1
  unfold labelCost looseCost
  change (((((SA).freeMarks+(SB).freeMarks:ℕ):ℝ)-
    (Fintype.card (CA m side j)+Fintype.card (CB m side j):ℕ))*Real.log (TypedGraphs.size rep)+
      StageDenominator.error K Q rep) + _ = _
  ring

end TorsionFreeZeroDivisors.PartitionEntropy

namespace TorsionFreeZeroDivisors.SideRestriction
open scoped Classical
open PortSubdivision
variable {V D : Type*} (Γ : PortGraph V D) (side : V → Bool)
    (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)

abbrev Vertex := {v : V // side v=b}
abbrev Dart := {d : D // side (Γ.origin d)=b}
def graph : PortGraph (Vertex side b) (Dart Γ side b) where
  origin d := ⟨Γ.origin d.val,d.property⟩
  reverse d := ⟨Γ.reverse d.val,(hs d.val).trans d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d.val)
  reverse_ne d h := Γ.reverse_ne d.val (congrArg Subtype.val h)

variable {QV QD : Type*} (Q : PortGraph QV QD) (fv : QV ↪ V) (fd : QD ↪ D)
    (ho : ∀ d,fv (Q.origin d)=Γ.origin (fd d))
    (hr : ∀ d,fd (Q.reverse d)=Γ.reverse (fd d))
    (hf : ∀ v,side (fv v)=b)

def vertex : QV ↪ Vertex side b := ⟨fun v => ⟨fv v,hf v⟩,fun _ _ h => fv.injective (congrArg Subtype.val h)⟩
def dart : QD ↪ Dart Γ side b :=
  ⟨fun d => ⟨fd d,by rw [←ho]; exact hf _⟩,fun _ _ h => fd.injective (congrArg Subtype.val h)⟩

lemma origin_map (d : QD) : vertex side b fv hf (Q.origin d) =
    (graph Γ side hs b).origin (dart Γ side b Q fv fd ho hf d) := by
  exact Subtype.ext (ho d)
include hr in
lemma reverse_map (d : QD) : dart Γ side b Q fv fd ho hf (Q.reverse d) =
    (graph Γ side hs b).reverse (dart Γ side b Q fv fd ho hf d) := by
  exact Subtype.ext (hr d)

variable [Fintype V] [Fintype D] [Fintype QV] [Fintype QD]
    {TV T : Type*} [Fintype TV] [Fintype T]
    (label : D → T) (outgoing : TV → Finset T) (pin : Vertex side b → Option TV)
    (bar : T → T) (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)

/-- Restrict a realized prescribed side to an injectively immersed subgraph
whose target vertices really lie on that side. -/
def embedding (e : RealizationTransport.Embedding (graph Γ side hs b) (fun d => label d.val)
    outgoing pin bar r) (pin' : QV → Option TV)
    (hp : ∀ v y,pin' v=some y → pin (vertex side b fv hf v)=some y) :
    RealizationTransport.Embedding Q (label ∘ fd) outgoing pin' bar r :=
  RealizationTransport.restrict e Q (vertex side b fv hf) (dart Γ side b Q fv fd ho hf)
    (origin_map Γ side hs b Q fv fd ho hf) (reverse_map Γ side hs b Q fv fd ho hr hf) pin' hp

end TorsionFreeZeroDivisors.SideRestriction

namespace TorsionFreeZeroDivisors.StageSideEmbedding
open scoped Classical BigOperators
open ChainSubdivision
variable {C V : Type*} (len m : C → ℕ) (j : ℕ) (side : C → Bool) (vside : V → Bool)
    (first last : {c // j < m c} → V)
    (hf : ∀ c,vside (first c)=side c.val) (hl : ∀ c,vside (last c)=side c.val) (b : Bool)

abbrev Chain := {c : C // j < m c ∧ side c=b}
abbrev Vertex := {v : V // vside v=b}
abbrev length : Chain m j side b → ℕ := fun c => len c.val

def firstPoint (c : Chain m j side b) : Vertex vside b :=
  ⟨first ⟨c.val,c.property.1⟩,(hf _).trans c.property.2⟩
def lastPoint (c : Chain m j side b) : Vertex vside b :=
  ⟨last ⟨c.val,c.property.1⟩,(hl _).trans c.property.2⟩
abbrev graph := ChainSubdivision.graph (length len m j side b)
  (firstPoint m j side vside first hf b) (lastPoint m j side vside last hl b)
local notation "Q" => graph len m j side vside first last hf hl b
local notation "P" => ChainSubdivision.graph (StageExpectation.activeLen len m j) first last

def vertex : ChainSubdivision.Vertex (length len m j side b) (V := Vertex vside b) →
    ChainSubdivision.Vertex (StageExpectation.activeLen len m j) (V := V)
  | .inl v => .inl v.val
  | .inr ⟨c,i⟩ => .inr ⟨⟨c.val,c.property.1⟩,i⟩
def dart : ChainSubdivision.Dart (length len m j side b) →
    ChainSubdivision.Dart (StageExpectation.activeLen len m j) :=
  fun d => (⟨⟨d.1.1.val,d.1.1.property.1⟩,d.1.2⟩,d.2)

lemma vertex_injective : Function.Injective (vertex len m j side vside b) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    | inr w => cases h
  | inr v =>
    cases w with
    | inl w => cases h
    | inr w =>
      rcases v with ⟨c,i⟩
      rcases w with ⟨d,k⟩
      have h' := Sum.inr.inj h
      have hcd : c=d := Subtype.ext (congrArg (fun x => x.1.val) h')
      cases hcd
      have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
      cases hik
      rfl

lemma dart_injective : Function.Injective (dart len m j side b) := by
  rintro ⟨⟨c,i⟩,r⟩ ⟨⟨d,k⟩,s⟩ h
  have hrs := congrArg Prod.snd h
  cases hrs
  have h' := congrArg Prod.fst h
  have hcd : c=d := Subtype.ext (congrArg (fun x => x.1.val) h')
  cases hcd
  have hik : i=k := eq_of_heq (Sigma.mk.inj_iff.mp h').2
  cases hik
  rfl

lemma point_map (c : Chain m j side b) (k : Fin (length len m j side b c+1)) :
    vertex len m j side vside b
      (point (length len m j side b) (firstPoint m j side vside first hf b)
        (lastPoint m j side vside last hl b) c k) =
    point (StageExpectation.activeLen len m j) first last ⟨c.val,c.property.1⟩ k := by
  unfold point
  split_ifs <;> rfl

lemma origin_map (d : ChainSubdivision.Dart (length len m j side b)) :
    vertex len m j side vside b ((Q).origin d) = (P).origin (dart len m j side b d) := by
  rcases d with ⟨⟨c,i⟩,r⟩
  cases r
  · simpa only [dart,origin_forward] using
      point_map len m j side vside first last hf hl b c ⟨i.val,by have h:=i.isLt; omega⟩
  · simpa only [dart,origin_backward] using
      point_map len m j side vside first last hf hl b c ⟨i.val+1,by have h:=i.isLt; omega⟩

lemma reverse_map (d : ChainSubdivision.Dart (length len m j side b)) :
    dart len m j side b ((Q).reverse d) = (P).reverse (dart len m j side b d) := rfl

/-- Restriction of a full stage string to this prescribed side. -/
def restrictWord (F : ComparedBlocks.Position (StageExpectation.activeLen len m j) → WordEstimate.Letter) :
    ComparedBlocks.Position (length len m j side b) → WordEstimate.Letter :=
  fun x => F ⟨⟨x.1.val,x.1.property.1⟩,x.2⟩

lemma label_map (F : ComparedBlocks.Position (StageExpectation.activeLen len m j) → WordEstimate.Letter)
    (d : ChainSubdivision.Dart (length len m j side b)) :
    ChainRealization.label (length len m j side b)
      (StageExpectation.readWord (length len m j side b) (restrictWord len m j side b F)) d =
    ChainRealization.label (StageExpectation.activeLen len m j)
      (StageExpectation.readWord (StageExpectation.activeLen len m j) F) (dart len m j side b d) := by
  rcases d with ⟨⟨c,i⟩,r⟩
  cases r <;> rfl

variable [Fintype C] [Fintype V]

/-- Exact partitions; no isolated vertices from inactive stages are introduced. -/
lemma chain_card : Fintype.card (Chain m j side true)+Fintype.card (Chain m j side false)=
    Fintype.card {c // j < m c} := by
  let f : Chain m j side true ⊕ Chain m j side false → {c // j < m c} :=
    Sum.elim (fun c => ⟨c.val,c.property.1⟩) (fun c => ⟨c.val,c.property.1⟩)
  have h : Function.Bijective f := by
    constructor
    · intro x y hxy
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : {c // j < m c} => z.val) hxy))
        | inr y =>
          have hv : x.val=y.val := congrArg Subtype.val hxy
          have ht := x.property.2
          rw [hv,y.property.2] at ht
          cases ht
      | inr x =>
        cases y with
        | inl y =>
          have hv : x.val=y.val := congrArg Subtype.val hxy
          have ht := x.property.2
          rw [hv,y.property.2] at ht
          cases ht
        | inr y => exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : {c // j < m c} => z.val) hxy))
    · rintro ⟨c,hc⟩
      cases hh : side c with
      | true => exact ⟨.inl ⟨c,hc,hh⟩,rfl⟩
      | false => exact ⟨.inr ⟨c,hc,hh⟩,rfl⟩
  simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.ofBijective f h)

lemma vertex_card : Fintype.card (Vertex vside true)+Fintype.card (Vertex vside false)=Fintype.card V := by
  have h := Fintype.card_subtype_compl (fun v : V => vside v=true)
  have he : {v : V // ¬vside v=true} ≃ Vertex vside false :=
    Equiv.subtypeEquivRight (fun v => by cases vside v <;> simp)
  rw [Fintype.card_congr he] at h
  have heq : Fintype.card {v : V // vside v=true}≤Fintype.card V := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  change Fintype.card {v : V // vside v=true}+_= _
  omega

end TorsionFreeZeroDivisors.StageSideEmbedding

namespace TorsionFreeZeroDivisors.ChainSide
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
local notation "F" => next Γ.reverse (turn Γ.origin mark h2)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2

def chain (c : R) : Bool := side (Γ.origin c.val.val)

include hs in
lemma next_side (d : D) : side (Γ.origin (F d))=side (Γ.origin d) := by
  change side (Γ.origin (turn Γ.origin mark h2 (Γ.reverse d)))=side (Γ.origin d)
  rw [turn_origin Γ.origin mark h2]
  exact hs d

include hs in
lemma iterate_side (d : D) (i : ℕ) : side (Γ.origin (F^[i] d))=side (Γ.origin d) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply',next_side Γ mark h2 side hs,ih]

include hs in
lemma suppressed_side (d : {d : D // turn Γ.origin mark h2 d=d}) :
    side ((S).origin ((S).reverse d))=side ((S).origin d) := by
  change side (Γ.origin ((S).reverse d).val)=side (Γ.origin d.val)
  have he := chain_last Γ mark h2 d
  rw [last_iterChain] at he
  rw [←he,hs]
  exact iterate_side Γ mark h2 side hs d.val _

lemma first_side (c : R) : side (ChainIsomorphism.first Γ mark h2 c).val=chain Γ mark h2 side c := rfl
include hs in
lemma last_side (c : R) : side (ChainIsomorphism.last Γ mark h2 c).val=chain Γ mark h2 side c :=
  suppressed_side Γ mark h2 side hs c.val

variable {P : Type*} [Fintype P]
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ)
local notation "W" => StageSubgraphs.ActiveV (S) (ListStageExponents.mult (S) paths) j
local notation "A" => ChainActiveStages.ActiveChain Γ mark h2 paths j

def vertex (w : W) : Bool := side w.val

lemma active_first (c : A) : vertex Γ mark h2 side paths j (ChainActiveStages.first Γ mark h2 paths j c)=
    chain Γ mark h2 side c.val := rfl
include hs in
lemma active_last (c : A) : vertex Γ mark h2 side paths j (ChainActiveStages.last Γ mark h2 paths j c)=
    chain Γ mark h2 side c.val := last_side Γ mark h2 side hs c.val

include hs in
lemma stage_internal (c : A) (i : Fin (ChainStageEmbedding.length Γ mark h2 paths j c-1)) :
    side (ChainStageEmbedding.vertexMap Γ mark h2 paths j (.inr ⟨c,i⟩))=chain Γ mark h2 side c.val := by
  exact iterate_side Γ mark h2 side hs c.val.val.val (i.val+1)

end TorsionFreeZeroDivisors.ChainSide

namespace TorsionFreeZeroDivisors.ActualSideRealization
open scoped Classical
open Function PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons StageSubgraphs
variable {V D : Type} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    {P : Type} [Fintype P] (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (j : ℕ) (b : Bool)
local notation "S" => suppressed Γ mark h2
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths j
local notation "first" => ChainActiveStages.first Γ mark h2 paths j
local notation "last" => ChainActiveStages.last Γ mark h2 paths j
local notation "hf" => ChainSide.active_first Γ mark h2 side paths j
local notation "hl" => ChainSide.active_last Γ mark h2 side hs paths j
local notation "W" => ActiveV (S) (ListStageExponents.mult (S) paths) j

abbrev length := StageSideEmbedding.length len m j cs b
abbrev Marked := StageSideEmbedding.Vertex vs b
abbrev graph := StageSideEmbedding.graph len m j cs vs first last hf hl b
local notation "Q" => graph Γ mark h2 side hs paths j b
local notation "l" => length Γ mark h2 side paths j b

def vertexMap : ChainSubdivision.Vertex l (V := Marked Γ mark h2 side paths j b) → V :=
  ChainStageEmbedding.vertexMap Γ mark h2 paths j ∘ StageSideEmbedding.vertex len m j cs vs b

def dartMap : ChainSubdivision.Dart l → D :=
  ChainStageEmbedding.dartMap Γ mark h2 paths j ∘ StageSideEmbedding.dart len m j cs b

lemma vertex_injective : Injective (vertexMap Γ mark h2 side paths j b) :=
  (ChainStageEmbedding.vertexMap_injective Γ mark h2 paths j).comp
    (StageSideEmbedding.vertex_injective len m j cs vs b)
lemma dart_injective : Injective (dartMap Γ mark h2 side paths j b) :=
  (ChainStageEmbedding.dartMap_injective Γ mark h2 paths j).comp
    (StageSideEmbedding.dart_injective len m j cs b)

lemma origin_map (d : ChainSubdivision.Dart l) :
    vertexMap Γ mark h2 side paths j b ((Q).origin d)=Γ.origin (dartMap Γ mark h2 side paths j b d) := by
  unfold vertexMap dartMap
  dsimp only [Function.comp_apply]
  rw [StageSideEmbedding.origin_map len m j cs vs first last hf hl b]
  exact ChainStageEmbedding.origin_map Γ mark h2 paths j _

lemma reverse_map (d : ChainSubdivision.Dart l) :
    dartMap Γ mark h2 side paths j b ((Q).reverse d)=Γ.reverse (dartMap Γ mark h2 side paths j b d) := by
  unfold dartMap
  dsimp only [Function.comp_apply]
  rw [StageSideEmbedding.reverse_map len m j cs vs first last hf hl b]
  exact ChainStageEmbedding.reverse_map Γ mark h2 paths j _

include hs in
lemma vertex_side (v : ChainSubdivision.Vertex l (V := Marked Γ mark h2 side paths j b)) :
    side (vertexMap Γ mark h2 side paths j b v)=b := by
  cases v with
  | inl v => exact v.property
  | inr v =>
    rcases v with ⟨c,i⟩
    exact (ChainSide.stage_internal Γ mark h2 side hs paths j ⟨c.val,c.property.1⟩ i).trans c.property.2

def word (label : D → Types.Letter) : ComparedBlocks.Position l → WordEstimate.Letter :=
  StageSideEmbedding.restrictWord len m j cs b (ActualStageRealization.word Γ mark h2 paths j label)

lemma label_eq (label : D → Types.Letter) (hlabel : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (d : ChainSubdivision.Dart l) :
    ChainRealization.label l (StageExpectation.readWord l (word Γ mark h2 side paths j b label)) d =
      label (dartMap Γ mark h2 side paths j b d) := by
  rw [show word Γ mark h2 side paths j b label = StageSideEmbedding.restrictWord len m j cs b
    (ActualStageRealization.word Γ mark h2 paths j label) from rfl,
    StageSideEmbedding.label_map]
  exact ActualStageRealization.label_eq Γ mark h2 paths j label hlabel _

variable [Fintype V] {TV : Type} [Fintype TV]
    (label : D → Types.Letter) (outgoing : TV → Finset Types.Letter)
    (pin : SideRestriction.Vertex side b → Option TV)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse)

/-- The literal realization of this prescribed-side active stage follows from
an actual embedding of the original prescribed side. All labels stay the
restrictions of ONE global word. -/
def embedding (e : RealizationTransport.Embedding (SideRestriction.graph Γ side hs b)
      (fun d => label d.val) outgoing pin Types.inverse r)
    (hlabel : ∀ d,label (Γ.reverse d)=Types.inverse (label d))
    (pin' : Marked Γ mark h2 side paths j b → Option TV)
    (hp : ∀ v y,pin' v=some y → pin ⟨v.val.val,v.property⟩=some y) :
    RealizationTransport.Embedding (Q)
      (ChainRealization.label l (StageExpectation.readWord l (word Γ mark h2 side paths j b label)))
      outgoing (ChainRealization.pin l pin') Types.inverse r := by
  let fv : ChainSubdivision.Vertex l ↪ V :=
    ⟨vertexMap Γ mark h2 side paths j b,vertex_injective Γ mark h2 side paths j b⟩
  let fd : ChainSubdivision.Dart l ↪ D :=
    ⟨dartMap Γ mark h2 side paths j b,dart_injective Γ mark h2 side paths j b⟩
  have hp' : ∀ v y, ChainRealization.pin l pin' v=some y →
      pin (SideRestriction.vertex side b fv (vertex_side Γ mark h2 side hs paths j b) v)=some y := by
    intro v y hy
    cases v with
    | inl v => exact hp v y hy
    | inr v => cases hy
  exact RealizationTransport.congrLabel
    (SideRestriction.embedding Γ side hs b (Q) fv fd
      (origin_map Γ mark h2 side hs paths j b) (reverse_map Γ mark h2 side hs paths j b)
      (vertex_side Γ mark h2 side hs paths j b) label outgoing pin Types.inverse r e _ hp') _
    (label_eq Γ mark h2 side paths j b label hlabel)

end TorsionFreeZeroDivisors.ActualSideRealization

end

end OAI
