import Mathlib
import OAI.Algebra.GroupRing.PartitionEntropy

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical BigOperators
variable {V TA TB : Type*} [Fintype V] (side : V → Bool)

/-- The optional first-stage root split by prescribed side. -/
def root (r : Option V) (b : Bool) : Option {v : V // side v=b} :=
  r.bind fun v => if h : side v=b then some ⟨v,h⟩ else none

omit [Fintype V] in
lemma root_none (b : Bool) : root side none b=none := rfl
omit [Fintype V] in
lemma root_some (v : V) : root side (some v) (side v)=some ⟨v,rfl⟩ := by
  simp [root]

omit [Fintype V] in
lemma root_save (r : Option V) :
    (if (root side r true).isSome then (1:ℤ) else 0) +
      (if (root side r false).isSome then (1:ℤ) else 0) = if r.isSome then 1 else 0 := by
  cases r with
  | none => rfl
  | some v => cases hs : side v <;> simp [root,hs]

lemma free_total (r : Option V) (a : TA) (b : TB) :
    (RootPins.free (root side r true) a : ℤ) + (RootPins.free (root side r false) b : ℤ) =
      Fintype.card V - if r.isSome then 1 else 0 := by
  rw [RootPins.free_cast,RootPins.free_cast]
  have hc := StageSideEmbedding.vertex_card side
  change Fintype.card {v : V // side v=true}+Fintype.card {v : V // side v=false}=Fintype.card V at hc
  have hc' := congrArg (fun n : ℕ => (n:ℤ)) hc
  simp only [Nat.cast_add] at hc'
  have hr := root_save side r
  omega

omit [Fintype V] in
lemma respects {r : Option V} {a : TA} (b : Bool) (f : V → TA)
    (h : ∀ v,r=some v → f v=a) :
    ∀ v y,RootPins.pin (root side r b) a v=some y → f v.val=y := by
  apply RootPins.respects
  intro v hv
  cases r with
  | none => cases hv
  | some w =>
    dsimp only [root,Option.bind_some] at hv
    split_ifs at hv with hw
    · have hval : w=v.val := congrArg Subtype.val (Option.some.inj hv)
      exact h v.val (by rw [←hval])

end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking StageSubgraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "mult" => ListStageExponents.mult (S) paths
local notation "R" => ChainIsomorphism.Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)

/-- The possible interval is designated once, not independently at each stage. -/
def cyclic (root : Option P) (p : P) : Bool := decide (root≠some p)

omit [Fintype V] [Fintype D] in
lemma intervals_card (root : Option P) :
    (Fintype.card {p : P // cyclic root p=false}:ℤ) = if root.isSome then 1 else 0 := by
  cases root with
  | none => simp [cyclic]
  | some p => simp [cyclic]

/-- Only the first stage fixes the marked initial vertex. -/
def vertex (root : Option P) (j : ℕ) : Option (ActiveV (S) mult j) :=
  if h : j=0 then by
    subst j
    exact root.map (ActiveRoot.vertex (S) paths hp)
  else none

omit [Fintype V] in
lemma vertex_isSome (root : Option P) (j : ℕ) :
    (vertex Γ mark h2 paths hp root j).isSome = if j=0 then root.isSome else false := by
  unfold vertex
  split_ifs with hj
  · subst j
    simp
  · rfl

/-- The root split over the two prescribed sides has exactly the source saving. -/
def power (side : ∀ j, ActiveV (S) mult j → Bool) (root : Option P)
    {TA TB : Type} (a : TA) (b : TB) (j : ℕ) : ℤ :=
  (RootPins.free (SidePins.root (side j) (vertex Γ mark h2 paths hp root j) true) a : ℤ)+
  (RootPins.free (SidePins.root (side j) (vertex Γ mark h2 paths hp root j) false) b : ℤ)-
    Fintype.card (ChainActiveStages.ActiveChain Γ mark h2 paths j)

lemma power_eq (side : ∀ j, ActiveV (S) mult j → Bool) (root : Option P)
    {TA TB : Type} (a : TA) (b : TB) (j : ℕ) :
    power Γ mark h2 paths hp side root a b j =
      (Fintype.card (ActiveV (S) mult j):ℤ)-Fintype.card (ChainActiveStages.ActiveChain Γ mark h2 paths j)-
        if j=0 then (Fintype.card {p : P // cyclic root p=false}:ℤ) else 0 := by
  unfold power
  rw [SidePins.free_total,vertex_isSome]
  by_cases hj : j=0
  · simp only [hj,ite_true,intervals_card]
    ring
  · simp [hj]

theorem power_nonpos (side : ∀ j, ActiveV (S) mult j → Bool) (root : Option P)
    {TA TB : Type} (a : TA) (b : TB)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step (S).origin (S).reverse))
    (hclose : ∀ i,cyclic root i=true → ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (S).origin (S).reverse x y)
    (M : ℕ) (hM : 0<M) (hm : ∀ c : R,m c≤M) :
    (∑ j : Fin M, (power Γ mark h2 paths hp side root a b j.val : ℝ)) ≤ 0 := by
  have hz := ChainActiveStages.exponent_nonpos Γ mark h2 paths hp (cyclic root) hc hclose M hM hm
  have he : (∑ j : Fin M,power Γ mark h2 paths hp side root a b j.val) ≤ 0 := by
    simpa [power_eq,ListStageExponents.mult] using hz
  exact_mod_cast he

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
variable {V T : Type*}
lemma pin_some_iff (root : Option V) (target : T) (v : V) (y : T) :
    pin root target v=some y ↔ root=some v ∧ target=y := by
  unfold pin
  split_ifs with h <;> simp [h]
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SidePins
open scoped Classical
variable {V : Type*} (side : V → Bool)
lemma root_eq_some (r : Option V) (b : Bool) (v : {v : V // side v=b}) :
    root side r b=some v ↔ r=some v.val := by
  cases r with
  | none => simp [root]
  | some w =>
    dsimp only [root,Option.bind_some]
    split_ifs with hw
    · simp only [Option.some.injEq]
      exact Subtype.ext_iff
    · simp only [false_iff,Option.some.injEq]
      intro h
      subst w
      exact hw v.property
end TorsionFreeZeroDivisors.SidePins

namespace TorsionFreeZeroDivisors.StageRoot
open scoped Classical
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChainMultiplicity ChunkComparisons FiniteChunking StageSubgraphs
variable {V D P : Type} [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
local notation "S" => suppressed Γ mark h2
local notation "mult" => ListStageExponents.mult (S) paths

/-- The actual marked initial vertex of the designated interval, if any. -/
def source (r : Option P) : Option V := r.map fun p => (S).origin ((paths p).head (hp p))

lemma vertex_source (r : Option P) (j : ℕ) (v : ActiveV (S) mult j)
    (h : vertex Γ mark h2 paths hp r j=some v) : source Γ mark h2 paths hp r=some v.val := by
  unfold vertex at h
  split_ifs at h with hj
  subst j
  rcases Option.map_eq_some_iff.mp h with ⟨p,hp',hv⟩
  subst r
  dsimp only [source,Option.map_some]
  have hval := congrArg Subtype.val hv
  rw [ActiveRoot.vertex_val] at hval
  exact congrArg some hval

variable (side : V → Bool)
lemma pin_compatible (r : Option P) {T : Type} (target : T) (b : Bool) (j : ℕ)
    (v : {v : ActiveV (S) mult j // ChainSide.vertex Γ mark h2 side paths j v=b}) (y : T)
    (h : RootPins.pin
      (SidePins.root (ChainSide.vertex Γ mark h2 side paths j) (vertex Γ mark h2 paths hp r j) b)
      target v=some y) :
    RootPins.pin (SidePins.root side (source Γ mark h2 paths hp r) b) target
      ⟨v.val.val,v.property⟩=some y := by
  rw [RootPins.pin_some_iff] at h ⊢
  refine ⟨?_,h.2⟩
  rw [SidePins.root_eq_some] at h
  rw [SidePins.root_eq_some]
  exact vertex_source Γ mark h2 paths hp r j v.val h.1

end TorsionFreeZeroDivisors.StageRoot

namespace TorsionFreeZeroDivisors.ActualStagePair
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d))
    (paths : P → List {d : D // turn Γ.origin mark h2 d=d}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "cs" => ChainSide.chain Γ mark h2 side
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "first" => ChainActiveStages.first Γ mark h2 paths
local notation "last" => ChainActiveStages.last Γ mark h2 paths
local notation "hf" => ChainSide.active_first Γ mark h2 side paths
local notation "hl" => ChainSide.active_last Γ mark h2 side hsid paths

abbrev pinA (j : ℕ) := RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) true) a
abbrev pinB (j : ℕ) := RootPins.pin (SidePins.root (vs j) (StageRoot.vertex Γ mark h2 paths hp root j) false) b

abbrev A (j : ℕ) : TwoSideStage.Side :=
  StagePartition.sideA len m cs j
    (firstPoint m j cs (vs j) (first j) (hf j) true)
    (lastPoint m j cs (vs j) (last j) (hl j) true)
    (@Types.outgoingA rep) (pinA Γ mark h2 side paths hp root rep a j)

abbrev B (j : ℕ) : TwoSideStage.Side :=
  StagePartition.sideB len m cs j
    (firstPoint m j cs (vs j) (first j) (hf j) false)
    (lastPoint m j cs (vs j) (last j) (hl j) false)
    (@Types.outgoingB rep) (pinB Γ mark h2 side paths hp root rep b j)
local notation "SA" => A Γ mark h2 side hsid paths hp root rep a
local notation "SB" => B Γ mark h2 side hsid paths hp root rep b

lemma power_eq (j : ℕ) :
    (((SA j).freeMarks+(SB j).freeMarks:ℕ):ℝ)-
      (Fintype.card (SA j).C+Fintype.card (SB j).C:ℕ) =
        (StageRoot.power Γ mark h2 paths hp vs root a b j:ℝ) := by
  have hc := StageSideEmbedding.chain_card m j cs
  unfold StageRoot.power
  dsimp only [TwoSideStage.Side.freeMarks,A,B,StagePartition.sideA,StagePartition.sideB]
  rw [Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_natCast,Int.cast_natCast,
    Nat.cast_add,←hc]
  rfl

lemma edges_eq (j : ℕ) : (SA j).edges+(SB j).edges =
    ∑ c : {c : R // j < m c},len c.val := by
  change (∑ c : {c : R // j < m c ∧ cs c=true},len c.val)+
    (∑ c : {c : R // j < m c ∧ cs c=false},len c.val)=_
  rw [← Finset.sum_subtype (Finset.univ.filter fun c => j < m c ∧ cs c=true) (by simp),
    ← Finset.sum_subtype (Finset.univ.filter fun c => j < m c ∧ cs c=false) (by simp),
    ← Finset.sum_subtype (Finset.univ.filter fun c => j < m c) (by simp)]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  cases cs c <;> simp

lemma edges_bound (j : ℕ) : ((SA j).edges+(SB j).edges:ℝ) ≤ StageMass.totalLength len m := by
  rw [← Nat.cast_add,edges_eq,StageMass.totalLength_eq]
  rw [← Finset.sum_subtype (Finset.univ.filter fun c => j < m c) (by simp)]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with hc
  · have h : (1:ℝ) ≤ m c := by exact_mod_cast (show 1 ≤ m c by omega)
    nlinarith [show (0:ℝ) ≤ len c from Nat.cast_nonneg (len c)]
  · positivity

variable {E : Type}

def count (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (j : ℕ) : (SA j).Match × (SB j).Match → ℕ :=
  TwoSideStage.count (SA j) (SB j) (ChainStageLabels.fullWords s len m j cmp d)
    (StagePartition.restrictA len m cs j) (StagePartition.restrictB len m cs j)

/-- Restricting actual embeddings on the two prescribed sides witnesses the
joint stage count, with a SINGLE global label projection. -/
theorem count_pos (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (j : ℕ) (label : D → Types.Letter)
    (hlabel : ∀ x,label (Γ.reverse x)=Types.inverse (label x))
    (pinA' : SideRestriction.Vertex side true → Option (Types.VertexA rep))
    (pinB' : SideRestriction.Vertex side false → Option (Types.VertexB rep))
    (r : (SA j).Match × (SB j).Match)
    (eA : RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep) pinA' Types.inverse r.1)
    (eB : RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep) pinB' Types.inverse r.2)
    (hpa : ∀ v y,pinA Γ mark h2 side paths hp root rep a j v=some y → pinA' ⟨v.val.val,v.property⟩=some y)
    (hpb : ∀ v y,pinB Γ mark h2 side paths hp root rep b j v=some y → pinB' ⟨v.val.val,v.property⟩=some y)
    (hw : ActualStageRealization.word Γ mark h2 paths j label ∈ ChainStageLabels.fullWords s len m j cmp d) :
    0<count Γ mark h2 side hsid paths hp root rep a b s cmp d j r := by
  exact TwoSideStage.count_pos (SA j) (SB j) _ _ _ r _ hw
    (ActualSideRealization.embedding Γ mark h2 side hsid paths j true label _ pinA' r.1 eA hlabel _ hpa)
    (ActualSideRealization.embedding Γ mark h2 side hsid paths j false label _ pinB' r.2 eB hlabel _ hpb)

/-- The actual rooted, mixed-side stage first moment, with its exact signed
vertex exponent and the source's common denominator loss. -/
theorem mean_bound (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (hs : 0<s) (j err K Q : ℕ)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep)
    (hr : K*GirthAsymptotics.L (TypedGraphs.size rep)+GirthAsymptotics.exclusion (TypedGraphs.size rep)<
      StageDenominator.carrier rep)
    (hQ : Fintype.card R≤Q)
    (hH : StageMass.totalLength len m ≤ K*(GirthAsymptotics.L (TypedGraphs.size rep):ℝ)) :
    TwoSideMean.mean (((SA j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))) ×ˢ
      ((SB j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep))))
      (count Γ mark h2 side hsid paths hp root rep a b s cmp d j) ≤
    Real.exp ((StageRoot.power Γ mark h2 paths hp vs root a b j:ℝ)*Real.log (TypedGraphs.size rep)+
      StageEntropy.labelCost s hs len m cmp err d j+StageEntropy.looseCost s len err+
        StageDenominator.error K Q rep) := by
  have hE : (SA j).edges+(SB j).edges ≤ K*GirthAsymptotics.L (TypedGraphs.size rep) := by
    exact_mod_cast (edges_bound Γ mark h2 side hsid paths hp root rep a b j).trans hH
  have hA := StageDenominator.conditionsA K rep hr (SA j).len (SA j).first (SA j).last (SA j).pin
    ((Nat.le_add_right _ _).trans hE)
  have hB := StageDenominator.conditionsB K rep hr (SB j).len (SB j).first (SB j).last (SB j).pin
    ((Nat.le_add_left _ _).trans hE)
  have hq : Fintype.card (StagePartition.CA m cs j)+Fintype.card (StagePartition.CB m cs j)≤Q := by
    rw [StageSideEmbedding.chain_card]
    apply le_trans _ hQ
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have h := PartitionEntropy.mean_bound s hs len m cs j
    (SA j).first (SA j).last (SB j).first (SB j).last
    (@Types.outgoingA rep) (@Types.outgoingB rep) (SA j).pin (SB j).pin cmp d err K Q rep
    hlarge hscale hreduced hn (Nat.sub_pos_of_lt hr) hA hB
    (fun c => chainLength_pos Γ mark h2 c.val) hq hE
  change TwoSideMean.mean _ (count Γ mark h2 side hsid paths hp root rep a b s cmp d j) ≤
    Real.exp (((((SA j).freeMarks+(SB j).freeMarks:ℕ):ℝ)-
      (Fintype.card (SA j).C+Fintype.card (SB j).C:ℕ))*Real.log (TypedGraphs.size rep)+
      StageEntropy.labelCost s hs len m cmp err d j+StageEntropy.looseCost s len err+
        StageDenominator.error K Q rep) at h
  rw [power_eq] at h
  exact h

end TorsionFreeZeroDivisors.ActualStagePair

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _
private lemma mem_profiles_iff {C : Type*} [Fintype C] (s : ℝ) (len : C → ℕ)
    (d : Underlying s len → ℤ) :
    d∈BinProfiles.profiles s len ↔ ∀ i,d i∈BinProfiles.values s := by
  unfold BinProfiles.profiles
  exact Fintype.mem_piFinset

variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "vs" => ChainSide.vertex Γ mark h2 side paths
local notation "SA" => ActualStagePair.A Γ mark h2 side hsid paths hp root rep a
local notation "SB" => ActualStagePair.B Γ mark h2 side hsid paths hp root rep b

abbrev Match (rep : ℕ) :=
  ConditionedMatchings.Matching (PatternEmbeddings.label (@Types.outgoingA rep)) Types.inverse ×
  ConditionedMatchings.Matching (PatternEmbeddings.label (@Types.outgoingB rep)) Types.inverse

def samples (rep : ℕ) : Finset (Match rep) :=
  ConditionedMatchings.Matching.conditioned (label:=PatternEmbeddings.label (@Types.outgoingA rep))
    (bar:=Types.inverse) (PatternEmbeddings.origin (@Types.outgoingA rep))
    (3*GirthAsymptotics.L (TypedGraphs.size rep)) ∅ ×ˢ
  ConditionedMatchings.Matching.conditioned (label:=PatternEmbeddings.label (@Types.outgoingB rep))
    (bar:=Types.inverse) (PatternEmbeddings.origin (@Types.outgoingB rep))
    (3*GirthAsymptotics.L (TypedGraphs.size rep)) ∅

lemma samples_eq (j : ℕ) : samples rep =
    (SA j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep)) ×ˢ
      (SB j).samples (3*GirthAsymptotics.L (TypedGraphs.size rep)) := by
  ext r
  dsimp only [ActualStagePair.A,ActualStagePair.B,StagePartition.sideA,StagePartition.sideB,
    TwoSideStage.Side.samples]
  simp only [samples,ConditionedMatchings.Matching.conditioned,
    Finset.mem_product,Finset.mem_filter,Finset.mem_univ,true_and]
  erw [Finset.mem_product]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

abbrev sourcePinA := RootPins.pin
  (SidePins.root side (StageRoot.source Γ mark h2 paths hp root) true) a
abbrev sourcePinB := RootPins.pin
  (SidePins.root side (StageRoot.source Γ mark h2 paths hp root) false) b

/-- Literal realization of an enlarged fixed pattern and its bin profile.
The prescribed-side embeddings are into the actual two independent matchings.
The comparisons refer to normalized traversals of the same suppressed graph. -/
def Occurs (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match rep) : Prop :=
  ∃ label : D → Types.Letter,
    (∀ x,label (Γ.reverse x)=Types.inverse (label x)) ∧
    (∀ x y,Γ.origin x=Γ.origin y → label x=label y → x=y) ∧
    ActualStageLabels.Comparing len m cmp (ActualStageFeasibility.globalWord Γ mark h2 label) ∧
    ActualStageFeasibility.bins s len (ActualStageFeasibility.globalWord Γ mark h2 label)=d ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep)
      (sourcePinA Γ mark h2 side paths hp root rep a) Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep)
      (sourcePinB Γ mark h2 side paths hp root rep b) Types.inverse r.2)

/-- Existence of the actual pattern witnesses every stage count. This does
not posit simultaneous independence of the chain-multiplicity stages. -/
theorem count_pos (s : ℝ) (hs : 0<s) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match rep)
    (hr : Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r) (j : ℕ) :
    0<ActualStagePair.count Γ mark h2 side hsid paths hp root rep a b s cmp d j r := by
  rcases hr with ⟨label,hl,hi,hc,hd,⟨eA⟩,⟨eB⟩⟩
  apply ActualStagePair.count_pos Γ mark h2 side hsid paths hp root rep a b s cmp d j label hl
    _ _ r eA eB
    (StageRoot.pin_compatible Γ mark h2 paths hp side root a true j)
    (StageRoot.pin_compatible Γ mark h2 paths hp side root b false j)
  have hw := ActualStageFeasibility.fullWords_of_comparing s len m cmp j
    (ActualStageFeasibility.globalWord Γ mark h2 label) hc
    (ActualStageFeasibility.immersed s Γ mark h2 hs label hl hi)
  rw [hd] at hw
  exact hw

omit [Fintype V] in
/-- A realizable bin profile automatically has the universal lower and upper
weight bounds; those numerical bounds are not extra assumptions on an event. -/
theorem bin_bounds (s : ℝ) (hs : 0<s) (cmp : Comparisons (E:=E) (traversalLength len m))
    (d : Underlying s len → ℤ) (r : Match rep)
    (hr : Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hscale' : ∀ i,(height s len i:ℝ)≤2*s) :
    (∀ i,(1/600:ℝ)*s/2≤d i) ∧ (∀ i,(d i:ℝ)≤256*s) := by
  rcases hr with ⟨label,hl,hi,_hc,hd,_⟩
  have hb := ActualStageFeasibility.mem_bin s len (ActualStageFeasibility.globalWord Γ mark h2 label)
    (ActualStageFeasibility.immersed s Γ mark h2 hs label hl hi)
  rw [hd] at hb
  have h i := WordEstimate.bin_full_bounds (height s len i) (hlarge i) s (hscale i) (hscale' i)
    (d i) _ (hb i)
  exact ⟨fun i => (h i).1,fun i => (h i).2.1⟩

/-- The unbinned event quantifies no artificial stage data: the bin witness is
forced by the literal label words. -/
def Unbinned (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m))
    (r : Match rep) : Prop :=
  ∃ d,Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r

omit [Fintype V] in
lemma occurs_profile (s : ℝ) (hs : 3003≤ s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (d : Underlying s len → ℤ)
    (r : Match rep) (hr : Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r) :
    d∈BinProfiles.profiles s len := by
  classical
  have hh (i : Underlying s len) := BinProfiles.height_bounds s (by linarith) len i
  have hl (i : Underlying s len) : 3002≤height s len i := by
    have h : (3002:ℝ)≤height s len i := by linarith [hh i]
    exact_mod_cast h
  obtain ⟨hlo,hhi⟩ := bin_bounds Γ mark h2 side hsid paths hp root rep a b s (by linarith)
    cmp d r hr hl (fun i => by linarith [hh i]) (fun i => by linarith [hh i])
  apply (mem_profiles_iff s len d).mpr
  intro i
  exact Finset.mem_Icc.mpr ⟨by
    have h : (0:ℝ)≤d i := (by positivity : (0:ℝ)≤(1/600:ℝ)*s/2).trans (hlo i)
    exact_mod_cast h,Int.le_floor.mpr (hhi i)⟩

omit [Fintype V] in
lemma unbinned_iff_profile (s : ℝ) (hs : 3003≤ s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (r : Match rep) :
    Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp r ↔
      ∃ d : {d // d∈BinProfiles.profiles s len},
        Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d.val r := by
  constructor
  · rintro ⟨d,hd⟩
    exact ⟨⟨d,occurs_profile Γ mark h2 side hsid paths hp root rep a b s hs cmp d r hd⟩,hd⟩
  · rintro ⟨d,hd⟩
    exact ⟨d.val,hd⟩

variable [Fintype E]

/-- One genuinely realized fixed-bin pattern is exponentially unlikely.
All numerical stage bounds are derived from its two literal matching means;
no independence between multiplicity stages is asserted. -/
theorem probability_bound (s : ℝ) (hs : 0<s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (d : Underlying s len → ℤ)
    (err K Q M : ℕ) (hM : 0<M) (hm : ∀ c,m c≤M)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hscale' : ∀ i,(height s len i:ℝ)≤2*s)
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep)
    (hr : K*GirthAsymptotics.L (TypedGraphs.size rep)+GirthAsymptotics.exclusion (TypedGraphs.size rep)<
      StageDenominator.carrier rep)
    (hQ : Fintype.card R≤Q)
    (hH : StageMass.totalLength len m ≤ K*(GirthAsymptotics.L (TypedGraphs.size rep):ℝ))
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (hb : (StageMass.uncovered s hs len m cmp err:ℝ) ≤
      StageFusion.epsilon (1/600) 256*StageMass.totalLength len m)
    (he : StageMass.residual (E:=E) s len m err M Q (StageDenominator.error K Q rep) ≤
      StageMass.totalLength len m/4800) :
    (((samples rep).filter (Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-StageMass.totalLength len m/(2400*M)) := by
  by_cases hex : ∃ r,Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d r
  · rcases hex with ⟨r,hr'⟩
    obtain ⟨hlow,hhigh⟩ := bin_bounds Γ mark h2 side hsid paths hp root rep a b s hs cmp d
      r hr' hlarge hscale hscale'
    have hpw := StageRoot.power_nonpos Γ mark h2 paths hp vs root a b hc hclose M hM hm
    have hlgn : 0≤Real.log (TypedGraphs.size rep) :=
      Real.log_nonneg (by exact_mod_cast (show 1≤TypedGraphs.size rep by omega))
    have hprod := StageMass.decay s hs len m cmp err M Q hm hQ ν hsmall herr d hlow hhigh
      (Real.log (TypedGraphs.size rep)) (StageDenominator.error K Q rep) hlgn
      (fun j : Fin M => (StageRoot.power Γ mark h2 paths hp vs root a b j.val:ℝ)) hpw hb he
    have h := StageFusion.one_pattern (samples rep) M hM
      (Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d)
      (fun j : Fin M => ActualStagePair.count Γ mark h2 side hsid paths hp root rep a b s cmp d j.val)
      (fun j : Fin M => (StageRoot.power Γ mark h2 paths hp vs root a b j.val:ℝ)*
        Real.log (TypedGraphs.size rep)+StageEntropy.labelCost s hs len m cmp err d j.val+
          (StageEntropy.looseCost s len err+StageDenominator.error K Q rep))
      (StageMass.totalLength len m/2400)
      (fun j r _hr hr' => count_pos Γ mark h2 side hsid paths hp root rep a b s hs cmp d r hr' j.val)
      (fun j => by
        have hmom := ActualStagePair.mean_bound Γ mark h2 side hsid paths hp root rep a b
          s cmp d hs j err K Q hlarge hscale hreduced hn hr hQ hH
        rw [← samples_eq Γ mark h2 side hsid paths hp root rep a b j] at hmom
        convert hmom using 1
        · unfold TwoSideMean.mean
          congr 1
        · congr 1; ring)
      (by simpa only [neg_div] using hprod)
    convert h using 1
    congr 1
    ring
  · have hf : (samples rep).filter (Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d)=∅ := by
      ext r
      simp only [Finset.mem_filter,Finset.notMem_empty,iff_false,not_and]
      exact fun _ => fun hr' => hex ⟨r,hr'⟩
    rw [hf,Finset.card_empty,Nat.cast_zero,zero_div]
    exact (Real.exp_pos _).le

/-- Union over all canonical weight bins of an actual pattern. -/
theorem unbinned_probability_bound (s : ℝ) (hs : 0<s) (hslarge : 3003≤ s)
    (cmp : Comparisons (E:=E) (traversalLength len m))
    (err K Q M : ℕ) (hM : 0<M) (hm : ∀ c,m c≤M)
    (hc : ∀ i,(paths i).IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hlarge : ∀ i,3002≤height s len i)
    (hscale : ∀ i,s+1200≤2*(height s len i:ℝ))
    (hscale' : ∀ i,(height s len i:ℝ)≤2*s)
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hn : 0<TypedGraphs.size rep)
    (hr : K*GirthAsymptotics.L (TypedGraphs.size rep)+GirthAsymptotics.exclusion (TypedGraphs.size rep)<
      StageDenominator.carrier rep)
    (hQ : Fintype.card R≤Q)
    (hH : StageMass.totalLength len m ≤ K*(GirthAsymptotics.L (TypedGraphs.size rep):ℝ))
    (ν : E → ℤ) (hsmall : 2*(err:ℝ)<s-1)
    (herr : ∀ e,2*|(cmp.offset e:ℝ)-(ν e:ℝ)*s|+4≤err)
    (hb : (StageMass.uncovered s hs len m cmp err:ℝ) ≤
      StageFusion.epsilon (1/600) 256*StageMass.totalLength len m)
    (he : StageMass.residual (E:=E) s len m err M Q (StageDenominator.error K Q rep) ≤
      StageMass.totalLength len m/4800)
    (hpositive : ∀ c,1≤ m c)
    (hbins : Real.log (256*s+1)/s≤1/(4800*M:ℝ)) :
    (((samples rep).filter (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-StageMass.totalLength len m/(4800*M)) := by
  let H := StageMass.totalLength len m
  have hH0 : 0≤H := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hsum : (∑ c : R,(len c:ℝ))≤H := by
    unfold H
    rw [StageMass.totalLength_eq]
    apply Finset.sum_le_sum
    intro c _
    have hp : (1:ℝ)≤ m c := by exact_mod_cast hpositive c
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (len c): (0:ℝ)≤len c)
  have hcard : ((BinProfiles.profiles s len).card:ℝ)≤Real.exp (H/(4800*M)) := by
    apply (BinProfiles.cardinal_bound s hs len).trans
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (H/s)*Real.log (256*s+1) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hsum hs.le) (Real.log_nonneg (by linarith))
      _ = H*(Real.log (256*s+1)/s) := by ring
      _ ≤ H*(1/(4800*M)) := mul_le_mul_of_nonneg_left hbins hH0
      _ = H/(4800*M) := by ring
  let Profiles := {d // d∈BinProfiles.profiles s len}
  have hB (d : Profiles) := probability_bound Γ mark h2 side hsid paths hp root rep a b
    s hs cmp d.val err K Q M hM hm hc hclose hlarge hscale hscale' hreduced hn hr hQ hH
    ν hsmall herr hb he
  have hu : (((samples rep).filter
      (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp)).card:ℝ)/(samples rep).card ≤
        ((BinProfiles.profiles s len).card:ℝ)*Real.exp (-H/(2400*M)) := by
    by_cases hsamp : (samples rep).Nonempty
    · have h := StageFusion.pattern_union (samples rep) hsamp
        (fun d : Profiles => Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d.val)
        (Real.exp (-H/(2400*M))) hB
      have heq : (samples rep).filter (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp)=
          (samples rep).filter (fun r => ∃ d : Profiles,
            Occurs Γ mark h2 side hsid paths hp root rep a b s cmp d.val r) := by
        ext r
        simp only [Finset.mem_filter]
        exact and_congr_right (fun _ => unbinned_iff_profile Γ mark h2 side hsid paths hp root rep a b
          s hslarge cmp r)
      rw [heq]
      convert h using 1
      congr 1
      exact_mod_cast (Fintype.card_coe (BinProfiles.profiles s len)).symm
    · have heq := Finset.not_nonempty_iff_eq_empty.mp hsamp
      rw [heq,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,zero_div]
      positivity
  calc
    _ ≤ ((BinProfiles.profiles s len).card:ℝ)*Real.exp (-H/(2400*M)) := hu
    _ ≤ Real.exp (H/(4800*M))*Real.exp (-H/(2400*M)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (-H/(4800*M)) := by rw [←Real.exp_add]; congr 1; ring

end TorsionFreeZeroDivisors.ActualPatternEvent

end

end OAI
