import Mathlib
import OAI.Algebra.GroupRing.SidePins

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternUniform
open scoped Classical Topology BigOperators
open Filter GridAsymptotics GirthAsymptotics TypedGraphs

/-- Numerical conditions shared by every bounded pattern, with the threshold
chosen before its carrier types, lengths, offsets, words or bin profile. -/
def Ready (K M Q J rep : ℕ) : Prop :=
  1 ≤ (L (size rep):ℝ) ∧ 0<size rep ∧
  K*L (size rep)+exclusion (size rep)<StageDenominator.carrier rep ∧
  GridUniform.binRate (L (size rep))≤1/(4800*M:ℝ) ∧
  ∀ d≤J,
    StageUniform.coefficient d K M Q*GridUniform.rate d (L (size rep))+
      M*StageDenominator.error K Q rep/(L (size rep):ℝ) ≤ 1/4800 ∧
    ∀ offset : Fin d → ℤ,3003≤chosenScale d (L (size rep)) offset ∧
      2*(letterError d (L (size rep)) offset:ℝ)<chosenScale d (L (size rep)) offset-1

theorem eventually_ready (K M Q J : ℕ) (hM : 0<M) :
    ∀ᶠ rep in atTop,Ready K M Q J rep := by
  have hL : Tendsto (fun rep => (L (size rep):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (L_tendsto.comp size_tendsto)
  have hb := (GridUniform.binRate_tendsto.comp hL).eventually_lt_const
    (show (0:ℝ)<1/(4800*M:ℝ) by positivity)
  have hd (d : Fin (J+1)) : ∀ᶠ rep in atTop,
      StageUniform.coefficient d.val K M Q*GridUniform.rate d.val (L (size rep))+
        M*StageDenominator.error K Q rep/(L (size rep):ℝ) ≤ 1/4800 ∧
      ∀ offset : Fin d.val → ℤ,3003≤chosenScale d.val (L (size rep)) offset ∧
        2*(letterError d.val (L (size rep)) offset:ℝ)<chosenScale d.val (L (size rep)) offset-1 := by
    have hr := ((GridUniform.rate_tendsto d.val).comp hL).const_mul
      (StageUniform.coefficient d.val K M Q)
    have he := (StageDenominator.error_ratio K Q).const_mul (M:ℝ)
    have ht := hr.add he
    simp only [mul_zero,add_zero] at ht
    have hevent := ht.eventually_lt_const (by norm_num : (0:ℝ)<1/4800)
    filter_upwards [hevent,hL.eventually (GridUniform.eventually_geometry d.val)] with rep hr hg
    refine ⟨?_,hg⟩
    simpa only [Function.comp_def,mul_div_assoc] using hr.le
  filter_upwards [eventually_all.mpr hd,hb,StageDenominator.eventually_room K,
    hL.eventually (eventually_ge_atTop (1:ℝ)),size_tendsto.eventually (eventually_ge_atTop 1)]
    with rep hd hb hr hL hn
  exact ⟨hL,by omega,hr,hb.le,fun d hd' => hd ⟨d,by omega⟩⟩

variable {C E : Type*} [Fintype C] [Fintype E]

theorem Ready.residual {K M Q J rep : ℕ} (h : Ready K M Q J rep)
    (hE : Fintype.card E≤J) (offset : Fin (Fintype.card E) → ℤ)
    (len m : C → ℕ) (hQ : Fintype.card C≤Q)
    (hH : StageMass.totalLength len m≤K*(L (size rep):ℝ))
    (hlo : (L (size rep):ℝ)≤StageMass.totalLength len m) (hpos : ∀ c,1≤ m c) :
    StageMass.residual (E:=E) (chosenScale (Fintype.card E) (L (size rep)) offset) len m
      (letterError (Fintype.card E) (L (size rep)) offset) M Q
      (StageDenominator.error K Q rep)≤StageMass.totalLength len m/4800 := by
  have hh := StageUniform.residual_bound K M Q (L (size rep)) h.1 offset len m hQ hH hpos
    (StageDenominator.error K Q rep)
  have hb := (div_le_iff₀ (show (0:ℝ)<L (size rep) by linarith [h.1])).mp
    (hh.trans (h.2.2.2.2 (Fintype.card E) hE).1)
  linarith

end TorsionFreeZeroDivisors.PatternUniform

namespace TorsionFreeZeroDivisors.ActualPatternEvent
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2

/-- The fixed-pattern event before any scale or bins are chosen. -/
def Realized (cmp : Comparisons (E:=E) (traversalLength len m)) (r : Match rep) : Prop :=
  ∃ label : D → Types.Letter,
    (∀ x,label (Γ.reverse x)=Types.inverse (label x)) ∧
    (∀ x y,Γ.origin x=Γ.origin y → label x=label y → x=y) ∧
    ActualStageLabels.Comparing len m cmp (ActualStageFeasibility.globalWord Γ mark h2 label) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep)
      (sourcePinA Γ mark h2 side paths hp root rep a) Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep)
      (sourcePinB Γ mark h2 side paths hp root rep b) Types.inverse r.2)

omit [Fintype V] in
lemma unbinned_iff (s : ℝ) (cmp : Comparisons (E:=E) (traversalLength len m)) (r : Match rep) :
    Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp r ↔
      Realized Γ mark h2 side hsid paths hp root rep a b cmp r := by
  constructor
  · rintro ⟨d,label,hl,hi,hc,_,ha,hb⟩
    exact ⟨label,hl,hi,hc,ha,hb⟩
  · rintro ⟨label,hl,hi,hc,ha,hb⟩
    exact ⟨_,label,hl,hi,hc,rfl,ha,hb⟩

variable [Fintype E]

def defect (cmp : Comparisons (E:=E) (traversalLength len m)) : ℕ :=
  (Finset.univ.filter (fun x => cmp.pairing.partner x=x)).card

omit [Fintype V] [Fintype E] in
lemma uncovered_eq (s : ℝ) (hs : 0<s)
    (cmp : Comparisons (E:=E) (traversalLength len m)) (err : ℕ) :
    StageMass.uncovered s hs len m cmp err=defect Γ mark h2 paths cmp := by
  unfold StageMass.uncovered defect OccurrenceMatching.Data.unpairedPositions
  apply congrArg Finset.card
  exact Finset.filter_congr_decidable _ _ _

/-- Uniform probability bound with no entropy, moment or scale hypothesis.
The ready threshold is independent of all carrier types and pattern data. -/
theorem uniform_probability_bound (K Q M J : ℕ) (hM : 0<M)
    (hready : PatternUniform.Ready K M Q J rep)
    (cmp : Comparisons (E:=E) (traversalLength len m))
    (hm : ∀ c,m c≤M) (hpositive : ∀ c,1≤ m c)
    (hc : ∀ i, List.IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse) (paths i))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hreduced : ∀ x e,cmp.side x=some e →
      (x.1.1,x.2.val)≠((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (hQ : Fintype.card R≤Q) (hE : Fintype.card E≤J)
    (hH : StageMass.totalLength len m ≤ K*(L (size rep):ℝ))
    (hlo : (L (size rep):ℝ)≤StageMass.totalLength len m)
    (hb : (defect Γ mark h2 paths cmp:ℝ)≤
      StageFusion.epsilon (1/600) 256*StageMass.totalLength len m) :
    (((samples rep).filter (Realized Γ mark h2 side hsid paths hp root rep a b cmp)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  let eqv := Fintype.equivFin E
  let off : Fin (Fintype.card E) → ℤ := fun i => cmp.offset (eqv.symm i)
  let s := chosenScale (Fintype.card E) (L (size rep)) off
  let err := letterError (Fintype.card E) (L (size rep)) off
  have hs : 0<s := chosenScale_pos _ hready.1 off
  obtain ⟨hl,he⟩ := (hready.2.2.2.2 (Fintype.card E) hE).2 off
  obtain ⟨ν,hν⟩ := uniform_alignment (Fintype.card E) hready.1 off
  have hν' (e : E) : 2*|(cmp.offset e:ℝ)-(ν (eqv e):ℝ)*s|+4≤err := by
    simpa only [off,Equiv.symm_apply_apply] using hν (eqv e)
  have hh (i : Underlying s len) := BinProfiles.height_bounds s hs.le len i
  have hlarge (i : Underlying s len) : 3002≤height s len i := by
    have h : (3002:ℝ)≤height s len i := by linarith [hh i]
    exact_mod_cast h
  have hres := hready.residual hE off len m hQ hH hlo hpositive
  have hu := unbinned_probability_bound Γ mark h2 side hsid paths hp root rep a b s hs hl cmp
    err K Q M hM hm hc hclose hlarge (fun i => by linarith [hh i])
    (fun i => by linarith [hh i]) hreduced hready.2.1 hready.2.2.1 hQ hH
    (fun e => ν (eqv e)) he hν' (by simpa only [uncovered_eq] using hb) hres hpositive
    ((GridUniform.bin_bound (Fintype.card E) hready.1 off).trans hready.2.2.2.1)
  have heq : (samples rep).filter (Realized Γ mark h2 side hsid paths hp root rep a b cmp)=
      (samples rep).filter (Unbinned Γ mark h2 side hsid paths hp root rep a b s cmp) := by
    ext r
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => (unbinned_iff Γ mark h2 side hsid paths hp root rep a b s cmp r).symm)
  rw [heq]
  apply hu.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hlo) (by positivity)

end TorsionFreeZeroDivisors.ActualPatternEvent

namespace TorsionFreeZeroDivisors.OriginalPattern
open scoped Classical BigOperators
open PortSubdivision ChainSuppression DegreeTwoSuppression SuppressedMoore ChainPaths ChainIsomorphism
open ChainChunkTransport ChunkComparisons FiniteChunking StageSubgraphs StageSideEmbedding
open ComparedBlocks RepeatedBlocks GridAsymptotics GirthAsymptotics TypedGraphs ActualPatternEvent
variable {V D P E : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (mark : V → Prop) (h2 : ∀ v,¬mark v → (out Γ.origin v).card=2)
    (side : V → Bool) (hsid : ∀ x,side (Γ.origin (Γ.reverse x))=side (Γ.origin x))
    (paths : P → List {x : D // turn Γ.origin mark h2 x=x}) (hp : ∀ p,paths p≠[])
    (root : Option P) (rep : ℕ) (a : Types.VertexA rep) (b : Types.VertexB rep)
local notation "R" => Rep Γ mark h2
local notation "m" => ChunkComparisons.multiplicity (color Γ mark h2 paths)
local notation "len" => repLength Γ mark h2
local notation "pl" => pathLength (chunks Γ mark h2 paths) (chunkLength Γ mark h2 paths)

/-- Literal whole-path comparisons, before cutting at the marked vertices. -/
def Realized (patCmp : Comparisons (E:=E) pl) (r : Match rep) : Prop :=
  ∃ label : D → Types.Letter,
    (∀ x,label (Γ.reverse x)=Types.inverse (label x)) ∧
    (∀ x y,Γ.origin x=Γ.origin y → label x=label y → x=y) ∧
    (∀ x e,patCmp.side x=some e → label (originalDart Γ mark h2 paths x)=
      if patCmp.reverse e then Types.inverse (label (originalDart Γ mark h2 paths (patCmp.pairing.partner x)))
      else label (originalDart Γ mark h2 paths (patCmp.pairing.partner x))) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid true)
      (fun x => label x.val) (@Types.outgoingA rep)
      (sourcePinA Γ mark h2 side paths hp root rep a) Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph Γ side hsid false)
      (fun x => label x.val) (@Types.outgoingB rep)
      (sourcePinB Γ mark h2 side paths hp root rep b) Types.inverse r.2)

/-- The actual cut comparison data, with its carrier exposed once. -/
def cut (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) : Comparisons (E:=E × RepeatedBlocks.Traversal m × RepeatedBlocks.Traversal m)
    (RepeatedBlocks.traversalLength len m) :=
  (repeatedChunks Γ mark h2 paths).comparisons patCmp lo hi hlo hhi

omit [Fintype V] in
lemma normalized (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) {r : Match rep}
    (h : Realized Γ mark h2 side hsid paths hp root rep a b patCmp r) :
    ActualPatternEvent.Realized Γ mark h2 side hsid paths hp root rep a b
      (cut Γ mark h2 paths patCmp lo hi hlo hhi) r := by
  rcases h with ⟨label,hl,hn,hc,ha,hb⟩
  exact ⟨label,hl,hn,ActualStageFeasibility.comparing Γ mark h2 paths patCmp lo hi hlo hhi label hl hc,ha,hb⟩

omit [Fintype V] in
lemma totalLength_eq : StageMass.totalLength len m =
    ∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ) := by
  have he := Fintype.card_congr (repeatedChunks Γ mark h2 paths).equiv
  rw [position_card,position_card] at he
  change (∑ t : RepeatedBlocks.Traversal m,(len t.1:ℝ))=_
  have hh : (∑ t : RepeatedBlocks.Traversal m,len t.1)=∑ p,pl p := he
  exact_mod_cast hh.trans (Finset.sum_congr rfl (fun p _ => pathLength_eq Γ mark h2 paths p))

omit [Fintype V] in
lemma defect_eq (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) :
    ActualPatternEvent.defect Γ mark h2 paths
      (cut Γ mark h2 paths patCmp lo hi hlo hhi) =
    (Finset.univ.filter (fun x => patCmp.pairing.partner x=x)).card := by
  unfold ActualPatternEvent.defect
  rw [←Fintype.card_subtype,←Fintype.card_subtype]
  exact Fintype.card_congr ((repeatedChunks Γ mark h2 paths).unpairedEquiv patCmp)

variable [Fintype E]

/-- The fixed original-path event has the source exponential bound; cuts and
orientations are deterministic and do not add any probability factor. -/
theorem probability_bound (patCmp : Comparisons (E:=E) pl) (lo hi : E → ℤ)
    (hlo : ∀ e,patCmp.lo e=(lo e:ℝ)) (hhi : ∀ e,patCmp.hi e=(hi e:ℝ)) (K Q M J : ℕ) (hM : 0<M)
    (hready : PatternUniform.Ready K M Q J rep)
    (hm : ∀ c,m c≤M) (hpositive : ∀ c,1≤ m c)
    (hc : ∀ i, List.IsChain (WeightedMoore.PortWalk.step
      (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse) (paths i))
    (hclose : ∀ i,StageRoot.cyclic root i=true →
      ∀ᵉ (x∈(paths i).getLast?) (y∈(paths i).head?),
      WeightedMoore.PortWalk.step (suppressed Γ mark h2).origin (suppressed Γ mark h2).reverse x y)
    (hreduced : ∀ x e,patCmp.side x=some e →
      originalDart Γ mark h2 paths x≠originalDart Γ mark h2 paths (patCmp.pairing.partner x) ∧
      originalDart Γ mark h2 paths x≠Γ.reverse (originalDart Γ mark h2 paths (patCmp.pairing.partner x)))
    (hQ : Fintype.card R≤Q)
    (hE : Fintype.card E*(Fintype.card (RepeatedBlocks.Traversal m))^2≤J)
    (hH : (∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ)) ≤ K*(L (size rep):ℝ))
    (hlength : (L (size rep):ℝ)≤∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ))
    (hb : ((Finset.univ.filter (fun x => patCmp.pairing.partner x=x)).card:ℝ)≤
      StageFusion.epsilon (1/600) 256*∑ p, (((paths p).flatMap (word Γ mark h2)).length:ℝ)) :
    (((samples rep).filter (Realized Γ mark h2 side hsid paths hp root rep a b patCmp)).card:ℝ)/
      (samples rep).card ≤ Real.exp (-(L (size rep):ℝ)/(4800*M)) := by
  have he : Fintype.card (E × RepeatedBlocks.Traversal m × RepeatedBlocks.Traversal m)≤J := by
    simpa only [Fintype.card_prod,pow_two,mul_assoc] using hE
  have h := ActualPatternEvent.uniform_probability_bound Γ mark h2 side hsid paths hp root rep a b
    K Q M J hM hready (cut Γ mark h2 paths patCmp lo hi hlo hhi)
    hm hpositive hc hclose (normalized_reduced Γ mark h2 paths patCmp lo hi hlo hhi hreduced) hQ he
    (by rwa [totalLength_eq]) (by rwa [totalLength_eq])
    (by simpa only [defect_eq,totalLength_eq] using hb)
  apply le_trans (b:=(((samples rep).filter (ActualPatternEvent.Realized Γ mark h2 side hsid paths hp root rep a b
      (cut Γ mark h2 paths patCmp lo hi hlo hhi))).card:ℝ)/(samples rep).card) _ h
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro r hr
  obtain ⟨hs,he⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hs,normalized Γ mark h2 side hsid paths hp root rep a b patCmp lo hi hlo hhi he⟩

end TorsionFreeZeroDivisors.OriginalPattern

namespace TorsionFreeZeroDivisors.ComparisonGeometry
open scoped Classical
open BlockAlignment ComparedBlocks ChunkComparisons
variable {P P' E E' : Type*} {len : P → ℕ} {len' : P' → ℕ}

def position (e : P ≃ P') (hl : ∀ p,len p=len' (e p)) : Position len ≃ Position len' :=
  Equiv.sigmaCongr e (fun p => Equiv.subtypeEquivRight (fun q => by rw [hl p]))

structure Iso (C : Comparisons (E:=E) len) (C' : Comparisons (E:=E') len') where
  path : P ≃ P'
  comparison : E ≃ E'
  length_eq : ∀ p,len p=len' (path p)
  flip_eq : ∀ j,comparison (C.flip j)=C'.flip (comparison j)
  source_eq : ∀ j,path (C.source j)=C'.source (comparison j)
  lo_eq : ∀ j,C.lo j=C'.lo (comparison j)
  hi_eq : ∀ j,C.hi j=C'.hi (comparison j)
  reverse_eq : ∀ j,C.reverse j=C'.reverse (comparison j)
  offset_eq : ∀ j,C.offset j=C'.offset (comparison j)

namespace Iso
variable {C : Comparisons (E:=E) len} {C' : Comparisons (E:=E') len'} (f : Iso C C')

lemma side_some (x : Position len) (j : E) :
    C'.side ((position f.path f.length_eq) x)=some (f.comparison j) ↔ C.side x=some j := by
  rw [C'.side_iff,C.side_iff]
  change (f.path x.1=C'.source (f.comparison j) ∧ x.2.val∈positions (C'.lo (f.comparison j)) (C'.hi (f.comparison j))) ↔ _
  rw [←f.source_eq,←f.lo_eq,←f.hi_eq,f.path.injective.eq_iff]

lemma side_eq (x : Position len) :
    C'.side ((position f.path f.length_eq) x)=(C.side x).map f.comparison := by
  cases h : C.side x with
  | some j => simpa only [Option.map_some] using (f.side_some x j).mpr h
  | none =>
    simp only [Option.map_none]
    cases h' : C'.side ((position f.path f.length_eq) x) with
    | none => rfl
    | some j =>
      have hh := (f.side_some x (f.comparison.symm j)).mp (by simpa only [Equiv.apply_symm_apply] using h')
      rw [h] at hh
      contradiction

lemma partner_eq (x : Position len) :
    position f.path f.length_eq (C.pairing.partner x)=
      C'.pairing.partner (position f.path f.length_eq x) := by
  cases h : C.side x with
  | none =>
    have h' : C'.side (position f.path f.length_eq x)=none := by rw [f.side_eq,h]; rfl
    rw [(C.none_iff x).mp h,(C'.none_iff _).mp h']
  | some j =>
    have h' := (f.side_some x j).mpr h
    apply position_ext
    · change f.path (C.pairing.partner x).1=_
      rw [C.partner_source _ _ h,C'.partner_source _ _ h',←f.flip_eq,f.source_eq]
    · change (C.pairing.partner x).2.val=_
      rw [C.partner_coordinate _ _ h,C'.partner_coordinate _ _ h',f.reverse_eq,f.offset_eq]
      rfl

end Iso
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.PortSubdivision
structure Iso {V D V' D' : Type*} (Γ : PortGraph V D) (Γ' : PortGraph V' D') where
  vertex : V ≃ V'
  dart : D ≃ D'
  origin_eq : ∀ d,vertex (Γ.origin d)=Γ'.origin (dart d)
  reverse_eq : ∀ d,dart (Γ.reverse d)=Γ'.reverse (dart d)

namespace Iso
variable {V D V' D' V'' D'' : Type*} {Γ : PortGraph V D} {Γ' : PortGraph V' D'} {Γ'' : PortGraph V'' D''}
def symm (f : Iso Γ Γ') : Iso Γ' Γ where
  vertex := f.vertex.symm
  dart := f.dart.symm
  origin_eq d := by
    apply f.vertex.injective
    simp only [Equiv.apply_symm_apply,f.origin_eq]
  reverse_eq d := by
    apply f.dart.injective
    simp only [Equiv.apply_symm_apply,f.reverse_eq]

def trans (f : Iso Γ Γ') (g : Iso Γ' Γ'') : Iso Γ Γ'' where
  vertex := f.vertex.trans g.vertex
  dart := f.dart.trans g.dart
  origin_eq d := by simp only [Equiv.trans_apply,f.origin_eq,g.origin_eq]
  reverse_eq d := by simp only [Equiv.trans_apply,f.reverse_eq,g.reverse_eq]
end Iso
end TorsionFreeZeroDivisors.PortSubdivision

end

end OAI
