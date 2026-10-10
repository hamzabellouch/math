import Mathlib
import OAI.Algebra.GroupRing.ChainUsage

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.RawDecomposition
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs
variable {V D P : Type} [Fintype V] [Fintype D] [Fintype P]
    (Γ : PortGraph V D) (raw : P → List D) (hp : ∀ p,raw p≠[])
    (hc : ∀ p,(raw p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse))

abbrev marks := ActualComplexity.endpoints Γ raw hp
abbrev mark := MarkedChainBound.marks Γ (marks Γ raw hp)
abbrev degree_two := marks_degree_two Γ (marks Γ raw hp)
abbrev Seeds := SourcePattern.Seeds Γ (marks Γ raw hp)

include hc in
omit [Fintype V] in
lemma decomposition (p : P) : ∃ ds : List (Seeds Γ raw hp),
    ds.flatMap (word Γ (mark Γ raw hp) (degree_two Γ raw hp))=raw p := by
  obtain ⟨ds,hd,_⟩ := ChainPathTransport.decomposes Γ (mark Γ raw hp) (degree_two Γ raw hp)
    (raw p) (hc p) (fun d hd => Or.inr (start_mem Γ raw hp p hd))
    (fun d hd => Or.inr (finish_mem Γ raw hp p hd))
  exact ⟨ds,hd⟩

def paths (p : P) : List (Seeds Γ raw hp) := (decomposition Γ raw hp hc p).choose
omit [Fintype V] in
lemma expands (p : P) : (paths Γ raw hp hc p).flatMap (word Γ (mark Γ raw hp) (degree_two Γ raw hp))=raw p :=
  (decomposition Γ raw hp hc p).choose_spec
omit [Fintype V] in
lemma nonempty (p : P) : paths Γ raw hp hc p≠[] := by
  intro he
  have hx := expands Γ raw hp hc p
  rw [he,List.flatMap_nil] at hx
  exact hp p hx.symm

abbrev lengths := pathLength (chunks Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc))
  (chunkLength Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc))
omit [Fintype V] in
lemma length_eq (p : P) : lengths Γ raw hp hc p=(raw p).length := by
  rw [lengths,pathLength_eq,expands]
omit [Fintype V] in
lemma lengths_eq : lengths Γ raw hp hc=(fun p => (raw p).length) := funext (length_eq Γ raw hp hc)

/-- Positions remember their literal original dart, without a choice of orientation. -/
def dart (x : Position (fun p => (raw p).length)) : D := (raw x.1).get ⟨x.2.val.toNat,by
  have hx := x.2.property
  have hz : 0≤x.2.val ∧ x.2.val<(raw x.1).length := by
    simpa only [AffineIntervals.nat_positions,Finset.mem_Ico] using hx
  omega⟩
omit [Fintype D] [Fintype P] in
lemma dart_get (x : Position (fun p => (raw p).length)) :
    (raw x.1)[x.2.val.toNat]?=some (dart raw x) := List.getElem?_eq_getElem _

def position : Position (lengths Γ raw hp hc) ≃ Position (fun p => (raw p).length) :=
  ComparisonGeometry.position (Equiv.refl P) (length_eq Γ raw hp hc)
omit [Fintype V] in
lemma dart_eq (x : Position (lengths Γ raw hp hc)) :
    originalDart Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc) x=
      dart raw (position Γ raw hp hc x) := by
  apply Option.some.inj
  rw [←originalDart_get,expands,←dart_get]
  rfl

omit [Fintype V] in
lemma source_eq (root : Option P) :
    StageRoot.source Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc)
      (nonempty Γ raw hp hc) root = root.map (fun p => Γ.origin ((raw p).head (hp p))) := by
  cases root with
  | none => rfl
  | some p =>
    change some (Γ.origin ((paths Γ raw hp hc p).head (nonempty Γ raw hp hc p)).val)=_
    have he := ChainPathTransport.flatMap_head Γ (mark Γ raw hp) (degree_two Γ raw hp) (paths Γ raw hp hc p)
    rw [expands,List.head?_eq_some_head (hp p),
      List.head?_eq_some_head (nonempty Γ raw hp hc p),Option.map_some] at he
    exact congrArg (fun d => some (Γ.origin d)) (Option.some.inj he).symm

end TorsionFreeZeroDivisors.RawDecomposition

namespace TorsionFreeZeroDivisors.ComparisonGeometry

section
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}

def cast (h : l=l') (c : Comparisons (E:=E) l) : Comparisons (E:=E) l' := h ▸ c
def castIso (h : l=l') (c : Comparisons (E:=E) l) : Iso c (cast h c) := by
  subst l'
  exact ⟨Equiv.refl P,Equiv.refl E,fun _ => rfl,fun _ => rfl,fun _ => rfl,
    fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl⟩

variable [Fintype P]
lemma Iso.unpaired {c : Comparisons (E:=E) l} {c' : Comparisons (E:=E) l'} (f : Iso c c') :
    (Finset.univ.filter (fun x => c.pairing.partner x=x)).card=
    (Finset.univ.filter (fun x => c'.pairing.partner x=x)).card := by
  rw [←Fintype.card_subtype,←Fintype.card_subtype]
  apply Fintype.card_congr
  exact (position f.path f.length_eq).subtypeEquiv (fun x => by
    rw [←f.partner_eq,(position f.path f.length_eq).injective.eq_iff])
end
open scoped Classical
open ComparedBlocks ChunkComparisons
variable {P E : Type} {l l' : P → ℕ}
def castBackIso (h : l'=l) (c : Comparisons (E:=E) l) : Iso (cast h.symm c) c where
  path := Equiv.refl P
  comparison := Equiv.refl E
  length_eq p := congrFun h p
  flip_eq := by cases h; exact fun _ => rfl
  source_eq := by cases h; exact fun _ => rfl
  lo_eq := by cases h; exact fun _ => rfl
  hi_eq := by cases h; exact fun _ => rfl
  reverse_eq := by cases h; exact fun _ => rfl
  offset_eq := by cases h; exact fun _ => rfl
end TorsionFreeZeroDivisors.ComparisonGeometry

namespace TorsionFreeZeroDivisors.RawSourcePattern

section
open scoped Classical BigOperators
open PortSubdivision MarkedChainBound DegreeTwoSuppression ChainSuppression SuppressedMoore ChainPaths
open ChainIsomorphism ChainChunkTransport ChunkComparisons FiniteChunking ComparedBlocks
open ActualComplexity CoreStripping ImageComplexity GirthAsymptotics TypedGraphs ActualPatternEvent

/-- The data of a literal bounded family of immersed graph paths. The finite
image graph is arbitrary; only the source's bounds on path and comparison
counts, total length and proportion of unpaired letters are stated here. -/
structure Data (B K I rep : ℕ) where
  V : Type
  D : Type
  P : Type
  E : Type
  [fV : Fintype V]
  [fD : Fintype D]
  [fP : Fintype P]
  [fE : Fintype E]
  graph : PortGraph V D
  no_isolated : Function.Surjective graph.origin
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List D
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  image : ∀ d,∃ p,d∈paths p ∨ graph.reverse d∈paths p
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step graph.origin graph.reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step graph.origin graph.reverse x y
  girth : ∀ a (c : graph.subdivision.Walk a a),c.IsCycle →
    (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : D => (1:ℝ))) c
  length_le : (∑p,(paths p).length:ℕ)≤B*L (size rep)
  length_ge : L (size rep)≤(∑p,(paths p).length:ℕ)
  comparisons : Comparisons (E:=E) (fun p => (paths p).length)
  lower : E → ℕ
  upper : E → ℕ
  lower_eq : ∀ e,comparisons.lo e=lower e
  upper_eq : ∀ e,comparisons.hi e=upper e
  lower_le : ∀ e,lower e≤upper e
  upper_le : ∀ e,upper e≤(paths (comparisons.source e)).length
  reduced : ∀ x e,comparisons.side x=some e →
    RawDecomposition.dart paths x≠RawDecomposition.dart paths (comparisons.pairing.partner x) ∧
    RawDecomposition.dart paths x≠graph.reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*(∑p,(paths p).length:ℕ)
attribute [instance] Data.fV Data.fD Data.fP Data.fE

namespace Data
variable {B K I rep : ℕ} (a : Data B K I rep)
abbrev vertices := ActualComplexity.endpoints a.graph a.paths a.nonempty
abbrev mark := MarkedChainBound.marks a.graph a.vertices
abbrev degree_two := marks_degree_two a.graph a.vertices
abbrev decomposed := RawDecomposition.paths a.graph a.paths a.nonempty a.path_chain
abbrev decomposed_nonempty := RawDecomposition.nonempty a.graph a.paths a.nonempty a.path_chain
abbrev lengths_eq := RawDecomposition.lengths_eq a.graph a.paths a.nonempty a.path_chain
abbrev comparison := ComparisonGeometry.cast a.lengths_eq.symm a.comparisons
abbrev iso := ComparisonGeometry.castBackIso a.lengths_eq a.comparisons
abbrev position := RawDecomposition.position a.graph a.paths a.nonempty a.path_chain

lemma expands (p : a.P) : (a.decomposed p).flatMap (word a.graph a.mark a.degree_two)=a.paths p :=
  RawDecomposition.expands a.graph a.paths a.nonempty a.path_chain p
lemma length_eq (p : a.P) : pathLength (chunks a.graph a.mark a.degree_two a.decomposed)
    (chunkLength a.graph a.mark a.degree_two a.decomposed) p=(a.paths p).length :=
  RawDecomposition.length_eq a.graph a.paths a.nonempty a.path_chain p
lemma dart_eq (x : Position (pathLength (chunks a.graph a.mark a.degree_two a.decomposed)
    (chunkLength a.graph a.mark a.degree_two a.decomposed))) :
    originalDart a.graph a.mark a.degree_two a.decomposed x=RawDecomposition.dart a.paths (a.position x) :=
  RawDecomposition.dart_eq a.graph a.paths a.nonempty a.path_chain x
lemma position_iso : a.position=ComparisonGeometry.position a.iso.path a.iso.length_eq := rfl

/-- All suppression data is constructed from the literal paths, with no bounds
on a suppressed skeleton included among the raw data. -/
def suppressed : SourcePattern.Data B K I rep where
  V := a.V
  D := a.D
  P := a.P
  E := a.E
  graph := a.graph
  vertices := a.vertices
  vertices_bound := (ActualComplexity.endpoints_card a.graph a.paths a.nonempty).trans
    (Nat.mul_le_mul_left 2 a.path_bound)
  no_isolated := a.no_isolated
  side := a.side
  side_edge := a.side_edge
  paths := a.decomposed
  nonempty := a.decomposed_nonempty
  root := a.root
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  image := by
    intro d
    simpa only [expands] using a.image d
  path_chain := by simpa only [expands] using a.path_chain
  cyclic_chain := by simpa only [expands] using a.cyclic_chain
  girth := a.girth
  length_le := by simpa only [expands] using a.length_le
  length_ge := by simpa only [expands] using a.length_ge
  comparisons := a.comparison
  lower := a.lower
  upper := a.upper
  lower_eq e := (a.iso.lo_eq e).trans (a.lower_eq e)
  upper_eq e := (a.iso.hi_eq e).trans (a.upper_eq e)
  lower_le := a.lower_le
  upper_le e := by
    rw [a.length_eq]
    have hs : a.comparison.source e=a.comparisons.source e := a.iso.source_eq e
    rw [hs]
    exact a.upper_le e
  reduced := by
    intro x e he
    have hh := a.reduced (a.position x) e ((a.iso.side_some x e).mpr he)
    rw [a.dart_eq,a.dart_eq,position_iso,a.iso.partner_eq]
    exact hh
  unpaired_le := by
    rw [a.iso.unpaired]
    simpa only [expands] using a.unpaired_le

/-- The event reads the literal original path label, and pins the actual initial
vertex of the exceptional interval on its prescribed side. -/
def event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep) : Prop :=
  ∃ label : a.D → Types.Letter,
    (∀ d,label (a.graph.reverse d)=Types.inverse (label d)) ∧
    (∀ d e,a.graph.origin d=a.graph.origin e → label d=label e → d=e) ∧
    (∀ p e,a.comparisons.side p=some e → label (RawDecomposition.dart a.paths p)=
      if a.comparisons.reverse e then Types.inverse (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph a.graph a.side a.side_edge true)
      (fun d => label d.val) (@Types.outgoingA rep)
      (RootPins.pin (SidePins.root a.side (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) true) x)
      Types.inverse r.1) ∧
    Nonempty (RealizationTransport.Embedding (SideRestriction.graph a.graph a.side a.side_edge false)
      (fun d => label d.val) (@Types.outgoingB rep)
      (RootPins.pin (SidePins.root a.side (a.root.map fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) false) y)
      Types.inverse r.2)

lemma suppressed_event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep)
    (h : a.event x y r) :
    OriginalPattern.Realized a.graph a.mark a.degree_two a.side a.side_edge a.decomposed
      a.decomposed_nonempty a.root rep x y a.comparison r := by
  rcases h with ⟨label,hl,hn,hc,ha,hb⟩
  refine ⟨label,hl,hn,?_,?_,?_⟩
  · intro p e he
    have hh := hc (a.position p) e ((a.iso.side_some p e).mpr he)
    rw [a.dart_eq,a.dart_eq,position_iso,a.iso.partner_eq,a.iso.reverse_eq]
    exact hh
  · simpa only [sourcePinA,RawDecomposition.source_eq] using ha
  · simpa only [sourcePinB,RawDecomposition.source_eq] using hb

end Data
end
open scoped Classical
open GirthAsymptotics TypedGraphs ActualPatternEvent Filter

/-- Literal immersed source paths, not assumed to come with a suppression or
finite encoding, are avoided by an actual pair of high-girth typed graphs. -/
theorem eventually_avoids (B K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,∀ a : Data B K I rep,¬a.event x y r := by
  have hT : 0<SourcePattern.T B K := Nat.mul_pos (SourcePattern.R_pos B K)
    (by omega)
  filter_upwards [BoundedPattern.eventually_avoids (SourcePattern.R B K) K (SourcePattern.T B K)
    I B (SourcePattern.R B K) (SourcePattern.T B K) (I*(SourcePattern.T B K)^2)
    (SourcePattern.R_pos B K) hK hI hT,
    (L_tendsto.comp size_tendsto).eventually (eventually_ge_atTop 1)] with rep hr hL
  change 1≤L (size rep) at hL
  intro x y
  obtain ⟨r,hs,ha⟩ := hr x y
  refine ⟨r,hs,fun a he => ?_⟩
  exact ha (a.suppressed.bounded (by omega)) (a.suppressed.bounded_good (by omega))
    (a.suppressed_event x y r he)

end TorsionFreeZeroDivisors.RawSourcePattern
namespace TorsionFreeZeroDivisors.DiameterCounting
open scoped BigOperators Classical
open ConditionedMatchings
variable {V D T : Type*} [Fintype V] [Fintype D]
variable (origin : D → V)

def ports (S : Finset V) : Finset D := Finset.univ.filter (fun e => origin e ∈ S)

omit [Fintype V] in
@[simp] lemma mem_ports (S : Finset V) (e : D) : e ∈ ports origin S ↔ origin e ∈ S := by
  simp [ports]

omit [Fintype V] in
lemma card_ports (S : Finset V) :
    (ports origin S).card = ∑ v ∈ S, Nat.card {e : D // origin e=v} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := origin) (t := S)]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
    ext e
    simp only [Finset.mem_filter,mem_ports,Finset.mem_univ,true_and]
    exact ⟨fun h => h.2,fun h => ⟨h ▸ hv,h⟩⟩
  · intro e he
    exact (mem_ports origin S e).mp he

omit [Fintype V] in
lemma card_ports_le (d : ℕ) (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (S : Finset V) : (ports origin S).card ≤ S.card*d := by
  rw [card_ports]
  calc
    _ ≤ ∑ _v ∈ S, d := Finset.sum_le_sum fun v _ => hd v
    _ = _ := by simp

omit [Fintype V] in
lemma card_ports_ge (d : ℕ) (hd : ∀ v, d ≤ Nat.card {e : D // origin e=v})
    (S : Finset V) : S.card*d ≤ (ports origin S).card := by
  rw [card_ports]
  calc
    _ = ∑ _v ∈ S, d := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => hd v

/-- All potential unordered prescribed matching pairs within a vertex set.
Keeping infeasible ones is a harmless overcount. -/
def possible (S : Finset V) : Finset (Sym2 D) :=
  ((ports origin S) ×ˢ (ports origin S)).image fun p => s(p.1,p.2)

omit [Fintype V] in
lemma mk_mem_possible {S : Finset V} {a b : D}
    (ha : origin a ∈ S) (hb : origin b ∈ S) : s(a,b) ∈ possible origin S := by
  exact Finset.mem_image.mpr ⟨(a,b),by simpa using And.intro ha hb,rfl⟩

omit [Fintype V] in
lemma possible_card (d : ℕ) (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (S : Finset V) : (possible origin S).card ≤ (S.card*d)^2 := by
  calc
    _ ≤ ((ports origin S) ×ˢ (ports origin S)).card := Finset.card_image_le
    _ = (ports origin S).card^2 := by rw [Finset.card_product]; ring
    _ ≤ _ := Nat.pow_le_pow_left (card_ports_le origin d hd S) _

variable {label : D → T} {bar : T → T}

def closedNeighbors (r : Matching label bar) (S : Finset V) : Finset V :=
  S ∪ (ports origin S).image (fun e => origin (r e))

def incidentEdges (r : Matching label bar) (S : Finset V) : Finset (Sym2 D) :=
  (ports origin S).image (fun e => s(e,r e))

omit [Fintype V] in
lemma incident_possible (r : Matching label bar) (S U : Finset V)
    (hU : closedNeighbors origin r S ⊆ U) : incidentEdges origin r S ⊆ possible origin U := by
  intro p hp
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
  have hs : origin e ∈ S := (mem_ports origin S e).mp he
  apply mk_mem_possible origin
  · exact hU (Finset.mem_union_left _ hs)
  · exact hU (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))

omit [Fintype V] in
lemma contains_incident (r : Matching label bar) (S : Finset V) :
    r.Contains (incidentEdges origin r S) := by
  intro a b hab
  obtain ⟨e,_,he⟩ := Finset.mem_image.mp hab
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · rw [← h1,← h2]
  · rw [← h1,← h2,r.reverse_reverse]

omit [Fintype V] in
lemma twice_incident (r : Matching label bar) (S : Finset V) :
    (ports origin S).card ≤ 2*(incidentEdges origin r S).card := by
  apply Finset.card_le_mul_card_image
  intro p hp
  obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hp
  have hsub : ((ports origin S).filter (fun a => s(a,r a)=s(e,r e))) ⊆ {e,r e} := by
    intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  have hp : ({e,r e} : Finset D).card ≤ 2 := by
    calc
      _ ≤ ({r e} : Finset D).card+1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  exact (Finset.card_le_card hsub).trans hp

/-- The literal dense set forced by a failure of the required doubling.
It keeps distinct matching prescriptions rather than counting occurrences. -/
theorem dense_witness (r : Matching label bar) (k d₀ : ℕ)
    (hd₀ : ∀ v, d₀ ≤ Nat.card {e : D // origin e=v})
    (hk : 2*k ≤ Fintype.card V) (S : Finset V) (hS : S.card=k)
    (hfail : (closedNeighbors origin r S).card ≤ 2*k) :
    ∃ U : Finset V, U.card=2*k ∧
      ∃ C : Finset (Sym2 D), C ⊆ possible origin U ∧
        C.card=(d₀*k+1)/2 ∧ r.Contains C := by
  obtain ⟨U,hU,hUc⟩ := Finset.exists_superset_card_eq hfail hk
  have he : (d₀*k+1)/2 ≤ (incidentEdges origin r S).card := by
    have h := (card_ports_ge origin d₀ hd₀ S).trans (twice_incident origin r S)
    rw [hS,Nat.mul_comm k d₀] at h
    omega
  obtain ⟨C,hC,hCc⟩ := Finset.exists_subset_card_eq he
  refine ⟨U,hUc,C,hC.trans (incident_possible origin r S U hU),hCc,?_⟩
  intro a b hab
  exact contains_incident origin r S a b (hC hab)

/-- Union of all dense witnesses of a fixed vertex and prescription size. -/
def denseEvent (N m t : ℕ) : Finset (Matching label bar) :=
  (Finset.univ.powersetCard m).biUnion fun U =>
    ((possible origin U).powersetCard t).biUnion fun C =>
      Matching.conditioned (label := label) (bar := bar) origin N C

/-- The exact finite union bound in the girth-conditioned space. The two
binomial factors count sets, avoiding the spurious extra power of k that
would arise if one counted ordered lists of edge prescriptions. -/
theorem dense_count (N m t d R : ℕ) (hbar : ∀ t, bar t ≠ t) (h2 : 2≤d)
    (hd : ∀ v, Nat.card {e : D // origin e=v} ≤ d)
    (hR : ∀ x, R+t+4*d^(2*N+1) ≤ Nat.card {e : D // label e=label x}) :
    (denseEvent (label := label) (bar := bar) origin N m t).card * R^t ≤
      (Fintype.card V).choose m * ((m*d)^2).choose t *
        (Matching.conditioned (label := label) (bar := bar) origin N ∅).card := by
  let Ω := Matching.conditioned (label := label) (bar := bar) origin N ∅
  let Us : Finset (Finset V) := Finset.univ.powersetCard m
  have hU (U : Finset V) (hu : U∈Us) :
      (((possible origin U).powersetCard t).biUnion fun C =>
        Matching.conditioned (label := label) (bar := bar) origin N C).card * R^t ≤
      ((m*d)^2).choose t * Ω.card := by
    have hcU : U.card=m := (Finset.mem_powersetCard.mp hu).2
    calc
      _ ≤ (∑ C ∈ (possible origin U).powersetCard t,
          (Matching.conditioned (label := label) (bar := bar) origin N C).card) * R^t :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ C ∈ (possible origin U).powersetCard t,
          (Matching.conditioned (label := label) (bar := bar) origin N C).card * R^t :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ _C ∈ (possible origin U).powersetCard t, Ω.card := by
        apply Finset.sum_le_sum
        intro C hC
        have hc : C.card=t := (Finset.mem_powersetCard.mp hC).2
        have h := Matching.prescriptions_count (label := label) (bar := bar)
          origin N hbar d h2 hd R C (by intro x; rw [hc]; exact hR x)
        simpa only [hc] using h
      _ = (possible origin U).card.choose t * Ω.card := by simp
      _ ≤ ((m*d)^2).choose t * Ω.card := by
        apply Nat.mul_le_mul_right
        apply Nat.choose_le_choose
        simpa only [hcU] using possible_card origin d hd U
  calc
    _ ≤ (∑ U ∈ Us, (((possible origin U).powersetCard t).biUnion fun C =>
        Matching.conditioned (label := label) (bar := bar) origin N C).card) * R^t :=
      Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ U ∈ Us, (((possible origin U).powersetCard t).biUnion fun C =>
        Matching.conditioned (label := label) (bar := bar) origin N C).card * R^t :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ _U ∈ Us, ((m*d)^2).choose t * Ω.card := Finset.sum_le_sum hU
    _ = _ := by simp [Us,Ω,Nat.mul_assoc]

/-- A failing set in an actual girth-conditioned sample occurs in the counted
union. No labels, vertex names or repeated traversals have been discarded. -/
theorem mem_dense_of_failure (N k d₀ : ℕ) (r : Matching label bar)
    (hr : r∈Matching.conditioned (label := label) (bar := bar) origin N ∅)
    (hd₀ : ∀ v, d₀ ≤ Nat.card {e : D // origin e=v})
    (hk : 2*k ≤ Fintype.card V) (S : Finset V) (hS : S.card=k)
    (hfail : (closedNeighbors origin r S).card ≤ 2*k) :
    r∈denseEvent (label := label) (bar := bar) origin N (2*k) ((d₀*k+1)/2) := by
  obtain ⟨U,hUc,C,hC,hCc,hrC⟩ := dense_witness origin r k d₀ hd₀ hk S hS hfail
  apply Finset.mem_biUnion.mpr
  refine ⟨U,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hUc⟩,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨C,Finset.mem_powersetCard.mpr ⟨hC,hCc⟩,?_⟩
  simp only [Matching.conditioned,Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
  exact ⟨hrC,hr.2⟩

end TorsionFreeZeroDivisors.DiameterCounting

end

end OAI
