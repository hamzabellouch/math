import Mathlib
import OAI.Algebra.GroupRing.TypedDiameter

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SupportedImage
open scoped Classical BigOperators
open PortSubdivision WeightedPortMoore WeightedCycles CoreStripping
variable {V D : Type} (Γ : PortGraph V D) (Q : Finset D) (hQ : Symmetric Γ Q)

/-- Discard isolated ambient vertices as well as unused darts. -/
def vertices : Finset V := Q.image Γ.origin

def graph : PortGraph (vertices Γ Q) Q where
  origin d := ⟨Γ.origin d,Finset.mem_image.mpr ⟨d,d.property,rfl⟩⟩
  reverse d := ⟨Γ.reverse d,hQ d d.property⟩
  reverse_reverse d := Subtype.ext (Γ.reverse_reverse d)
  reverse_ne d h := Γ.reverse_ne d (congrArg Subtype.val h)

lemma no_isolated : Function.Surjective (graph Γ Q hQ).origin := by
  intro v
  obtain ⟨d,hd,he⟩ := Finset.mem_image.mp v.property
  exact ⟨⟨d,hd⟩,Subtype.ext he⟩

/-- Literal inclusion into the actual source graph subdivision. -/
def inclusion : (graph Γ Q hQ).subdivision →g Γ.subdivision where
  toFun := Sum.map Subtype.val Subtype.val
  map_rel' := by
    intro a b h
    rcases a with a|a <;> rcases b with b|b
    · exact h
    · exact congrArg Subtype.val h
    · exact congrArg Subtype.val h
    · exact congrArg Subtype.val h
lemma inclusion_injective : Function.Injective (inclusion Γ Q hQ) :=
  Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
lemma inclusion_weight {a b : (vertices Γ Q) ⊕ Q}
    (p : (graph Γ Q hQ).subdivision.Walk a b) :
    weight (edgeWeight (fun _ : D => (1:ℝ))) (p.map (inclusion Γ Q hQ)) =
      weight (edgeWeight (fun _ : Q => (1:ℝ))) p := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.map_cons,weight_cons,weight_cons,ih]
    congr 1
    cases a <;> cases b <;> rfl

lemma girth (L : ℝ)
    (hL : ∀ a (p : Γ.subdivision.Walk a a),p.IsCycle →
      L≤weight (edgeWeight (fun _ : D => (1:ℝ))) p) :
    ∀ a (p : (graph Γ Q hQ).subdivision.Walk a a),p.IsCycle →
      L≤weight (edgeWeight (fun _ : Q => (1:ℝ))) p := by
  intro a p hp
  have hm := hp.map (inclusion_injective Γ Q hQ)
  simpa only [inclusion_weight] using hL _ (p.map (inclusion Γ Q hQ)) hm

variable {P : Type} (paths : P → List D) (hpaths : ∀ p d,d∈paths p → d∈Q)
def path (p : P) : List Q := (paths p).attach.map (fun d => ⟨d.val,hpaths p d.val d.property⟩)
lemma path_val (p : P) : (path Q paths hpaths p).map Subtype.val=paths p := by
  simp only [path,List.map_map,Function.comp_def]
  simpa only [List.map_id,id_eq] using (List.attach_map_val (f:=id) (l:=paths p))
lemma length (p : P) : (path Q paths hpaths p).length=(paths p).length := by
  simp [path]
lemma nonempty (p : P) (hp : paths p≠[]) : path Q paths hpaths p≠[] := by
  intro hn
  apply hp
  rw [←path_val Q paths hpaths p,hn]
  rfl
lemma chain (p : P) (hp : (paths p).IsChain (WeightedMoore.PortWalk.step Γ.origin Γ.reverse)) :
    (path Q paths hpaths p).IsChain (WeightedMoore.PortWalk.step (graph Γ Q hQ).origin (graph Γ Q hQ).reverse) := by
  have hh : ((path Q paths hpaths p).map Subtype.val).IsChain
      (WeightedMoore.PortWalk.step Γ.origin Γ.reverse) := by rw [path_val]; exact hp
  rw [List.isChain_map] at hh
  apply hh.imp
  intro a b hab
  exact ⟨Subtype.ext hab.1,fun h => hab.2 (congrArg Subtype.val h)⟩
lemma mem_path (p : P) (d : Q) : d∈path Q paths hpaths p ↔ d.val∈paths p := by
  rw [←path_val Q paths hpaths p,List.mem_map]
  constructor
  · intro hd
    exact ⟨d,hd,rfl⟩
  · rintro ⟨e,he,hed⟩
    exact (Subtype.ext hed : e=d) ▸ he
lemma head_value (p : P) (hp : paths p≠[]) :
    ((path Q paths hpaths p).head (nonempty Q paths hpaths p hp)).val=(paths p).head hp := by
  have hh := congrArg List.head? (path_val Q paths hpaths p)
  rw [List.head?_map,List.head?_eq_some_head (nonempty Q paths hpaths p hp),
    List.head?_eq_some_head hp] at hh
  exact Option.some.inj hh
lemma cyclic (p : P)
    (hp : ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step Γ.origin Γ.reverse x y) :
    ∀ᵉ (x∈(path Q paths hpaths p).getLast?) (y∈(path Q paths hpaths p).head?),
      WeightedMoore.PortWalk.step (graph Γ Q hQ).origin (graph Γ Q hQ).reverse x y := by
  intro x hx y hy
  have hxv : x.val∈(paths p).getLast? := by
    rw [←path_val Q paths hpaths p,List.getLast?_map]
    change ((path Q paths hpaths p).getLast?).map Subtype.val=some x.val
    rw [show (path Q paths hpaths p).getLast?=some x from hx]
    rfl
  have hyv : y.val∈(paths p).head? := by
    rw [←path_val Q paths hpaths p,List.head?_map]
    change ((path Q paths hpaths p).head?).map Subtype.val=some y.val
    rw [show (path Q paths hpaths p).head?=some y from hy]
    rfl
  have hh := hp x hxv y hyv
  exact ⟨Subtype.ext hh.1,fun he => hh.2 (congrArg Subtype.val he)⟩
lemma covered (hc : ∀ d∈Q,∃ p,d∈paths p ∨ Γ.reverse d∈paths p) :
    ∀ d : Q,∃ p,d∈path Q paths hpaths p ∨ (graph Γ Q hQ).reverse d∈path Q paths hpaths p := by
  intro d
  obtain ⟨p,hp⟩ := hc d d.property
  refine ⟨p,?_⟩
  simpa only [mem_path, graph] using hp

/-- The symmetric set of precisely the darts used by the actual paths. -/
def used [Fintype P] (paths : P → List D) : Finset D :=
  Finset.univ.biUnion fun p => (paths p).toFinset ∪ (paths p).toFinset.image Γ.reverse
lemma mem_used [Fintype P] (paths : P → List D) (d : D) :
    d∈used Γ paths ↔ ∃ p,d∈paths p ∨ Γ.reverse d∈paths p := by
  simp only [used,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union,List.mem_toFinset,Finset.mem_image]
  apply exists_congr
  intro p
  constructor
  · rintro (h|⟨e,he,hed⟩)
    · exact Or.inl h
    · right
      have heq : e=Γ.reverse d := by simpa using congrArg Γ.reverse hed
      exact heq ▸ he
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr ⟨Γ.reverse d,h,Γ.reverse_reverse d⟩
lemma used_symmetric [Fintype P] (paths : P → List D) : Symmetric Γ (used Γ paths) := by
  intro d hd
  obtain ⟨p,hp⟩ := (mem_used Γ paths d).mp hd
  apply (mem_used Γ paths (Γ.reverse d)).mpr
  refine ⟨p,?_⟩
  simpa only [PortGraph.reverse_reverse_apply] using hp.symm
lemma path_in_used [Fintype P] (paths : P → List D) (p : P) (d : D) (hd : d∈paths p) :
    d∈used Γ paths := (mem_used Γ paths d).mpr ⟨p,Or.inl hd⟩

end TorsionFreeZeroDivisors.SupportedImage

namespace TorsionFreeZeroDivisors.RootPins
open scoped Classical
lemma pin_map {V W T : Type*} (f : V ↪ W) (r : Option V) (t : T) (v : V) :
    pin (r.map f) t (f v)=pin r t v := by
  cases r with
  | none => simp [pin]
  | some w => simp [pin,f.injective.eq_iff]
end TorsionFreeZeroDivisors.RootPins

namespace TorsionFreeZeroDivisors.SupportedImage
open scoped Classical
open PortSubdivision
variable {V D : Type} (Γ : PortGraph V D) (Q : Finset D) (hQ : CoreStripping.Symmetric Γ Q)
    (side : V → Bool) (hs : ∀ d,side (Γ.origin (Γ.reverse d))=side (Γ.origin d)) (b : Bool)
def sideVertex : SideRestriction.Vertex (fun v : vertices Γ Q => side v.val) b ↪ SideRestriction.Vertex side b :=
  ⟨fun v => ⟨v.val.val,v.property⟩,fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h))⟩
def sideDart : SideRestriction.Dart (graph Γ Q hQ) (fun v => side v.val) b ↪ SideRestriction.Dart Γ side b :=
  ⟨fun d => ⟨d.val.val,d.property⟩,fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h))⟩
lemma side_root (r : Option (vertices Γ Q)) :
    (SidePins.root (fun v : vertices Γ Q => side v.val) r b).map (sideVertex Γ Q side b)=
      SidePins.root side (r.map Subtype.val) b := by
  cases r with
  | none => rfl
  | some v =>
    by_cases hv : side v.val=b
    · simp only [SidePins.root,Option.map_some,Option.bind_some,hv,dite_eq_left]
      rfl
    · simp [SidePins.root,hv]

variable [Fintype V] [Fintype D] {T TV : Type} [Fintype T] [Fintype TV]
    (label : D → T) (outgoing : TV → Finset T) (bar : T → T)
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) bar)
    (root : Option (vertices Γ Q)) (target : TV)
/-- Actual embeddings restrict to the used image, with the exact side/root pin. -/
def embedding
    (e : RealizationTransport.Embedding (SideRestriction.graph Γ side hs b) (fun d => label d.val)
      outgoing (RootPins.pin (SidePins.root side (root.map Subtype.val) b) target) bar r) :
    RealizationTransport.Embedding
      (SideRestriction.graph (graph Γ Q hQ) (fun v => side v.val) (fun d => hs d.val) b)
      (fun d => label d.val.val) outgoing
      (RootPins.pin (SidePins.root (fun v : vertices Γ Q => side v.val) root b) target) bar r :=
  RealizationTransport.restrict e _ (sideVertex Γ Q side b) (sideDart Γ Q hQ side b)
    (fun _ => rfl) (fun _ => rfl) _ (by
      intro v y hy
      rw [←side_root Γ Q side b root,RootPins.pin_map]
      exact hy)
end TorsionFreeZeroDivisors.SupportedImage
namespace TorsionFreeZeroDivisors.AmbientPattern
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
/-- A path system in an ambient finite graph. The graph need not be the union
of the paths; taking its literal supported image constructs the raw data. -/
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
  side : V → Bool
  side_edge : ∀ d,side (graph.origin (graph.reverse d))=side (graph.origin d)
  paths : P → List D
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
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
abbrev used := SupportedImage.used a.graph a.paths
abbrev symmetric := SupportedImage.used_symmetric a.graph a.paths
abbrev supportedGraph := SupportedImage.graph a.graph a.used a.symmetric
abbrev vertices := SupportedImage.vertices a.graph a.used
abbrev pathUsed := SupportedImage.path_in_used a.graph a.paths
abbrev supportedPaths := SupportedImage.path a.used a.paths a.pathUsed
lemma lengths_eq : (fun p => (a.supportedPaths p).length)=(fun p => (a.paths p).length) :=
  funext (SupportedImage.length a.used a.paths a.pathUsed)
abbrev comparison := ComparisonGeometry.cast a.lengths_eq.symm a.comparisons
abbrev iso := ComparisonGeometry.castBackIso a.lengths_eq a.comparisons
abbrev position : Position (fun p => (a.supportedPaths p).length) ≃ Position (fun p => (a.paths p).length) :=
  ComparisonGeometry.position a.iso.path a.iso.length_eq
lemma dart_eq (x : Position (fun p => (a.supportedPaths p).length)) :
    (RawDecomposition.dart a.supportedPaths x).val=RawDecomposition.dart a.paths (a.position x) := by
  apply Option.some.inj
  rw [←Option.map_some (f:=Subtype.val),←RawDecomposition.dart_get,←List.getElem?_map,
    SupportedImage.path_val,←RawDecomposition.dart_get]
  rfl

/-- Restrict to actual used darts and their incident vertices. Every original
length, comparison and counting hypothesis is transported verbatim. -/
def supported : RawSourcePattern.Data B K I rep where
  V := a.vertices
  D := a.used
  P := a.P
  E := a.E
  graph := a.supportedGraph
  no_isolated := SupportedImage.no_isolated a.graph a.used a.symmetric
  side := fun v => a.side v.val
  side_edge d := a.side_edge d.val
  paths := a.supportedPaths
  nonempty p := SupportedImage.nonempty a.used a.paths a.pathUsed p (a.nonempty p)
  root := a.root
  path_bound := a.path_bound
  comparison_bound := a.comparison_bound
  image := SupportedImage.covered a.graph a.used a.symmetric a.paths a.pathUsed
    (fun d hd => (SupportedImage.mem_used a.graph a.paths d).mp hd)
  path_chain p := SupportedImage.chain a.graph a.used a.symmetric a.paths a.pathUsed p (a.path_chain p)
  cyclic_chain p hp := SupportedImage.cyclic a.graph a.used a.symmetric a.paths a.pathUsed p (a.cyclic_chain p hp)
  girth := SupportedImage.girth a.graph a.used a.symmetric (L (size rep)) a.girth
  length_le := by simpa only [SupportedImage.length] using a.length_le
  length_ge := by simpa only [SupportedImage.length] using a.length_ge
  comparisons := a.comparison
  lower := a.lower
  upper := a.upper
  lower_eq e := (a.iso.lo_eq e).trans (a.lower_eq e)
  upper_eq e := (a.iso.hi_eq e).trans (a.upper_eq e)
  lower_le := a.lower_le
  upper_le e := by
    rw [SupportedImage.length]
    have hs : a.comparison.source e=a.comparisons.source e := a.iso.source_eq e
    rw [hs]
    exact a.upper_le e
  reduced := by
    intro x e he
    have hh := a.reduced (a.position x) e ((a.iso.side_some x e).mpr he)
    constructor
    · intro h
      apply hh.1
      have hv := congrArg Subtype.val h
      rw [a.dart_eq,a.dart_eq,a.iso.partner_eq] at hv
      exact hv
    · intro h
      apply hh.2
      have hv := congrArg Subtype.val h
      change (RawDecomposition.dart a.supportedPaths x).val=a.graph.reverse
        (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner x)).val at hv
      rw [a.dart_eq,a.dart_eq,a.iso.partner_eq] at hv
      exact hv
  unpaired_le := by
    rw [a.iso.unpaired]
    simpa only [SupportedImage.length] using a.unpaired_le
abbrev supportedRoot : Option a.vertices := a.root.map fun p =>
  a.supportedGraph.origin ((a.supportedPaths p).head (a.supported.nonempty p))
lemma supported_root : a.supportedRoot.map Subtype.val=
    a.root.map (fun p => a.graph.origin ((a.paths p).head (a.nonempty p))) := by
  cases h : a.root with
  | none => simp only [supportedRoot,h,Option.map_none]
  | some p =>
    simp only [supportedRoot,h,Option.map_some]
    change some (a.graph.origin (((a.supportedPaths p).head (a.supported.nonempty p)).val))=_
    rw [SupportedImage.head_value]

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

lemma comparing (label : a.D → Types.Letter)
    (hc : ∀ p e,a.comparisons.side p=some e → label (RawDecomposition.dart a.paths p)=
      if a.comparisons.reverse e then Types.inverse (label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p)))
      else label (RawDecomposition.dart a.paths (a.comparisons.pairing.partner p))) :
    ∀ (p : Position (fun p => (a.supportedPaths p).length)) (e : a.E),a.comparison.side p=some e →
      label (RawDecomposition.dart a.supportedPaths p).val=
      if a.comparison.reverse e then Types.inverse
        (label (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner p)).val)
      else label (RawDecomposition.dart a.supportedPaths (a.comparison.pairing.partner p)).val := by
  intro p e he
  have hh := hc (a.position p) e ((a.iso.side_some p e).mpr he)
  have hr : a.comparison.reverse e=a.comparisons.reverse e := a.iso.reverse_eq e
  have hp : a.position (a.comparison.pairing.partner p)=a.comparisons.pairing.partner (a.position p) :=
    a.iso.partner_eq p
  simp only [a.dart_eq]
  rw [hr,hp]
  exact hh

/-- Restrict the literal realization, including its exact root and labels,
to the supported raw source pattern. -/
lemma supported_event (x : Types.VertexA rep) (y : Types.VertexB rep) (r : Match rep)
    (h : a.event x y r) : a.supported.event x y r := by
  rcases h with ⟨label,hl,hn,hc,ha,hb⟩
  refine ⟨(fun d => label d.val),?_,?_,?_,?_,?_⟩
  · exact fun d => hl d.val
  · intro d e ho he
    exact Subtype.ext (hn d.val e.val (congrArg Subtype.val ho) he)
  · exact a.comparing label hc
  · refine ⟨SupportedImage.embedding a.graph a.used a.symmetric a.side a.side_edge true label
      (@Types.outgoingA rep) Types.inverse r.1 a.supportedRoot x ?_⟩
    simpa only [a.supported_root] using ha.some
  · refine ⟨SupportedImage.embedding a.graph a.used a.symmetric a.side a.side_edge false label
      (@Types.outgoingB rep) Types.inverse r.2 a.supportedRoot y ?_⟩
    simpa only [a.supported_root] using hb.some

end Data

/-- The fixed-sample bounded pattern conclusion applies to every original
ambient path system, not only to a presupposed image or suppression. -/
theorem with_diameter (B K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in Filter.atTop,∀ (x : Types.VertexA rep) (y : Types.VertexB rep),
      ∃ r∈samples rep,GraphSample.Diameters rep r ∧ ∀ a : Data B K I rep,¬a.event x y r := by
  filter_upwards [GraphSample.raw_with_diameter B K I hK hI] with rep hr
  intro x y
  obtain ⟨r,hr,hd,ha⟩ := hr x y
  exact ⟨r,hr,hd,fun a he => ha a.supported (a.supported_event x y r he)⟩
end TorsionFreeZeroDivisors.AmbientPattern

end

end OAI
