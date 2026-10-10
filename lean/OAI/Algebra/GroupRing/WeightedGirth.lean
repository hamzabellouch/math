import Mathlib
import OAI.Algebra.GroupRing.RawDecomposition

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.WeightedGirth
open scoped Classical BigOperators
open PortSubdivision WeightedPortMoore WeightedCycles
variable {V D : Type} (Γ : PortGraph V D)

def middle : Sym2 (V ⊕ D) → Bool :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr _,.inr _ => true
    | _,_ => false,by intro a b; cases a <;> cases b <;> rfl⟩
def bundle : Sym2 (V ⊕ D) → Finset (Sym2 (V ⊕ D)) :=
  Sym2.lift ⟨fun a b => match a,b with
    | .inr d,.inr e => {s(a,b),s(Sum.inl (Γ.origin d),a),s(Sum.inl (Γ.origin e),b)}
    | _,_ => {s(a,b)},by
      intro a b
      cases a <;> cases b
      all_goals simp only [Sym2.eq_swap]
      exact congrArg (fun t : Finset (Sym2 (V⊕D)) => insert _ t) (Finset.pair_comm _ _)⟩
lemma bundle_card (e : Sym2 (V ⊕ D)) : (bundle Γ e).card≤3 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a with
    | inl v => cases b <;> simp [bundle]
    | inr d =>
      cases b with
      | inl v => simp [bundle]
      | inr f =>
        change ({_,_,_} : Finset (Sym2 (V⊕D))).card ≤ 3
        have h₁ := Finset.card_insert_le s(Sum.inr d,Sum.inr f)
          ({s(Sum.inl (Γ.origin d),Sum.inr d),s(Sum.inl (Γ.origin f),Sum.inr f)} : Finset (Sym2 (V⊕D)))
        have h₂ := Finset.card_insert_le s(Sum.inl (Γ.origin d),Sum.inr d)
          ({s(Sum.inl (Γ.origin f),Sum.inr f)} : Finset (Sym2 (V⊕D)))
        simp only [Finset.card_singleton] at h₂
        dsimp only at *
        omega
lemma self_mem_bundle (e : Sym2 (V ⊕ D)) : e∈bundle Γ e := by
  induction e using Sym2.inductionOn with
  | _ a b => cases a <;> cases b <;> simp [bundle]
lemma weight_eq_indicator (e : Sym2 (V ⊕ D)) :
    edgeWeight (fun _ : D => (1:ℝ)) e=if middle e then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ a b => cases a <;> cases b <;> norm_num [edgeWeight,middle]

lemma edges_covered {a : V⊕D} (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    p.edges.toFinset⊆(p.edges.toFinset.filter (fun e => middle e)).biUnion (bundle Γ) := by
  intro e he
  have hep : e∈p.edges := List.mem_toFinset.mp he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hadj := p.adj_of_mem_edges hep
    cases x with
    | inl v =>
      cases y with
      | inl w => exact False.elim hadj
      | inr d =>
        change Γ.origin d=v at hadj
        subst v
        have hd : Sum.inr d∈p.support := p.snd_mem_support_of_mem_edges hep
        have hm := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
        have hm' : s(Sum.inr d,Sum.inr (Γ.reverse d))∈p.edges := (p.rotate_edges _ hd).mem_iff.mp hm
        apply Finset.mem_biUnion.mpr
        refine ⟨s(Sum.inr d,Sum.inr (Γ.reverse d)),Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm',rfl⟩,?_⟩
        simp [bundle]
    | inr d =>
      cases y with
      | inl v =>
        change Γ.origin d=v at hadj
        subst v
        have hd : Sum.inr d∈p.support := p.fst_mem_support_of_mem_edges hep
        have hm := Γ.cycle_middle_at_port d (p.rotate (.inr d) hd) (hp.rotate hd)
        have hm' : s(Sum.inr d,Sum.inr (Γ.reverse d))∈p.edges := (p.rotate_edges _ hd).mem_iff.mp hm
        apply Finset.mem_biUnion.mpr
        refine ⟨s(Sum.inr d,Sum.inr (Γ.reverse d)),Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm',rfl⟩,?_⟩
        simp [bundle,Sym2.eq_swap]
      | inr f =>
        exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_filter.mpr ⟨he,rfl⟩,self_mem_bundle Γ _⟩

/-- In a genuine subdivision cycle every middle edge supports at most two
spokes. Thus girth measured in three-edge subdivisions implies the literal
unit macro-edge weighted girth used by the pattern theorem. -/
lemma length_le_three_weight {a : V⊕D} (p : Γ.subdivision.Walk a a) (hp : p.IsCycle) :
    (p.length:ℝ)≤3*weight (edgeWeight (fun _ : D => (1:ℝ))) p := by
  have hn := hp.isTrail.edges_nodup
  have hc : p.edges.toFinset.card≤3*(p.edges.toFinset.filter (fun e => middle e)).card := calc
    _≤((p.edges.toFinset.filter (fun e => middle e)).biUnion (bundle Γ)).card := Finset.card_le_card (edges_covered Γ p hp)
    _≤∑e∈p.edges.toFinset.filter (fun e => middle e),(bundle Γ e).card := Finset.card_biUnion_le
    _≤∑_e∈p.edges.toFinset.filter (fun e => middle e),3 := Finset.sum_le_sum (fun e _ => bundle_card Γ e)
    _=3*(p.edges.toFinset.filter (fun e => middle e)).card := by simp [Nat.mul_comm]
  have hw : weight (edgeWeight (fun _ : D => (1:ℝ))) p=
      (p.edges.toFinset.filter (fun e => middle e)).card := by
    rw [weight,←List.sum_toFinset _ hn]
    simp only [weight_eq_indicator,←Finset.sum_filter]
    simp
  rw [hw]
  have hl : p.edges.toFinset.card=p.length := by rw [List.toFinset_card_of_nodup hn,SimpleGraph.Walk.length_edges]
  rw [hl] at hc
  exact_mod_cast hc
lemma weighted_girth (L : ℕ) (hg : (3*L:ℕ)≤Γ.subdivision.egirth) :
    ∀ a (p : Γ.subdivision.Walk a a),p.IsCycle → (L:ℝ)≤weight (edgeWeight (fun _ : D => (1:ℝ))) p := by
  intro a p hp
  have hl : 3*L≤p.length := by exact_mod_cast SimpleGraph.le_egirth.mp hg a p hp
  have hl' : (3:ℝ)*L≤p.length := by exact_mod_cast hl
  have hw := length_le_three_weight Γ p hp
  linarith
end TorsionFreeZeroDivisors.WeightedGirth
namespace TorsionFreeZeroDivisors.SumGirth
open SimpleGraph
variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
def inlWalk {a b : V} : (G⊕g H).Walk (.inl a) (.inl b) → G.Walk a b
  | .nil => .nil
  | .cons (v:=.inl c) h p => .cons h (inlWalk p)
  | .cons (v:=.inr _) h _ => by cases h
lemma map_inlWalk {a b : V} (p : (G⊕g H).Walk (.inl a) (.inl b)) :
    (inlWalk G H p).map Embedding.sumInl.toHom=p := by
  fun_induction inlWalk G H p
  · rfl
  · rename_i a b c h p ih
    change SimpleGraph.Walk.cons _ ((inlWalk G H p).map Embedding.sumInl.toHom) = _
    rw [ih]
    rfl
  · contradiction
lemma inlWalk_length {a b : V} (p : (G⊕g H).Walk (.inl a) (.inl b)) :
    (inlWalk G H p).length=p.length := by
  calc
    _ = ((inlWalk G H p).map Embedding.sumInl.toHom).length := (SimpleGraph.Walk.length_map _ _).symm
    _ = p.length := congrArg SimpleGraph.Walk.length (map_inlWalk G H p)
lemma inlWalk_cycle {a : V} (p : (G⊕g H).Walk (.inl a) (.inl a)) (hp : p.IsCycle) :
    (inlWalk G H p).IsCycle := by
  rw [←map_inlWalk G H p] at hp
  exact hp.of_map
lemma le_egirth (n : ℕ∞) (hG : n≤G.egirth) (hH : n≤H.egirth) :
    n≤(G⊕g H).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro a p hp
  cases a with
  | inl a =>
    have h := SimpleGraph.le_egirth.mp hG a (inlWalk G H p) (inlWalk_cycle G H p hp)
    simpa only [inlWalk_length] using h
  | inr b =>
    let q : (H⊕g G).Walk (.inl b) (.inl b) := p.map Iso.sumComm.toHom
    have hq : q.IsCycle := hp.map Iso.sumComm.injective
    have h := SimpleGraph.le_egirth.mp hH b (inlWalk H G q) (inlWalk_cycle H G q hq)
    have hl : (inlWalk H G q).length=p.length := (inlWalk_length H G q).trans (p.length_map Iso.sumComm.toHom)
    rw [hl] at h
    exact h
lemma walk_side {a b : V⊕W} (p : (G⊕g H).Walk a b) : a.isLeft=b.isLeft := by
  induction p with
  | nil => rfl
  | @cons a b c h p ih =>
    have hs : a.isLeft=b.isLeft := by cases a <;> cases b <;> first | rfl | cases h
    exact hs.trans ih
lemma diameter (B : ℕ)
    (hG : ∀ a b,G.Reachable a b → G.dist a b≤B)
    (hH : ∀ a b,H.Reachable a b → H.dist a b≤B) :
    ∀ a b,(G⊕g H).Reachable a b → (G⊕g H).dist a b≤B := by
  intro a b ⟨p⟩
  have hs := walk_side G H p
  cases a with
  | inl a =>
    cases b with
    | inr b => cases hs
    | inl b =>
      have hab : G.Reachable a b := ⟨inlWalk G H p⟩
      obtain ⟨q,hq⟩ := hab.exists_walk_length_eq_dist
      exact (SimpleGraph.dist_le (q.map (Embedding.sumInl (H:=H)).toHom)).trans (by
        simpa only [SimpleGraph.Walk.length_map,hq] using hG a b hab)
  | inr a =>
    cases b with
    | inl b => cases hs
    | inr b =>
      let p' : (H⊕g G).Walk (.inl a) (.inl b) := p.map Iso.sumComm.toHom
      have hab : H.Reachable a b := ⟨inlWalk H G p'⟩
      obtain ⟨q,hq⟩ := hab.exists_walk_length_eq_dist
      exact (SimpleGraph.dist_le (q.map (Embedding.sumInr (G:=G)).toHom)).trans (by
        simpa only [SimpleGraph.Walk.length_map,hq] using hH a b hab)
end TorsionFreeZeroDivisors.SumGirth
namespace TorsionFreeZeroDivisors.SumPort

section
open PortSubdivision SimpleGraph
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def graph : PortGraph (VA⊕VB) (DA⊕DB) where
  origin := Sum.map A.origin B.origin
  reverse := Sum.map A.reverse B.reverse
  reverse_reverse := by intro d; cases d <;> simp
  reverse_ne := by
    intro dart equality
    cases dart with
    | inl dart => exact A.reverse_ne dart (Sum.inl.inj equality)
    | inr dart => exact B.reverse_ne dart (Sum.inr.inj equality)
def subdivisionIso : (graph A B).subdivision ≃g A.subdivision⊕g B.subdivision where
  toEquiv := Equiv.sumSumSumComm VA VB DA DB
  map_rel_iff' := by
    intro a b
    rcases a with (a|a)|(a|a) <;> rcases b with (b|b)|(b|b) <;>
      simp [graph,PortGraph.subdivision,Equiv.sumSumSumComm]
lemma girth (n : ℕ∞) (hA : n≤A.subdivision.egirth) (hB : n≤B.subdivision.egirth) :
    n≤(graph A B).subdivision.egirth := by
  rw [(subdivisionIso A B).egirth_eq]
  exact SumGirth.le_egirth _ _ _ hA hB

def side : VA⊕VB → Bool | .inl _ => true | .inr _ => false
lemma side_edge (d : DA⊕DB) : side ((graph A B).origin ((graph A B).reverse d))=side ((graph A B).origin d) := by
  cases d <;> rfl

def leftV (v : SideRestriction.Vertex (@side VA VB) true) : VA :=
  match v with
  | ⟨.inl a,_⟩ => a
  | ⟨.inr _,h⟩ => by cases h
def rightV (v : SideRestriction.Vertex (@side VA VB) false) : VB :=
  match v with
  | ⟨.inr b,_⟩ => b
  | ⟨.inl _,h⟩ => by cases h
lemma leftV_injective : Function.Injective (@leftV VA VB) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · exact Subtype.ext (congrArg Sum.inl h)
  · cases hb
  · cases ha
  · cases ha
lemma rightV_injective : Function.Injective (@rightV VA VB) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · cases ha
  · cases ha
  · cases hb
  · exact Subtype.ext (congrArg Sum.inr h)
end
open PortSubdivision
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
def leftD (d : SideRestriction.Dart (graph A B) side true) : DA :=
  match d with
  | ⟨.inl a,_⟩ => a
  | ⟨.inr _,h⟩ => by cases h
def rightD (d : SideRestriction.Dart (graph A B) side false) : DB :=
  match d with
  | ⟨.inr b,_⟩ => b
  | ⟨.inl _,h⟩ => by cases h
lemma leftD_injective : Function.Injective (leftD A B) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · exact Subtype.ext (congrArg Sum.inl h)
  · cases hb
  · cases ha
  · cases ha
lemma rightD_injective : Function.Injective (rightD A B) := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  cases a <;> cases b
  · cases ha
  · cases ha
  · cases hb
  · exact Subtype.ext (congrArg Sum.inr h)
lemma root_value {V : Type*} (s : V → Bool) (r : Option V) (b : Bool)
    (v : SideRestriction.Vertex s b) (h : SidePins.root s r b=some v) : r=some v.val := by
  cases r with
  | none => cases h
  | some w =>
    dsimp only [SidePins.root,Option.bind_some] at h
    split_ifs at h with hw
    have hv : w=v.val := congrArg Subtype.val (Option.some.inj h)
    rw [hv]
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph

section
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
abbrev VA := Types.VertexA rep
abbrev VB := Types.VertexB rep
abbrev DA := TypedGraphs.Dart (@Types.outgoingA rep)
abbrev DB := TypedGraphs.Dart (@Types.outgoingB rep)
def A : PortGraph (VA rep) (DA rep) := r.1.graph (TypedGraphs.origin (@Types.outgoingA rep))
def B : PortGraph (VB rep) (DB rep) := r.2.graph (TypedGraphs.origin (@Types.outgoingB rep))
def graph := SumPort.graph (A rep r) (B rep r)
def label : DA rep⊕DB rep → Types.Letter := Sum.elim (TypedGraphs.label _) (TypedGraphs.label _)
lemma label_reverse (d : DA rep⊕DB rep) : label rep ((graph rep r).reverse d)=Types.inverse (label rep d) := by
  cases d with
  | inl d => exact r.1.label_reverse d
  | inr d => exact r.2.label_reverse d
lemma immersed (d e : DA rep⊕DB rep)
    (ho : (graph rep r).origin d=(graph rep r).origin e) (hl : label rep d=label rep e) : d=e := by
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (Subtype.ext (Prod.ext (Sum.inl.inj ho) hl))
    | inr e => cases ho
  | inr d =>
    cases e with
    | inl e => cases ho
    | inr e => exact congrArg Sum.inr (Subtype.ext (Prod.ext (Sum.inr.inj ho) hl))
lemma girth (hr : r∈samples rep) : (3*L (size rep):ℕ)≤(graph rep r).subdivision.egirth := by
  have hm := Finset.mem_product.mp hr
  have hA := (Finset.mem_filter.mp hm.1).2.2
  have hB := (Finset.mem_filter.mp hm.2).2.2
  exact SumPort.girth _ _ _ hA hB
lemma weighted_girth (hr : r∈samples rep) :
    ∀ a (p : (graph rep r).subdivision.Walk a a),p.IsCycle →
      (L (size rep):ℝ)≤WeightedCycles.weight (WeightedPortMoore.edgeWeight (fun _ : DA rep⊕DB rep => (1:ℝ))) p :=
  WeightedGirth.weighted_girth _ _ (girth rep r hr)

def embeddingA (root : Option (VA rep⊕VB rep)) (x : VA rep)
    (hr : ∀ z,root=some (.inl z) → z=x) :
    RealizationTransport.Embedding
      (SideRestriction.graph (graph rep r) SumPort.side (SumPort.side_edge _ _) true)
      (fun d => label rep d.val) (@Types.outgoingA rep)
      (RootPins.pin (SidePins.root SumPort.side root true) x) Types.inverse r.1 where
  vertex := ⟨SumPort.leftV,SumPort.leftV_injective⟩
  port := ⟨SumPort.leftD _ _,SumPort.leftD_injective _ _⟩
  origin_eq := by rintro ⟨d,hd⟩; cases d with | inl d => rfl | inr d => cases hd
  label_eq := by rintro ⟨d,hd⟩; cases d with | inl d => rfl | inr d => cases hd
  reverse_eq := by rintro ⟨d,hd⟩; cases d with | inl d => rfl | inr d => cases hd
  pin_eq := by
    apply RootPins.respects
    rintro ⟨v,hv⟩ h
    cases v with
    | inl v => exact hr v (SumPort.root_value SumPort.side root true _ h)
    | inr v => cases hv

def embeddingB (root : Option (VA rep⊕VB rep)) (y : VB rep)
    (hr : ∀ z,root=some (.inr z) → z=y) :
    RealizationTransport.Embedding
      (SideRestriction.graph (graph rep r) SumPort.side (SumPort.side_edge _ _) false)
      (fun d => label rep d.val) (@Types.outgoingB rep)
      (RootPins.pin (SidePins.root SumPort.side root false) y) Types.inverse r.2 where
  vertex := ⟨SumPort.rightV,SumPort.rightV_injective⟩
  port := ⟨SumPort.rightD _ _,SumPort.rightD_injective _ _⟩
  origin_eq := by rintro ⟨d,hd⟩; cases d with | inl d => cases hd | inr d => rfl
  label_eq := by rintro ⟨d,hd⟩; cases d with | inl d => cases hd | inr d => rfl
  reverse_eq := by rintro ⟨d,hd⟩; cases d with | inl d => cases hd | inr d => rfl
  pin_eq := by
    apply RootPins.respects
    rintro ⟨v,hv⟩ h
    cases v with
    | inl v => cases hv
    | inr v => exact hr v (SumPort.root_value SumPort.side root false _ h)
end
open scoped Classical BigOperators
open PortSubdivision ComparedBlocks ComparisonGeometry GirthAsymptotics TypedGraphs ActualPatternEvent
structure BoundedSystem (Bnd K I rep : ℕ) (r : Match rep) (x : VA rep) (y : VB rep) where
  P : Type
  E : Type
  [fP : Fintype P]
  [fE : Fintype E]
  paths : P → List (DA rep⊕DB rep)
  nonempty : ∀ p,paths p≠[]
  root : Option P
  path_bound : Fintype.card P≤K
  comparison_bound : Fintype.card E≤I
  path_chain : ∀ p,(paths p).IsChain (WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse)
  cyclic_chain : ∀ p,StageRoot.cyclic root p=true →
    ∀ᵉ (x∈(paths p).getLast?) (y∈(paths p).head?),
      WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse x y
  length_le : (∑p,(paths p).length:ℕ)≤Bnd*L (size rep)
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
    RawDecomposition.dart paths x≠(graph rep r).reverse (RawDecomposition.dart paths (comparisons.pairing.partner x))
  unpaired_le : ((Finset.univ.filter (fun x => comparisons.pairing.partner x=x)).card:ℝ)≤
    StageFusion.epsilon (1/600) 256*(∑p,(paths p).length:ℕ)
  rootA : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inl z) → z=x
  rootB : ∀ z,root.map (fun p => (graph rep r).origin ((paths p).head (nonempty p)))=some (.inr z) → z=y
  compatible : ∀ p e,comparisons.side p=some e → label rep (RawDecomposition.dart paths p)=
    if comparisons.reverse e then Types.inverse (label rep (RawDecomposition.dart paths (comparisons.pairing.partner p)))
    else label rep (RawDecomposition.dart paths (comparisons.pairing.partner p))
attribute [instance] BoundedSystem.fP BoundedSystem.fE

end TorsionFreeZeroDivisors.SampleGraph

end

end OAI
