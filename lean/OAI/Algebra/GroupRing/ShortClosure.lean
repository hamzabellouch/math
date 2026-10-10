import Mathlib
import OAI.Algebra.GroupRing.BoundedSystem

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.ShortClosure
open scoped Classical
open PortSubdivision WeightedMoore
variable {V D : Type} (Γ : PortGraph V D)

/-- Forgetting loops and multiplicities, only for measuring component distances. -/
def simpleGraph : SimpleGraph V where
  Adj a b := a≠b ∧ ∃ d,Γ.origin d=a ∧ Γ.origin (Γ.reverse d)=b
  symm := ⟨by
    rintro a b ⟨hab,d,ha,hb⟩
    exact ⟨hab.symm,Γ.reverse d,hb,by simpa⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def edgeDart {a b : V} (h : (simpleGraph Γ).Adj a b) : D := h.2.choose
lemma edgeDart_start {a b : V} (h : (simpleGraph Γ).Adj a b) : Γ.origin (edgeDart Γ h)=a :=
  h.2.choose_spec.1
lemma edgeDart_end {a b : V} (h : (simpleGraph Γ).Adj a b) : Γ.origin (Γ.reverse (edgeDart Γ h))=b :=
  h.2.choose_spec.2

def liftWalk {a b : V} : (simpleGraph Γ).Walk a b → List D
  | .nil => []
  | .cons h p => edgeDart Γ h::liftWalk p

lemma liftWalk_length {a b : V} (p : (simpleGraph Γ).Walk a b) : (liftWalk Γ p).length=p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [liftWalk,List.length_cons,SimpleGraph.Walk.length_cons,ih]

lemma liftWalk_start {a b : V} (p : (simpleGraph Γ).Walk a b) :
    ∀ d∈(liftWalk Γ p).head?,Γ.origin d=a := by
  cases p with
  | nil => simp [liftWalk]
  | cons h p =>
    intro d hd
    have hd : d=edgeDart Γ h := by simpa only [liftWalk,List.head?_cons,Option.some.injEq] using hd.symm
    subst d
    exact edgeDart_start Γ h

lemma liftWalk_head_target {a b : V} (p : (simpleGraph Γ).Walk a b) :
    ∀ d∈(liftWalk Γ p).head?,Γ.origin (Γ.reverse d)∈p.support := by
  cases p with
  | nil => simp [liftWalk]
  | @cons a b c h p =>
    intro d hd
    have hd : d=edgeDart Γ h := by simpa only [liftWalk,List.head?_cons,Option.some.injEq] using hd.symm
    subst d
    rw [edgeDart_end]
    exact List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support p)

lemma liftWalk_finish {a b : V} (p : (simpleGraph Γ).Walk a b) : endpoint Γ a (liftWalk Γ p)=b := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change endpoint Γ _ ([edgeDart Γ h]++liftWalk Γ p)=_
    rw [endpoint_append_list]
    change endpoint Γ (Γ.origin (Γ.reverse (edgeDart Γ h))) (liftWalk Γ p)=_
    rw [edgeDart_end]
    exact ih

lemma liftWalk_reduced {a b : V} (p : (simpleGraph Γ).Walk a b) (hp : p.IsPath) :
    ReducedPath Γ a b (liftWalk Γ p) := by
  refine ⟨?_,liftWalk_start Γ p,liftWalk_finish Γ p⟩
  induction p with
  | nil => simp [liftWalk]
  | @cons a b c h p ih =>
    apply (ih hp.of_cons).cons
    intro y hy
    refine ⟨(edgeDart_end Γ h).trans (liftWalk_start Γ p y hy).symm,?_⟩
    intro he
    have hu : a∉p.support := (List.nodup_cons.mp hp.support_nodup).1
    apply hu
    have hm := liftWalk_head_target Γ p y hy
    simpa only [he,PortGraph.reverse_reverse_apply,edgeDart_start] using hm

lemma dart_reachable (d : D) : (simpleGraph Γ).Reachable (Γ.origin d) (Γ.origin (Γ.reverse d)) := by
  by_cases h : Γ.origin d=Γ.origin (Γ.reverse d)
  · exact h ▸ SimpleGraph.Reachable.refl (G:=simpleGraph Γ) (Γ.origin d)
  · exact (show (simpleGraph Γ).Adj _ _ from ⟨h,d,rfl,rfl⟩).reachable

/-- A literal reduced segment stays in one connected component, including when
loops or parallel darts were present in the original port graph. -/
lemma ReducedPath.reachable {a b : V} {l : List D} (hp : ReducedPath Γ a b l) :
    (simpleGraph Γ).Reachable a b := by
  induction l generalizing a with
  | nil => rw [←hp.finish]; exact .refl _
  | cons d l ih =>
    have hs : Γ.origin d=a := hp.start d (by simp)
    have ht : ReducedPath Γ (Γ.origin (Γ.reverse d)) b l := by
      refine ⟨hp.chain.tail,?_,?_⟩
      · intro e he
        exact (hp.chain.rel_head? he).1.symm
      · have he := hp.finish
        change endpoint Γ a ([d]++l)=b at he
        rw [endpoint_append_list] at he
        exact he
    rw [←hs]
    exact (dart_reachable Γ d).trans (ih ht)

/-- Geodesics of the simple shadow lift without backtracking to the actual
multigraph. Thus the previously proved component diameter is the needed one. -/
lemma reduced_return {a b : V} {p : List D} (hp : ReducedPath Γ a b p) :
    ∃ q : List D,ReducedPath Γ b a q ∧ q.length=(simpleGraph Γ).dist b a := by
  obtain ⟨w,hw⟩ := (hp.reachable Γ).symm.exists_walk_length_eq_dist
  exact ⟨liftWalk Γ w,liftWalk_reduced Γ w (w.isPath_of_length_eq_dist hw),(liftWalk_length Γ w).trans hw⟩

variable [Fintype V] [Fintype D]
/-- The entire deterministic closure lemma, with an explicit logarithmic
additive loss. No graph embedding theorem or cyclic cancellation is assumed. -/
theorem short_closure (B : ℕ)
    (hdiam : ∀ a b,(simpleGraph Γ).Reachable a b → (simpleGraph Γ).dist a b≤B)
    (hdeg : ∀ v,7≤(Finset.univ.filter (fun x : D => Γ.origin x=v)).card)
    {a b : V} {p : List D} (hp : ReducedPath Γ a b p) (hpn : p≠[]) :
    ∃ t : List D,t.length≤B+4*(Nat.log 2 (Fintype.card V)+1) ∧
      ReducedPath Γ a a (p++t) ∧
      ∀ᵉ (x∈(p++t).getLast?) (y∈(p++t).head?),PortWalk.step Γ.origin Γ.reverse x y := by
  obtain ⟨q,hq,hql⟩ := reduced_return Γ hp
  obtain ⟨t,ht,hp',hc⟩ := extend_of_return Γ hp hpn hq hdeg
  refine ⟨t,?_,hp',hc⟩
  have hb := hdiam b a (hp.reachable Γ).symm
  omega

end TorsionFreeZeroDivisors.ShortClosure
namespace TorsionFreeZeroDivisors.SumPort
open PortSubdivision
open scoped Classical BigOperators
variable {VA VB DA DB : Type} (A : PortGraph VA DA) (B : PortGraph VB DB)
lemma simple_eq : ShortClosure.simpleGraph (graph A B)=
    ShortClosure.simpleGraph A⊕g ShortClosure.simpleGraph B := by
  ext a b
  rcases a with a|a <;> rcases b with b|b <;>
    simp [ShortClosure.simpleGraph,graph,SimpleGraph.sum,Sum.exists]
variable [Fintype DA] [Fintype DB]
lemma degree_left (v : VA) :
    (Finset.univ.filter (fun d : DA⊕DB => (graph A B).origin d=Sum.inl v)).card=
      (Finset.univ.filter (fun d : DA => A.origin d=v)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp [graph, -Finset.sum_boole]
lemma degree_right (v : VB) :
    (Finset.univ.filter (fun d : DA⊕DB => (graph A B).origin d=Sum.inr v)).card=
      (Finset.univ.filter (fun d : DB => B.origin d=v)).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_sum_type]
  simp [graph, -Finset.sum_boole]
lemma typed_degree {V : Type} [Fintype V] (outgoing : V → Finset Types.Letter) (v : V) :
    (Finset.univ.filter (fun d : TypedGraphs.Dart outgoing => TypedGraphs.origin outgoing d=v)).card=(outgoing v).card := by
  have h := Fintype.card_congr (TypedGraphs.originFiber outgoing v)
  simpa [Fintype.card_subtype] using h
end TorsionFreeZeroDivisors.SumPort
namespace TorsionFreeZeroDivisors.SampleGraph
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings ActualPatternEvent TypedGraphs GirthAsymptotics
variable (rep : ℕ) (r : Match rep)
lemma simple_eq : ShortClosure.simpleGraph (graph rep r)=
    ShortClosure.simpleGraph (A rep r)⊕g ShortClosure.simpleGraph (B rep r) :=
  SumPort.simple_eq (A rep r) (B rep r)
lemma degreeA (v : VA rep) :
    (Finset.univ.filter (fun d : DA rep⊕DB rep => (graph rep r).origin d=Sum.inl v)).card=
      (Types.outgoingA v).card := by
  unfold graph
  have h := (SumPort.degree_left (A rep r) (B rep r) v).trans (SumPort.typed_degree (@Types.outgoingA rep) v)
  convert h using 1
  congr 1
  ext d
  simp
lemma degreeB (v : VB rep) :
    (Finset.univ.filter (fun d : DA rep⊕DB rep => (graph rep r).origin d=Sum.inr v)).card=
      (Types.outgoingB v).card := by
  unfold graph
  have h := (SumPort.degree_right (A rep r) (B rep r) v).trans (SumPort.typed_degree (@Types.outgoingB rep) v)
  convert h using 1
  congr 1
  ext d
  simp
lemma degree (v : VA rep⊕VB rep) :
    129≤(Finset.univ.filter (fun d : DA rep⊕DB rep => (graph rep r).origin d=v)).card := by
  cases v with
  | inl v => rw [degreeA]; exact (Types.degreeA_bounds v).1
  | inr v => rw [degreeB]; exact (Types.degreeB_bounds v).1
lemma diameter (hd : GraphSample.Diameters rep r) :
    ∀ a b,(ShortClosure.simpleGraph (graph rep r)).Reachable a b →
      (ShortClosure.simpleGraph (graph rep r)).dist a b≤TypedDiameter.D₀*L (size rep) := by
  rw [simple_eq]
  exact SumGirth.diameter _ _ _ hd.1 hd.2
lemma card_vertices : Fintype.card (VA rep⊕VB rep)=2*size rep := by
  rw [Fintype.card_sum,Types.card_vertexA,Types.card_vertexB]
  unfold size
  omega
lemma closure_log_bound (n : ℕ) (hL : 1≤L n) :
    4*(Nat.log 2 (2*n)+1)≤1608*L n := by
  have h := TypedDiameter.log_radius_bound n hL
  by_cases hn : n=0
  · subst n; simp only [Nat.mul_zero,Nat.log_zero_right,zero_add]; omega
  · rw [Nat.mul_comm 2 n,Nat.log_mul_base (by omega) hn]
    omega
/-- The short-closure conclusion on the actual sampled two-side graph,
with one uniform fixed constant independent of the segment and n. -/
theorem short_closure (hL : 1≤L (size rep)) (hd : GraphSample.Diameters rep r)
    {a b : VA rep⊕VB rep} {p : List (DA rep⊕DB rep)}
    (hp : ShortClosure.ReducedPath (graph rep r) a b p) (hpn : p≠[]) :
    ∃ t : List (DA rep⊕DB rep),t.length≤(TypedDiameter.D₀+1608)*L (size rep) ∧
      ShortClosure.ReducedPath (graph rep r) a a (p++t) ∧
      ∀ᵉ (x∈(p++t).getLast?) (y∈(p++t).head?),
        WeightedMoore.PortWalk.step (graph rep r).origin (graph rep r).reverse x y := by
  obtain ⟨t,ht,hp',hc⟩ := ShortClosure.short_closure (graph rep r) (TypedDiameter.D₀*L (size rep))
    (diameter rep r hd) (fun v => (by norm_num : 7≤129).trans (degree rep r v)) hp hpn
  refine ⟨t,?_,hp',hc⟩
  rw [card_vertices] at ht
  have hb := closure_log_bound (size rep) hL
  nlinarith
end TorsionFreeZeroDivisors.SampleGraph

namespace TorsionFreeZeroDivisors.RestrictComparisons
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks
variable {T E : Type} {len : T → ℕ} (C : Comparisons (E:=E) len) (keep : T → Prop)

abbrev Length : {t // keep t} → ℕ := fun t => len t.val

def embed (x : Position (Length keep (len:=len))) : Position len := ⟨x.1.val,x.2⟩
def liftPosition (x : Position len) (h : keep x.1) : Position (Length keep (len:=len)) := ⟨⟨x.1,h⟩,x.2⟩
lemma embed_local (x : Position len) (h : keep x.1) : embed keep (liftPosition keep x h)=x := by cases x; rfl
lemma local_embed (x : Position (Length keep (len:=len))) : liftPosition keep (embed keep x) x.1.property=x := by cases x; rfl
lemma embed_injective : Function.Injective (embed keep (len:=len)) := by
  rintro ⟨⟨t,ht⟩,q⟩ ⟨⟨u,hu⟩,r⟩ h
  cases h
  rfl

abbrev Active (e : E) : Prop := keep (C.source e) ∧ keep (C.source (C.flip e))
lemma active_flip (e : E) : Active C keep (C.flip e) ↔ Active C keep e := by
  simp only [Active,C.flip_inv e,and_comm]
def flip (e : {e // Active C keep e}) : {e // Active C keep e} :=
  ⟨C.flip e.val,(active_flip C keep e.val).mpr e.property⟩
lemma flip_inv : Function.Involutive (flip C keep) := by
  intro e
  apply Subtype.ext
  exact C.flip_inv e.val
lemma flip_ne (e : {e // Active C keep e}) : flip C keep e≠e := by
  intro h
  exact C.flip_ne e.val (congrArg Subtype.val h)

def partner (x : Position (Length keep (len:=len))) : Position (Length keep (len:=len)) :=
  if h : keep (C.pairing.partner (embed keep x)).1 then
    liftPosition keep (C.pairing.partner (embed keep x)) h else x
lemma partner_image_yes (x : Position (Length keep (len:=len)))
    (h : keep (C.pairing.partner (embed keep x)).1) :
    embed keep (partner C keep x)=C.pairing.partner (embed keep x) := by
  simp only [partner,dite_eq_left h,embed_local]
lemma partner_no (x : Position (Length keep (len:=len)))
    (h : ¬keep (C.pairing.partner (embed keep x)).1) : partner C keep x=x := by
  simp only [partner,dite_eq_right h]
lemma partner_inv : Function.Involutive (partner C keep) := by
  intro x
  by_cases h : keep (C.pairing.partner (embed keep x)).1
  · have hh : keep (C.pairing.partner (embed keep (partner C keep x))).1 := by
      rw [partner_image_yes C keep x h,C.pairing.involutive]
      exact x.1.property
    apply embed_injective keep
    rw [partner_image_yes C keep _ hh,partner_image_yes C keep x h,C.pairing.involutive]
  · rw [partner_no C keep x h,partner_no C keep x h]

/-- Drop comparisons exactly when either whole path has been deleted. -/
def side (x : Position (Length keep (len:=len))) : Option {e // Active C keep e} :=
  match C.side (embed keep x) with
  | none => none
  | some e => if h : Active C keep e then some ⟨e,h⟩ else none
lemma side_some (x : Position (Length keep (len:=len))) (e : {e // Active C keep e}) :
    side C keep x=some e ↔ C.side (embed keep x)=some e.val := by
  unfold side
  cases h : C.side (embed keep x) with
  | none => simp
  | some f =>
    by_cases hf : Active C keep f
    · simp only [dite_eq_left hf,Option.some.injEq,Subtype.ext_iff]
    · simp only [dite_eq_right hf,reduceCtorEq,false_iff,Option.some.injEq]
      intro he; subst f; exact hf e.property
lemma partner_image_of_side {x : Position (Length keep (len:=len))} {e : {e // Active C keep e}}
    (he : side C keep x=some e) : embed keep (partner C keep x)=C.pairing.partner (embed keep x) := by
  apply partner_image_yes
  rw [C.partner_source _ _ ((side_some C keep x e).mp he)]
  exact e.property.2
lemma side_none (x : Position (Length keep (len:=len))) : side C keep x=none ↔ partner C keep x=x := by
  constructor
  · intro hs
    by_cases hk : keep (C.pairing.partner (embed keep x)).1
    · apply embed_injective keep
      rw [partner_image_yes C keep x hk]
      apply (C.none_iff _).mp
      cases he : C.side (embed keep x) with
      | none => rfl
      | some e =>
        have ha : Active C keep e := by
          constructor
          · rw [←((C.side_iff _ _).mp he).1]; exact x.1.property
          · rwa [←C.partner_source _ _ he]
        have hh := (side_some C keep x ⟨e,ha⟩).mpr he
        rw [hs] at hh
        cases hh
    · exact partner_no C keep x hk
  · intro hp
    cases hs : side C keep x with
    | none => rfl
    | some e =>
      have hh := partner_image_of_side C keep hs
      rw [hp] at hh
      have hn := (C.none_iff _).mpr hh.symm
      have he := (side_some C keep x e).mp hs
      rw [hn] at he
      cases he

def comparisons : Comparisons (E:={e // Active C keep e}) (Length keep (len:=len)) where
  pairing := ⟨partner C keep,partner_inv C keep⟩
  side := side C keep
  flip := flip C keep
  flip_inv := flip_inv C keep
  flip_ne := flip_ne C keep
  side_partner := by
    intro x e he
    apply (side_some C keep _ _).mpr
    rw [partner_image_of_side C keep he]
    exact C.side_partner _ _ ((side_some C keep x e).mp he)
  none_iff := side_none C keep
  source e := ⟨C.source e.val,e.property.1⟩
  lo e := C.lo e.val
  hi e := C.hi e.val
  reverse e := C.reverse e.val
  offset e := C.offset e.val
  side_iff := by
    intro x e
    rw [side_some,C.side_iff]
    simp only [Subtype.ext_iff]
    rfl
  partner_source := by
    intro x e he
    apply Subtype.ext
    have hh := congrArg Sigma.fst (partner_image_of_side C keep he)
    exact hh.trans (C.partner_source _ _ ((side_some C keep x e).mp he))
  partner_coordinate := by
    intro x e he
    have hh := congrArg (fun x : Position len => x.2.val) (partner_image_of_side C keep he)
    exact hh.trans (C.partner_coordinate _ _ ((side_some C keep x e).mp he))
  target_range e := C.target_range e.val

/-- A new fixed position was either already fixed or points to a deleted path.
This is an exact dichotomy of literal occurrence indices. -/
lemma fixed_iff (x : Position (Length keep (len:=len))) :
    partner C keep x=x ↔ C.pairing.partner (embed keep x)=embed keep x ∨
      ¬keep (C.pairing.partner (embed keep x)).1 := by
  constructor
  · intro hx
    by_cases h : keep (C.pairing.partner (embed keep x)).1
    · left
      have hh := partner_image_yes C keep x h
      rw [hx] at hh
      exact hh.symm
    · exact Or.inr h
  · rintro (h|h)
    · apply embed_injective keep
      have hk : keep (C.pairing.partner (embed keep x)).1 := by rw [h]; exact x.1.property
      rw [partner_image_yes C keep x hk,h]
    · exact partner_no C keep x h

variable [Fintype T]
lemma deleted_partner_card :
    (Finset.univ.filter (fun x : Position (Length keep (len:=len)) =>
      ¬keep (C.pairing.partner (embed keep x)).1)).card ≤
      (Finset.univ.filter (fun x : Position len => ¬keep x.1)).card := by
  apply Finset.card_le_card_of_injOn (fun x => C.pairing.partner (embed keep x))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    apply embed_injective keep
    have hi : Function.Injective C.pairing.partner := C.pairing.involutive.injective
    exact hi h
lemma old_fixed_card :
    (Finset.univ.filter (fun x : Position (Length keep (len:=len)) =>
      C.pairing.partner (embed keep x)=embed keep x)).card ≤
      (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card := by
  apply Finset.card_le_card_of_injOn (embed keep)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact embed_injective keep h
lemma fixed_card :
    (Finset.univ.filter (fun x : Position (Length keep (len:=len)) =>
      partner C keep x=x)).card ≤
      (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card+
      (Finset.univ.filter (fun x : Position len => ¬keep x.1)).card := by
  have he : (Finset.univ.filter (fun x : Position (Length keep (len:=len)) => partner C keep x=x))=
      (Finset.univ.filter (fun x : Position (Length keep (len:=len)) => C.pairing.partner (embed keep x)=embed keep x)) ∪
      (Finset.univ.filter (fun x : Position (Length keep (len:=len)) => ¬keep (C.pairing.partner (embed keep x)).1)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,fixed_iff]
  rw [he]
  exact (Finset.card_union_le _ _).trans (add_le_add (old_fixed_card C keep) (deleted_partner_card C keep))
lemma deleted_nonfixed_partner_card :
    (Finset.univ.filter (fun x : Position (Length keep (len:=len)) =>
      ¬keep (C.pairing.partner (embed keep x)).1)).card ≤
      (Finset.univ.filter (fun x : Position len => ¬keep x.1 ∧ C.pairing.partner x≠x)).card := by
  apply Finset.card_le_card_of_injOn (fun x => C.pairing.partner (embed keep x))
  · intro x hx
    have hd := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,?_⟩
    intro hf
    rw [C.pairing.involutive] at hf
    change embed keep x=C.pairing.partner (embed keep x) at hf
    rw [←hf] at hd
    exact hd x.1.property
  · intro x _ y _ h
    apply embed_injective keep
    exact C.pairing.involutive.injective h
lemma fixed_card_sharp :
    (Finset.univ.filter (fun x : Position (Length keep (len:=len)) =>
      partner C keep x=x)).card ≤
      (Finset.univ.filter (fun x : Position len => C.pairing.partner x=x)).card+
      (Finset.univ.filter (fun x : Position len => ¬keep x.1 ∧ C.pairing.partner x≠x)).card := by
  have he : (Finset.univ.filter (fun x : Position (Length keep (len:=len)) => partner C keep x=x))=
      (Finset.univ.filter (fun x : Position (Length keep (len:=len)) => C.pairing.partner (embed keep x)=embed keep x)) ∪
      (Finset.univ.filter (fun x : Position (Length keep (len:=len)) => ¬keep (C.pairing.partner (embed keep x)).1)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,fixed_iff]
  rw [he]
  exact (Finset.card_union_le _ _).trans (add_le_add (old_fixed_card C keep) (deleted_nonfixed_partner_card C keep))
end TorsionFreeZeroDivisors.RestrictComparisons

end

end OAI
