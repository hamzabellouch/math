import OAI.Probability.FKMaps.CornerInverse

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma StackMatching.empty_interval_preserves {w : α→TypedLetter} {u v z : List α}
    (M : StackMatching w (u++(v++z))) (hn : (u++(v++z)).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) :
    (∀ d,M.mate d∈v ↔ d∈v) ∧ (∀ d,turns M.first d∈v ↔ d∈v) := by
  have hm (d : α) (hd : d∈v) : turns (M.first++M.second) d∈v := by
    exact empty_interval_matching_closed w u v z hn M.first M.second
      M.first_arches M.second_arches M.covers M.first_types M.second_types hv d hd
  have hn' : (endpoints (M.first++M.second)).Nodup := M.covers.nodup_iff.mpr hn
  exact ⟨turns_sublist_preserves hn' (List.Sublist.refl _) hm,
    turns_sublist_preserves hn' (List.sublist_append_left _ _) hm⟩

omit [Fintype α] in
lemma formPerm_append_comm (v z : List α) (hn : (v++z).Nodup) :
    (v++z).formPerm=(z++v).formPerm := by
  have h := List.formPerm_rotate (v++z) hn v.length
  rw [List.rotate_append_length_eq] at h
  exact h.symm

omit [Fintype α] in
/-- Cutting any nonempty successful insertion interval is a literal
one-vertex split of the original rotation. No random root/rotation is used. -/
lemma StackMatching.empty_interval_rotation {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hcomp : z++u=b::R) :
    (u++((a::L)++z)).formPerm*turns M.first=
      swap a b*((a::L).formPerm*(b::R).formPerm*turns M.first) := by
  have he : (u++((a::L)++z)).formPerm=((a::L)++(b::R)).formPerm := by
    rw [formPerm_append_comm u _ hn,List.append_assoc,hcomp]
  have hh : ((a::L)++(b::R)).Nodup := by
    rw [← hcomp,← List.append_assoc]
    exact (List.perm_append_comm).nodup_iff.mp hn
  rw [he]
  have h := formPerm_cut a b L R (by simpa only [List.cons_append] using hh)
  change (a::(L++b::R)).formPerm*turns M.first=_
  rw [h]
  simp only [mul_assoc]

/-- The two graph pieces retain every edge, including both matching colours.
This is the actual all-edge graph at an arbitrary insertion interval. -/
def StackMatching.empty_interval_wedge {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R) :
    let p := (a::L).formPerm*(b::R).formPerm*turns M.first
    let S : Set α := {d | d∈a::L}
    GraphWedge.Data (sideGraph M.mate p S (M.empty_interval_preserves hn hv).1)
      (sideGraph M.mate p Sᶜ (fun d => not_congr ((M.empty_interval_preserves hn hv).1 d)))
      (dartGraph M.mate (swap a b*p)) := by
  let S : Set α := {d | d∈a::L}
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  have hh : ((a::L)++(b::R)).Nodup := by
    rw [← hcomp,← List.append_assoc]
    exact List.perm_append_comm.nodup_iff.mp hn
  have hd : (a::L).Disjoint (b::R) := List.disjoint_iff_ne.mpr (List.nodup_append.mp hh).2.2
  have hpres := M.empty_interval_preserves hn hv
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  exact PermutationWedge.data hp (by simp [S])
    (fun hb => List.disjoint_left.mp hd hb (by simp)) hpres.1

/-- The first dart following the successful subword and its first dart are
literally in the same original rotation vertex. This is the pole identity. -/
theorem StackMatching.empty_interval_pole {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R) :
    vertex ((u++((a::L)++z)).formPerm*turns M.first) a=
      vertex ((u++((a::L)++z)).formPerm*turns M.first) b := by
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  let D := M.empty_interval_wedge u L z a b R hn hv hcomp
  have hD := D.shared
  dsimp only [D,StackMatching.empty_interval_wedge,PermutationWedge.data,
    PermutationWedge.inclusionHom,PermutationWedge.flipInclusionHom,
    PermutationWedge.inclusion,PermutationWedge.flipInclusion,sideMk] at hD
  exact hD

end FKCRT.Inventory
end


noncomputable section
open Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
variable {α : Type*} [Fintype α]
attribute [local instance] Classical.propDecidable

lemma sameCycle_congr_on {p q : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (_hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d∈S,p d=q d) {x y : α} (hx : x∈S) :
    p.SameCycle x y ↔ q.SameCycle x y := by
  have hpow : ∀ n : ℕ,(p^n) x=(q^n) x ∧ (p^n) x∈S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      simp only [pow_succ',mul_apply]
      exact ⟨(he _ ih.2).trans (congrArg q ih.1),(hp _).mpr ih.2⟩
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by simpa only [zpow_natCast] using (hpow n).1.symm.trans hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n:ℤ),by simpa only [zpow_natCast] using (hpow n).1.trans hn⟩

/-- Changing the ambient permutation off a retained invariant dart set does
not change its actual rotation vertices. -/
def sideCongr {p q : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d∈S,p d=q d) : Side p S ≃ Side q S :=
  Quotient.congrRight (fun x _ => sameCycle_congr_on hp hq he x.property)

lemma sideCongr_mk {p q : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d∈S,p d=q d) (d : α) (hd : d∈S) :
    sideCongr hp hq he (sideMk p S d hd)=sideMk q S d hd := rfl

/-- The all-edge graph is invariant under restriction/normalization on a
closed set of darts; only the two literal permutation actions are used. -/
def sideGraphCongr {p q e f : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (hq : ∀ d,q d∈S ↔ d∈S)
    (he : ∀ d,e d∈S ↔ d∈S) (hf : ∀ d,f d∈S ↔ d∈S)
    (hpq : ∀ d∈S,p d=q d) (hef : ∀ d∈S,e d=f d) :
    sideGraph e p S he ≃g sideGraph f q S hf where
  toEquiv := sideCongr hp hq hpq
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne (congrArg (sideCongr hp hq hpq) h),?_⟩
      have transport (x y : Side p S) (d : α) (hd : d∈S)
          (hx : sideMk q S d hd=sideCongr hp hq hpq x)
          (hy : sideMk q S (f d) ((hf d).mpr hd)=sideCongr hp hq hpq y) :
          ∃ d,∃ hd : d∈S,sideMk p S d hd=x ∧ sideMk p S (e d) ((he d).mpr hd)=y := by
        refine ⟨d,hd,(sideCongr hp hq hpq).injective hx,?_⟩
        apply (sideCongr hp hq hpq).injective
        rw [sideCongr_mk]
        simpa only [hef d hd] using hy
      rcases h with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
      · exact Or.inl (transport x y d hd hx hy)
      · exact Or.inr (transport y x d hd hy hx)
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne ((sideCongr hp hq hpq).injective h),?_⟩
      have transport (x y : Side p S) (d : α) (hd : d∈S)
          (hx : sideMk p S d hd=x) (hy : sideMk p S (e d) ((he d).mpr hd)=y) :
          ∃ d,∃ hd : d∈S,sideMk q S d hd=sideCongr hp hq hpq x ∧
            sideMk q S (f d) ((hf d).mpr hd)=sideCongr hp hq hpq y := by
        refine ⟨d,hd,congrArg (sideCongr hp hq hpq) hx,?_⟩
        have hh := congrArg (sideCongr hp hq hpq) hy
        simpa only [sideCongr_mk,hef d hd] using hh
      rcases h with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
      · exact Or.inl (transport x y d hd hx hy)
      · exact Or.inr (transport y x d hd hy hx)

def fullInclusion (p : Perm α) (S : Set α) : Side p S→Vertex p :=
  Quotient.lift (fun d => vertex p d.val) (fun _ _ h => Quotient.sound h)

omit [Fintype α] in
lemma fullInclusion_mk (p : Perm α) (S : Set α) (d : α) (hd : d∈S) :
    fullInclusion p S (sideMk p S d hd)=vertex p d := rfl

omit [Fintype α] in
lemma fullInclusion_injective (p : Perm α) (S : Set α) :
    Function.Injective (fullInclusion p S) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro h
      apply Quotient.sound
      change vertex p x.val=vertex p y.val at h
      have hh : p.SameCycle x.val y.val := Quotient.exact h
      exact hh

lemma fullRetract_wellDefined {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) {x y : α}
    (hxy : p.SameCycle x y) :
    (if hx : x∈S then sideMk p S x hx else sideMk p S a ha)=
      (if hy : y∈S then sideMk p S y hy else sideMk p S a ha) := by
  classical
  have hh := MapCycles.sameCycle_partition hp hxy
  by_cases hx : x∈S
  · rw [dite_eq_left hx,dite_eq_left (hh.mp hx)]
    exact Quotient.sound hxy
  · rw [dite_eq_right hx,dite_eq_right (fun h => hx (hh.mpr h))]

def fullRetract {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) : Vertex p→Side p S := by
  classical
  exact Quotient.lift (fun d => if hd : d∈S then sideMk p S d hd else sideMk p S a ha)
    (fun _ _ h => fullRetract_wellDefined hp a ha h)

lemma fullRetract_mk {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) (d : α) :
    fullRetract hp a ha (vertex p d)=
      (if hd : d∈S then sideMk p S d hd else sideMk p S a ha) := by
  classical
  rfl

lemma fullRetract_inclusion {p : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (a : α) (ha : a∈S) (x : Side p S) :
    fullRetract hp a ha (fullInclusion p S x)=x := by
  induction x using Quotient.inductionOn with
  | h d => exact dite_eq_left d.property

def fullInclusionHom {p e : Perm α} {S : Set α}
    (he : ∀ d,e d∈S ↔ d∈S) : sideGraph e p S he →g dartGraph e p where
  toFun := fullInclusion p S
  map_rel' := by
    intro x y hxy
    refine ⟨fun h => hxy.1 (fullInclusion_injective p S h),?_⟩
    rcases hxy.2 with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
    · exact Or.inl ⟨d,congrArg (fullInclusion p S) hx,congrArg (fullInclusion p S) hy⟩
    · exact Or.inr ⟨d,congrArg (fullInclusion p S) hy,congrArg (fullInclusion p S) hx⟩

lemma fullRetract_edge {p e : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (he : ∀ d,e d∈S ↔ d∈S) (a : α) (ha : a∈S)
    {x y : Vertex p} (hxy : (dartGraph e p).Adj x y) :
    (sideGraph e p S he).edist (fullRetract hp a ha x) (fullRetract hp a ha y)≤1 := by
  classical
  have forward (d : α) (hne : vertex p d≠vertex p (e d)) :
      (sideGraph e p S he).edist (fullRetract hp a ha (vertex p d))
        (fullRetract hp a ha (vertex p (e d)))≤1 := by
    rw [fullRetract_mk,fullRetract_mk]
    by_cases hd : d∈S
    · rw [dite_eq_left hd,dite_eq_left ((he d).mpr hd)]
      apply (SimpleGraph.edist_eq_one_iff_adj.mpr ?_).le
      refine ⟨fun h => hne (congrArg (fullInclusion p S) h),Or.inl ⟨d,hd,rfl,rfl⟩⟩
    · rw [dite_eq_right hd,dite_eq_right (fun h => hd ((he d).mp h)),SimpleGraph.edist_self]
      exact zero_le_one
  rcases hxy.2 with ⟨d,rfl,rfl⟩|⟨d,rfl,rfl⟩
  · exact forward d hxy.1
  · rw [SimpleGraph.edist_comm]
    exact forward d hxy.1.symm

/-- Other invariant components, including isolated deleted darts, cannot
shorten distances in a retained component. -/
theorem fullInclusion_edist {p e : Perm α} {S : Set α}
    (hp : ∀ d,p d∈S ↔ d∈S) (he : ∀ d,e d∈S ↔ d∈S)
    (x y : Side p S) :
    (dartGraph e p).edist (fullInclusion p S x) (fullInclusion p S y)=
      (sideGraph e p S he).edist x y := by
  apply le_antisymm (GraphWedge.hom_edist_le (fullInclusionHom he) x y)
  obtain ⟨a,ha⟩ := Quotient.exists_rep x
  have h := GraphWedge.retraction_pair_edist_le (sideGraph e p S he)
    (⊥ : SimpleGraph Unit) (dartGraph e p) (fullRetract hp a.val a.property)
    (fun _ => ()) (by
      intro u v huv
      simpa only [SimpleGraph.edist_self,add_zero] using fullRetract_edge hp he a.val a.property huv)
    (fullInclusion p S x) (fullInclusion p S y)
  change (sideGraph e p S he).edist x y≤
    (dartGraph e p).edist (fullInclusion p S x) (fullInclusion p S y)
  simpa only [fullRetract_inclusion,SimpleGraph.edist_self,add_zero] using h

end FKCRT.PermutationWedge
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Chords
variable {N K : ℕ}

/-- Reachability lifts through a strictly increasing matching embedding
whenever its image contains the whole component being lifted. -/
theorem reachable_lift (a : Perm (Fin N)) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (hmatch : ∀ i,a (e i)=e (b i))
    (r : Opener b)
    (himage : ∀ x : Opener a,(graph a).Reachable (openerEmbedding a b e hmatch r) x →
      x.val∈Set.range e) :
    ∀ x : Opener a,(graph a).Reachable (openerEmbedding a b e hmatch r) x →
      ∃ y : Opener b,openerEmbedding a b e hmatch y=x ∧ (graph b).Reachable r y := by
  intro x hx
  have hh := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hx
  induction hh with
  | refl => exact ⟨r,rfl,SimpleGraph.Reachable.refl r⟩
  | @tail x z hpath hadj ih =>
    obtain ⟨y,hy,hry⟩ := ih ((SimpleGraph.reachable_iff_reflTransGen _ _).mpr hpath)
    have hz : (graph a).Reachable (openerEmbedding a b e hmatch r) z :=
      ((SimpleGraph.reachable_iff_reflTransGen _ _).mpr hpath).trans hadj.reachable
    obtain ⟨v,hv⟩ := opener_range a b e hmatch z (himage z hz)
    refine ⟨v,hv,hry.trans ?_⟩
    apply SimpleGraph.Adj.reachable
    exact (cross_embedding a b e hmatch y v).mp (by rw [hy,hv];exact hadj)

theorem component_compression (a : Perm (Fin N)) (ha : Function.Involutive a) (b : Perm (Fin K))
    (e : Fin K ↪o Fin N) (hmatch : ∀ i,a (e i)=e (b i))
    (r : Opener b)
    (himage : Set.range e={d | d∈componentDarts a (openerEmbedding a b e hmatch r)}) :
    ∀ x : Opener b,(graph b).Reachable r x := by
  intro x
  have hx : (e x.val)∈componentDarts a (openerEmbedding a b e hmatch r) := by
    change e x.val∈({d | d∈componentDarts a (openerEmbedding a b e hmatch r)} : Set (Fin N))
    rw [← himage];exact Set.mem_range_self _
  have hxa : (graph a).Reachable (openerEmbedding a b e hmatch r)
      (openerEmbedding a b e hmatch x) := by
    obtain ⟨y,hy,he|he⟩ := (mem_componentDarts _ _ _).mp hx
    · have hy' : y=openerEmbedding a b e hmatch x := Subtype.ext he.symm
      exact hy' ▸ hy
    · have hxp := e.strictMono x.property
      rw [← hmatch,he] at hxp
      rw [ha] at hxp
      exact False.elim ((not_lt_of_ge y.property.le) hxp)
  obtain ⟨v,hv,hrv⟩ := reachable_lift a b e hmatch r (by
    intro y hy
    rw [himage]
    exact (mem_componentDarts _ _ _).mpr ⟨y,hy,Or.inl rfl⟩)
    (openerEmbedding a b e hmatch x) hxa
  exact (openerEmbedding a b e hmatch).injective hv ▸ hrv

end FKCRT.Chords
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory.StackMatching
open MapCycles
variable {α : Type*} [DecidableEq α] {w : α→TypedLetter} {l : List α}

lemma pair_mask (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) : ∀ e∈M.first++M.second,p e.1=p e.2 := by
  intro e he
  have hh := hp e.1 (M.endpoints_mem e he).1
  rw [mate,(turns_pair (M.covers.nodup_iff.mpr hn) e he).1] at hh
  exact hh.symm

def filter (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) : StackMatching w (l.filter p) where
  first := M.first.filter (fun e => p e.1)
  second := M.second.filter (fun e => p e.1)
  first_arches := M.first_arches.filter p (fun e he =>
    M.pair_mask hn p hp e (List.mem_append_left _ he))
  second_arches := M.second_arches.filter p (fun e he =>
    M.pair_mask hn p hp e (List.mem_append_right _ he))
  covers := by
    rw [← List.filter_append,endpoints_filter p _ (M.pair_mask hn p hp)]
    exact M.covers.filter p
  first_types := fun e he => M.first_types e (List.mem_filter.mp he).1
  second_types := fun e he => M.second_types e (List.mem_filter.mp he).1

lemma filter_mate (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hi : i∈l) (hpi : p i=true) :
    (M.filter hn p hp).mate i=M.mate i := by
  have hnp := M.covers.nodup_iff.mpr hn
  have hnf := (M.filter hn p hp).covers.nodup_iff.mpr (hn.filter p)
  obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp (M.covers.mem_iff.mpr hi)
  · have hmem : e∈(M.filter hn p hp).first++(M.filter hn p hp).second := by
      change e∈M.first.filter (fun e => p e.1)++M.second.filter (fun e => p e.1)
      rw [← List.filter_append]
      exact List.mem_filter.mpr ⟨he,hpi⟩
    exact (turns_pair hnf e hmem).1.trans (turns_pair hnp e he).1.symm
  · have hmem : e∈(M.filter hn p hp).first++(M.filter hn p hp).second := by
      change e∈M.first.filter (fun e => p e.1)++M.second.filter (fun e => p e.1)
      rw [← List.filter_append]
      exact List.mem_filter.mpr ⟨he,(M.pair_mask hn p hp e he).trans hpi⟩
    exact (turns_pair hnf e hmem).2.trans (turns_pair hnp e he).2.symm

end FKCRT.Inventory.StackMatching
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.MapCycles
variable {α : Type*} [DecidableEq α]

lemma turns_filter_on (E : List (α×α)) (hn : (endpoints E).Nodup)
    (p : α→Bool) (hp : ∀ e∈E,p e.1=p e.2) (d : α) (hd : p d=true) :
    turns (E.filter (fun e => p e.1)) d=turns E d := by
  have hs : E.filter (fun e => p e.1)<+E := List.filter_sublist
  have hn' := hn.sublist (hs.flatMap _)
  by_cases hm : d∈endpoints E
  · obtain ⟨e,he,rfl|rfl⟩ := mem_endpoints.mp hm
    · have hf : e∈E.filter (fun e => p e.1) := List.mem_filter.mpr ⟨he,hd⟩
      exact (turns_pair hn' e hf).1.trans (turns_pair hn e he).1.symm
    · have hf : e∈E.filter (fun e => p e.1) := List.mem_filter.mpr ⟨he,(hp e he).trans hd⟩
      exact (turns_pair hn' e hf).2.trans (turns_pair hn e he).2.symm
  · rw [turns_fixed_of_notMem hm,turns_fixed_of_notMem]
    exact fun h => hm ((hs.flatMap _).subset h)

omit [DecidableEq α] in
lemma perm_preserves_of_fixed {p : Perm α} {S : Set α} (h : ∀ d∈S,p d=d) :
    ∀ d,p d∈S ↔ d∈S := by
  intro d
  constructor
  · intro hd
    have hh : p (p d)=p d := h _ hd
    exact p.injective hh ▸ hd
  · intro hd
    simpa only [h d hd] using hd

end FKCRT.MapCycles
namespace FKCRT.Inventory.StackMatching
open MapCycles
variable {α : Type*} [DecidableEq α] {w : α→TypedLetter} {l : List α}

lemma filter_first (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=true) :
    turns (M.filter hn p hp).first i=turns M.first i := by
  have hE : (endpoints M.first).Nodup :=
    (M.covers.nodup_iff.mpr hn).sublist ((List.sublist_append_left _ _).flatMap _)
  exact turns_filter_on M.first hE p (fun e he => M.pair_mask hn p hp e (List.mem_append_left _ he)) i hpi

lemma filter_mate_on (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=true) :
    (M.filter hn p hp).mate i=M.mate i := by
  change turns (M.first.filter (fun e => p e.1)++M.second.filter (fun e => p e.1)) i=_
  rw [← List.filter_append]
  exact turns_filter_on _ (M.covers.nodup_iff.mpr hn) p (M.pair_mask hn p hp) i hpi

lemma filter_mate_fixed (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=false) :
    (M.filter hn p hp).mate i=i := by
  apply turns_fixed_of_notMem
  intro h
  have hh := (M.filter hn p hp).covers.mem_iff.mp h
  exact Bool.noConfusion (hpi.symm.trans (List.mem_filter.mp hh).2)

lemma filter_first_fixed (M : StackMatching w l) (hn : l.Nodup) (p : α→Bool)
    (hp : ∀ d∈l,p (M.mate d)=p d) (i : α) (hpi : p i=false) :
    turns (M.filter hn p hp).first i=i := by
  apply turns_fixed_of_notMem
  intro h
  have h' : i∈endpoints ((M.filter hn p hp).first++(M.filter hn p hp).second) := by
    rw [endpoints_append]
    exact List.mem_append_left _ h
  have hf := (M.filter hn p hp).covers.mem_iff.mp h'
  exact Bool.noConfusion (hpi.symm.trans (List.mem_filter.mp hf).2)

end FKCRT.Inventory.StackMatching
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.GraphWedge
lemma iso_edist {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (E : G ≃g H) (x y : α) : H.edist (E x) (E y)=G.edist x y := by
  apply le_antisymm (hom_edist_le E.toHom x y)
  simpa using hom_edist_le E.symm.toHom (E x) (E y)
end FKCRT.GraphWedge
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma filter_delete_interval (u v z : List α) (hn : (u++(v++z)).Nodup) :
    (u++(v++z)).filter (fun d => decide (d∉v))=u++z := by
  have hu : u.Disjoint v := List.disjoint_iff_ne.mpr (fun x hx y hy he =>
    (List.nodup_append.mp hn).2.2 x hx y (List.mem_append_left _ hy) he)
  have hz : v.Disjoint z := List.disjoint_iff_ne.mpr
    (List.nodup_append.mp (List.nodup_append.mp hn).2.1).2.2
  simp only [List.filter_append]
  have hfU : u.filter (fun d => decide (d∉v))=u := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (fun h => List.disjoint_left.mp hu hd h)
  have hfV : v.filter (fun d => decide (d∉v))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hd
    simp [hd]
  have hfZ : z.filter (fun d => decide (d∉v))=z := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true (fun h => List.disjoint_left.mp hz h hd)
  rw [hfU,hfV,hfZ,List.nil_append]

/-- The actual retained matching after a successful insertion is erased. -/
def StackMatching.deleteInterval {w : α→TypedLetter} {u v z : List α}
    (M : StackMatching w (u++(v++z))) (hn : (u++(v++z)).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) : StackMatching w (u++z) := by
  have hpres := (M.empty_interval_preserves hn hv).1
  let keep : α→Bool := fun d => decide (d∉v)
  have hk : ∀ d∈u++(v++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact not_congr (hpres d)
  exact filter_delete_interval u v z hn ▸ M.filter hn keep hk

omit [Fintype α] [DecidableEq α] in
lemma StackMatching.cast_first {w : α→TypedLetter} {l l' : List α}
    (h : l=l') (M : StackMatching w l) : (h ▸ M).first=M.first := by cases h;rfl

/-- Removing any genuine successful interval preserves *all-edge* distances
between retained darts, not just spanning-tree distances. The resulting
rotation is that of the original ordered word with the interval deleted. -/
theorem StackMatching.delete_interval_distance {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (x y : α) (hx : x∉a::L) (hy : y∉a::L) :
    let D := M.deleteInterval hn hv
    let s := (u++((a::L)++z)).formPerm*turns M.first
    let r := (u++z).formPerm*turns D.first
    (dartGraph M.mate s).edist (vertex s x) (vertex s y)=
      (dartGraph D.mate r).edist (vertex r x) (vertex r y) := by
  let S : Set α := {d | d∈a::L}
  let keep : α→Bool := fun d => decide (d∉a::L)
  have hpres := M.empty_interval_preserves hn hv
  have hk : ∀ d∈u++((a::L)++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact not_congr (hpres.1 d)
  let D := M.deleteInterval hn hv
  have hDfirst : D.first=(M.filter hn keep hk).first := StackMatching.cast_first _ _
  have hDmate : D.mate=(M.filter hn keep hk).mate := StackMatching.cast_mate _ _
  have hd : (a::L).Disjoint (b::R) := by
    have hh : ((a::L)++(b::R)).Nodup := by
      rw [← hcomp,← List.append_assoc]
      exact List.perm_append_comm.nodup_iff.mp hn
    exact List.disjoint_iff_ne.mpr (List.nodup_append.mp hh).2.2
  have hnu : (u++z).Nodup := by
    exact hn.sublist (List.Sublist.append (List.Sublist.refl u) (List.sublist_append_right _ _))
  have hrotate : (u++z).formPerm=(b::R).formPerm := by
    rw [formPerm_append_comm u z hnu,hcomp]
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  let r := (u++z).formPerm*turns D.first
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  have hfixed (d : α) (hd' : d∈a::L) : r d=d := by
    have hf : turns D.first d=d := by
      rw [hDfirst]
      exact M.filter_first_fixed hn keep hk d (by simp only [keep,decide_eq_false_iff_not,not_not];exact hd')
    simp only [r,mul_apply,hf,hrotate]
    exact List.formPerm_apply_of_notMem (fun h => List.disjoint_left.mp hd hd' h)
  have hr : ∀ d,r d∈S ↔ d∈S := perm_preserves_of_fixed hfixed
  have hep : ∀ d,D.mate d∈S ↔ d∈S := by
    apply perm_preserves_of_fixed
    intro d hd'
    rw [hDmate]
    exact M.filter_mate_fixed hn keep hk d (by simp only [keep,decide_eq_false_iff_not,not_not];exact hd')
  have hpq (d : α) (hd' : d∈Sᶜ) : p d=r d := by
    have hf : turns D.first d=turns M.first d := by
      rw [hDfirst]
      exact M.filter_first hn keep hk d (by exact decide_eq_true hd')
    have hnd : turns M.first d∉a::L := fun h => hd' ((hpres.2 d).mp h)
    have hnr : (b::R).formPerm (turns M.first d)∉a::L := fun h => hnd ((formPerm_other_mem_iff hd _).mp h)
    simp only [p,r,mul_apply,hf,hrotate,List.formPerm_apply_of_notMem hnr]
  have hef (d : α) (hd' : d∈Sᶜ) : M.mate d=D.mate d := by
    rw [hDmate]
    exact (M.filter_mate_on hn keep hk d (by exact decide_eq_true hd')).symm
  let E := sideGraphCongr (fun d => not_congr (hp d)) (fun d => not_congr (hr d))
    (fun d => not_congr (hpres.1 d)) (fun d => not_congr (hep d)) hpq hef
  dsimp only
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  change (dartGraph M.mate (swap a b*p)).edist _ _=(dartGraph D.mate r).edist _ _
  calc
    _=(sideGraph M.mate p Sᶜ (fun d => not_congr (hpres.1 d))).edist
      (sideMk p Sᶜ x hx) (sideMk p Sᶜ y hy) :=
        (M.empty_interval_wedge u L z a b R hn hv hcomp).edist_right _ _
    _=(sideGraph D.mate r Sᶜ (fun d => not_congr (hep d))).edist
      (sideMk r Sᶜ x hx) (sideMk r Sᶜ y hy) := (GraphWedge.iso_edist E _ _).symm
    _=_ := (fullInclusion_edist (fun d => not_congr (hr d))
      (fun d => not_congr (hep d)) (sideMk r Sᶜ x hx) (sideMk r Sᶜ y hy)).symm

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Each genuine inserted successful word has precisely one metric gate in
its complement in the original all-edge map. This equality is in the original
graph, not an independently postulated block-tree metric. -/
theorem StackMatching.empty_interval_gate {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (x y : α) (hx : x∈a::L) (hy : y∉a::L) :
    let s := (u++((a::L)++z)).formPerm*turns M.first
    (dartGraph M.mate s).edist (vertex s x) (vertex s y)=
      (dartGraph M.mate s).edist (vertex s x) (vertex s a)+
      (dartGraph M.mate s).edist (vertex s a) (vertex s y) := by
  dsimp only
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  let S : Set α := {d | d∈a::L}
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  let D := M.empty_interval_wedge u L z a b R hn hv hcomp
  let xx := sideMk p S x hx
  let yy := sideMk p Sᶜ y hy
  change _ = _+_
  have hl := D.edist_left xx D.poleLeft
  have hr := D.edist_right D.poleRight yy
  have hc := D.edist_cross xx yy
  rw [← D.shared] at hr
  dsimp only [D,StackMatching.empty_interval_wedge,PermutationWedge.data,
    PermutationWedge.inclusionHom,PermutationWedge.flipInclusionHom,
    PermutationWedge.inclusion,PermutationWedge.flipInclusion,xx,yy] at hl hr hc
  exact hc.trans (congrArg₂ (·+·) hl.symm hr.symm)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
lemma complement_disjoint_interval (u v z : List α) (hn : (u++(v++z)).Nodup) :
    (u++z).Disjoint v := by
  apply List.disjoint_append_left.mpr
  constructor
  · apply List.disjoint_iff_ne.mpr
    intro x hx y hy h
    exact (List.nodup_append.mp hn).2.2 x hx y (List.mem_append_left _ hy) h
  · exact (List.disjoint_iff_ne.mpr
      (List.nodup_append.mp (List.nodup_append.mp hn).2.1).2.2).symm

/-- A notation for the actual original all-edge distance of a typed matching. -/
def StackMatching.distance {w : α→TypedLetter} {l : List α}
    (M : StackMatching w l) (x y : α) : ℕ∞ :=
  let s := l.formPerm*turns M.first
  (dartGraph M.mate s).edist (vertex s x) (vertex s y)

lemma StackMatching.distance_cast {w : α→TypedLetter} {l l' : List α}
    (h : l=l') (M : StackMatching w l) (x y : α) :
    (h ▸ M).distance x y=M.distance x y := by cases h;rfl

/-- Erasing a possibly empty successful interval does not shorten any
retained all-edge distance. Both vertices are kept literal dart vertices. -/
lemma StackMatching.erase_distance [Fintype α] {w : α→TypedLetter}
    (u v z : List α) (M : StackMatching w (u++(v++z)))
    (hn : (u++(v++z)).Nodup) (hv : stackTypedRun (v.map w) []=some [])
    (hc : u++z≠[]) (x y : α) (hx : x∈u++z) (hy : y∈u++z) :
    ∃ D : StackMatching w (u++z),M.distance x y=D.distance x y := by
  cases v with
  | nil =>
    refine ⟨(by simpa only [List.nil_append] using M),?_⟩
    rfl
  | cons a L =>
    have hcomp : z++u≠[] := by
      intro h
      obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp h
      exact hc rfl
    obtain ⟨b,R,hR⟩ := List.exists_cons_of_ne_nil hcomp
    refine ⟨M.deleteInterval hn hv,?_⟩
    exact M.delete_interval_distance u L z a b R hn hv hR x y
      (fun h => List.disjoint_left.mp (complement_disjoint_interval u (a::L) z hn) hx h)
      (fun h => List.disjoint_left.mp (complement_disjoint_interval u (a::L) z hn) hy h)

/-- Literal dart order for all successive corner insertions. -/
def dartInsert (l : List (α×List α)) : List α := l.flatMap fun p => p.1::p.2

omit [DecidableEq α] in
lemma core_sublist_insert (l : List (α×List α)) : l.map Prod.fst <+ dartInsert l := by
  induction l with
  | nil => exact List.Sublist.refl _
  | cons p l ih =>
    change p.1::l.map Prod.fst <+ p.1::(p.2++dartInsert l)
    exact (ih.trans (List.sublist_append_right _ _)).cons_cons _

/-- Iterated exact preservation of INTERIOR CORE distances under all its
actual successful corner insertions, including trivial leaf intervals.
No stochastic estimate and no replacement metric is assumed. -/
theorem StackMatching.core_distance [Fintype α] {w : α→TypedLetter}
    (p : List α) (l : List (α×List α))
    (M : StackMatching w (p++dartInsert l)) (hn : (p++dartInsert l).Nodup)
    (he : ∀ c∈l,stackTypedRun (c.2.map w) []=some [])
    (hc : p++l.map Prod.fst≠[]) (x y : α)
    (hx : x∈p++l.map Prod.fst) (hy : y∈p++l.map Prod.fst) :
    ∃ D : StackMatching w (p++l.map Prod.fst),M.distance x y=D.distance x y := by
  induction l generalizing p with
  | nil =>
    refine ⟨M,?_⟩
    rfl
  | cons c l ih =>
    let q := p++[c.1]
    have hword : p++dartInsert (c::l)=q++(c.2++dartInsert l) := by
      simp only [q,dartInsert,List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append]
    let M' : StackMatching w (q++(c.2++dartInsert l)) := hword ▸ M
    have hn' : (q++(c.2++dartInsert l)).Nodup := hword ▸ hn
    have he' : stackTypedRun (c.2.map w) []=some [] := he c (by simp)
    have hcore : p++(c::l).map Prod.fst=q++l.map Prod.fst := by
      simp only [q,List.map_cons,List.append_assoc,List.singleton_append]
    have hsub : q++l.map Prod.fst <+ q++dartInsert l :=
      List.Sublist.append (List.Sublist.refl _) (core_sublist_insert _)
    have hx' : x∈q++dartInsert l := hsub.subset (hcore ▸ hx)
    have hy' : y∈q++dartInsert l := hsub.subset (hcore ▸ hy)
    have hnon : q++dartInsert l≠[] := List.ne_nil_of_mem hx'
    obtain ⟨D,hD⟩ := M'.erase_distance q c.2 (dartInsert l) hn' he' hnon x y hx' hy'
    have hnD : (q++dartInsert l).Nodup :=
      hn'.sublist (List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _))
    obtain ⟨E,hE⟩ := ih q D hnD (fun t ht => he t (by simp [ht]))
      (hcore ▸ hc) (hcore ▸ hx) (hcore ▸ hy)
    refine ⟨hcore.symm ▸ E,?_⟩
    rw [StackMatching.distance_cast]
    exact (M.distance_cast hword x y).symm.trans (hD.trans hE)

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
lemma filter_keep_interval (u v z : List α) (hn : (u++(v++z)).Nodup) :
    (u++(v++z)).filter (fun d => decide (d∈v))=v := by
  have hd := complement_disjoint_interval u v z hn
  rw [List.filter_append,List.filter_append]
  have hu : u.filter (fun d => decide (d∈v))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hm
    simp only [decide_eq_true_eq]
    exact fun h => List.disjoint_left.mp hd (List.mem_append_left _ hm) h
  have hz : z.filter (fun d => decide (d∈v))=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro d hm
    simp only [decide_eq_true_eq]
    exact fun h => List.disjoint_left.mp hd (List.mem_append_right _ hm) h
  have hv : v.filter (fun d => decide (d∈v))=v := by
    apply List.filter_eq_self.mpr
    intro d hd
    exact decide_eq_true hd
  rw [hu,hv,hz,List.nil_append,List.append_nil]

/-- The literal restricted successful matching, retaining an inserted word. -/
def StackMatching.keepInterval {w : α→TypedLetter} {u v z : List α}
    (M : StackMatching w (u++(v++z))) (hn : (u++(v++z)).Nodup)
    (hv : stackTypedRun (v.map w) []=some []) : StackMatching w v := by
  have hpres := (M.empty_interval_preserves hn hv).1
  let keep : α→Bool := fun d => decide (d∈v)
  have hk : ∀ d∈u++(v++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact hpres d
  exact filter_keep_interval u v z hn ▸ M.filter hn keep hk

/-- All-edge distances inside inserted words are unchanged in the ambient
map, and agree with the actual isolated typed matching of that word. -/
theorem StackMatching.keep_interval_distance {w : α→TypedLetter}
    (u L z : List α) (a b : α) (R : List α)
    (M : StackMatching w (u++((a::L)++z))) (hn : (u++((a::L)++z)).Nodup)
    (hv : stackTypedRun ((a::L).map w) []=some []) (hcomp : z++u=b::R)
    (x y : α) (hx : x∈a::L) (hy : y∈a::L) :
    M.distance x y=(M.keepInterval hn hv).distance x y := by
  let S : Set α := {d | d∈a::L}
  let keep : α→Bool := fun d => decide (d∈a::L)
  have hpres := M.empty_interval_preserves hn hv
  have hk : ∀ d∈u++((a::L)++z),keep (M.mate d)=keep d := by
    intro d _
    simp only [keep,decide_eq_decide]
    exact hpres.1 d
  let D := M.keepInterval hn hv
  have hDfirst : D.first=(M.filter hn keep hk).first := StackMatching.cast_first _ _
  have hDmate : D.mate=(M.filter hn keep hk).mate := StackMatching.cast_mate _ _
  have hd : (a::L).Disjoint (b::R) := by
    have hh : ((a::L)++(b::R)).Nodup := by
      rw [← hcomp,← List.append_assoc]
      exact List.perm_append_comm.nodup_iff.mp hn
    exact List.disjoint_iff_ne.mpr (List.nodup_append.mp hh).2.2
  let p := (a::L).formPerm*(b::R).formPerm*turns M.first
  let r := (a::L).formPerm*turns D.first
  have hp : ∀ d,p d∈S ↔ d∈S := by
    intro d
    simp only [p,S,Set.mem_ofPred_eq,mul_apply,List.formPerm_mem_iff_mem,
      formPerm_other_mem_iff hd,hpres.2]
  have hfixed (d : α) (hd' : d∉a::L) : r d=d := by
    have hf : turns D.first d=d := by
      rw [hDfirst]
      exact M.filter_first_fixed hn keep hk d (by exact decide_eq_false hd')
    simp only [r,mul_apply,hf,List.formPerm_apply_of_notMem hd']
  have hrC : ∀ d,r d∈Sᶜ ↔ d∈Sᶜ := perm_preserves_of_fixed hfixed
  have hr : ∀ d,r d∈S ↔ d∈S := by
    intro d
    exact not_iff_not.mp (hrC d)
  have hepC : ∀ d,D.mate d∈Sᶜ ↔ d∈Sᶜ := by
    apply perm_preserves_of_fixed
    intro d hd'
    rw [hDmate]
    exact M.filter_mate_fixed hn keep hk d (by exact decide_eq_false hd')
  have hep : ∀ d,D.mate d∈S ↔ d∈S := fun d => not_iff_not.mp (hepC d)
  have hpq (d : α) (hd' : d∈S) : p d=r d := by
    have hf : turns D.first d=turns M.first d := by
      rw [hDfirst]
      exact M.filter_first hn keep hk d (by exact decide_eq_true hd')
    have hnr : turns M.first d∉b::R := fun h =>
      List.disjoint_left.mp hd ((hpres.2 d).mpr hd') h
    simp only [p,r,mul_apply,hf,List.formPerm_apply_of_notMem hnr]
  have hef (d : α) (hd' : d∈S) : M.mate d=D.mate d := by
    rw [hDmate]
    exact (M.filter_mate_on hn keep hk d (by exact decide_eq_true hd')).symm
  let E := sideGraphCongr hp hr hpres.1 hep hpq hef
  unfold StackMatching.distance
  rw [M.empty_interval_rotation u L z a b R hn hcomp]
  change (dartGraph M.mate (swap a b*p)).edist _ _=(dartGraph D.mate r).edist _ _
  calc
    _=(sideGraph M.mate p S hpres.1).edist (sideMk p S x hx) (sideMk p S y hy) :=
      (M.empty_interval_wedge u L z a b R hn hv hcomp).edist_left _ _
    _=(sideGraph D.mate r S hep).edist (sideMk r S x hx) (sideMk r S y hy) :=
      (GraphWedge.iso_edist E _ _).symm
    _=_ := (fullInclusion_edist hr hep (sideMk r S x hx) (sideMk r S y hy)).symm

end FKCRT.Inventory
end

end OAI
