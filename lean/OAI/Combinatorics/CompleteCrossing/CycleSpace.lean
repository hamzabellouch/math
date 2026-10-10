import OAI.Combinatorics.CompleteCrossing.Drawing
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! Cycle-space spanning, flows, simple cycles, and oriented darts. -/

section

/-! Linear properties of actual oriented simple cycles. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} {G : Graph V E}
namespace SimpleCycle

def next (C : SimpleCycle G) (i : Fin C.length) : Fin C.length :=
  ⟨(i.val+1)%C.length, Nat.mod_lt _ (by have := C.three_le; omega)⟩

theorem follows_next (C : SimpleCycle G) (i : Fin C.length) :
    (G.src (C.edge i)=C.vertex i ∧ G.dst (C.edge i)=C.vertex (C.next i)) ∨
      (G.dst (C.edge i)=C.vertex i ∧ G.src (C.edge i)=C.vertex (C.next i)) := C.follows i

theorem next_eq_finRotate (C : SimpleCycle G) : C.next = finRotate C.length := by
  funext i
  apply Fin.ext
  have hL : 1 < C.length := by have := C.three_le; omega
  simp [next, finRotate_apply, Fin.val_add, Nat.mod_eq_of_lt hL]

theorem next_val (C : SimpleCycle G) (i : Fin C.length) :
    (C.next i).val = if i.val+1<C.length then i.val+1 else 0 := by
  change (i.val+1)%C.length = _
  by_cases h : i.val+1<C.length
  · simp [h, Nat.mod_eq_of_lt h]
  · have he : i.val+1=C.length := by omega
    simp [he]

theorem next_ne_self (C : SimpleCycle G) (i : Fin C.length) : C.next i≠i := by
  intro h
  have he := congrArg Fin.val h
  rw [next_val] at he
  have := C.three_le
  split_ifs at he <;> omega

theorem next_next_ne_self (C : SimpleCycle G) (i : Fin C.length) : C.next (C.next i)≠i := by
  intro h
  have he := congrArg Fin.val h
  simp only [next_val] at he
  have := C.three_le
  split_ifs at he <;> omega

theorem edge_injective (C : SimpleCycle G) : Function.Injective C.edge := by
  intro i j hij
  have hi := C.follows_next i
  have hj := C.follows_next j
  rw [hij] at hi
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact C.vertex_injective (hi.1.symm.trans hj.1)
  · have h1 := C.vertex_injective (hi.1.symm.trans hj.2)
    have h2 := C.vertex_injective (hi.2.symm.trans hj.1)
    exact False.elim (C.next_next_ne_self j (by rw [← h1,h2]))
  · have h1 := C.vertex_injective (hi.1.symm.trans hj.2)
    have h2 := C.vertex_injective (hi.2.symm.trans hj.1)
    exact False.elim (C.next_next_ne_self j (by rw [← h1,h2]))
  · exact C.vertex_injective (hi.1.symm.trans hj.1)

theorem edgeChain_at_edge (C : SimpleCycle G) (i : Fin C.length) :
    C.edgeChain (C.edge i) = if G.src (C.edge i)=C.vertex i then 1 else -1 := by
  classical
  simp only [edgeChain, C.edge_injective.eq_iff]
  simp

theorem edgeChain_at_edge_ne_zero (C : SimpleCycle G) (i : Fin C.length) :
    C.edgeChain (C.edge i) ≠ 0 := by
  rw [edgeChain_at_edge]
  split_ifs <;> norm_num

theorem edgeChain_eq_zero_of_not_mem_range (C : SimpleCycle G) {e : E}
    (he : e∉Set.range C.edge) : C.edgeChain e=0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  rw [ite_eq_right (fun h => he ⟨i,h⟩)]

theorem edgeChain_support (C : SimpleCycle G) (e : E) :
    C.edgeChain e≠0 ↔ e∈Set.range C.edge := by
  constructor
  · exact fun h => Classical.byContradiction (fun he => h (C.edgeChain_eq_zero_of_not_mem_range he))
  · rintro ⟨i,rfl⟩
    exact C.edgeChain_at_edge_ne_zero i

theorem signed_boundary_step (C : SimpleCycle G) (i : Fin C.length) (v : V) :
    (if G.src (C.edge i)=C.vertex i then (1:ℝ) else -1) *
      ((if G.dst (C.edge i)=v then 1 else 0)-(if G.src (C.edge i)=v then 1 else 0)) =
    (if C.vertex (C.next i)=v then 1 else 0)-(if C.vertex i=v then 1 else 0) := by
  classical
  rcases C.follows_next i with h | h
  · simp [h.1,h.2]
  · have hn : C.vertex (C.next i)≠C.vertex i := fun h => C.next_ne_self i (C.vertex_injective h)
    simp only [h.1,h.2,ite_eq_right hn]
    ring

theorem boundary_edgeChain [Fintype E] (C : SimpleCycle G) (v : V) : boundary G C.edgeChain v=0 := by
  classical
  unfold boundary edgeChain
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi (i : Fin C.length) :
      (∑e, (if C.edge i=e then (if G.src e=C.vertex i then (1:ℝ) else -1) else 0) *
        ((if G.dst e=v then 1 else 0)-(if G.src e=v then 1 else 0))) =
      (if C.vertex (C.next i)=v then 1 else 0)-(if C.vertex i=v then 1 else 0) := by
    rw [Finset.sum_eq_single (C.edge i)]
    · simpa using C.signed_boundary_step i v
    · intro e _ he
      simp [Ne.symm he]
    · simp
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, next_eq_finRotate]
  exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate C.length)
    (fun i => if C.vertex i=v then (1:ℝ) else 0))

end SimpleCycle
end Paper170

end
end

section

noncomputable section
open scoped BigOperators Classical
namespace Paper170

variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

omit [Fintype V] in
lemma incoming_has_outgoing (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (v : V) (e : E)
    (he : (G.dst e = v ∧ 0 < z e) ∨ (G.src e = v ∧ z e < 0)) :
    ∃ f, ((G.src f = v ∧ 0 < z f) ∨ (G.dst f = v ∧ z f < 0)) := by
  by_contra hn
  have hn' (f : E) : ¬ ((G.src f = v ∧ 0 < z f) ∨ (G.dst f = v ∧ z f < 0)) := fun hf => hn ⟨f, hf⟩
  let term := fun f : E => z f * ((if G.dst f = v then 1 else 0) -
    (if G.src f = v then 1 else 0))
  have hnonneg (f : E) : 0 ≤ term f := by
    by_cases hdst : G.dst f = v
    · by_cases hsrc : G.src f = v
      · exact (G.loopless f (hsrc.trans hdst.symm)).elim
      · have hf : 0 ≤ z f := by
          by_contra! h
          exact hn' f (Or.inr ⟨hdst, h⟩)
        simpa [term, hdst, hsrc] using hf
    · by_cases hsrc : G.src f = v
      · have hf : z f ≤ 0 := by
          by_contra! h
          exact hn' f (Or.inl ⟨hsrc, h⟩)
        simpa [term, hdst, hsrc] using neg_nonneg.mpr hf
      · simp [term, hdst, hsrc]
  have hpos : 0 < term e := by
    rcases he with ⟨hdst, he⟩ | ⟨hsrc, he⟩
    · have hsrc : G.src e ≠ v := fun h => G.loopless e (h.trans hdst.symm)
      simpa [term, hdst, hsrc] using he
    · have hdst : G.dst e ≠ v := fun h => G.loopless e (hsrc.trans h.symm)
      simpa [term, hdst, hsrc] using neg_pos.mpr he
  have ht : 0 < ∑ f, term f := Finset.sum_pos' (fun f _ => hnonneg f)
    ⟨e, Finset.mem_univ e, hpos⟩
  have hzero : (∑ f, term f) = 0 := hz v
  linarith

abbrev FlowVertex (z : E → ℝ) := {v : V // ∃ e, ((G.src e = v ∧ 0 < z e) ∨ (G.dst e = v ∧ z e < 0))}

omit [Fintype V] in
lemma flow_successor_exists (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (v : FlowVertex G z) : ∃ w : FlowVertex G z, ∃ e, ((G.src e = v.val ∧ G.dst e = w.val ∧ 0 < z e) ∨
    (G.dst e = v.val ∧ G.src e = w.val ∧ z e < 0)) := by
  obtain ⟨e, he⟩ := v.property
  rcases he with ⟨hsrc, he⟩ | ⟨hdst, he⟩
  · refine ⟨⟨G.dst e, incoming_has_outgoing G z hz (G.dst e) e (Or.inl ⟨rfl, he⟩)⟩,
      e, Or.inl ⟨hsrc, rfl, he⟩⟩
  · refine ⟨⟨G.src e, incoming_has_outgoing G z hz (G.src e) e (Or.inr ⟨rfl, he⟩)⟩,
      e, Or.inr ⟨hdst, rfl, he⟩⟩

def flowNext (z : E → ℝ) (hz : ∀ v, boundary G z v = 0) (v : FlowVertex G z) :
    FlowVertex G z := (flow_successor_exists G z hz v).choose

def flowEdge (z : E → ℝ) (hz : ∀ v, boundary G z v = 0) (v : FlowVertex G z) : E :=
  (flow_successor_exists G z hz v).choose_spec.choose

omit [Fintype V] in
lemma flowEdge_spec (z : E → ℝ) (hz : ∀ v, boundary G z v = 0) (v : FlowVertex G z) :
    ((G.src (flowEdge G z hz v) = v.val ∧ G.dst (flowEdge G z hz v) = (flowNext G z hz v).val ∧ 0 < z (flowEdge G z hz v)) ∨
    (G.dst (flowEdge G z hz v) = v.val ∧ G.src (flowEdge G z hz v) = (flowNext G z hz v).val ∧ z (flowEdge G z hz v) < 0)) :=
  (flow_successor_exists G z hz v).choose_spec.choose_spec

omit [Fintype V] [Fintype E] in
lemma flowArc_irrefl (z : E → ℝ) (v : V) (e : E) : ¬ ((G.src e = v ∧ G.dst e = v ∧ 0 < z e) ∨
    (G.dst e = v ∧ G.src e = v ∧ z e < 0)) := by
  rintro (⟨hs, hd, _⟩ | ⟨hd, hs, _⟩) <;> exact G.loopless e (hs.trans hd.symm)

omit [Fintype V] [Fintype E] in
lemma flowArc_not_reverse (z : E → ℝ) (v w : V) (e f : E)
    (he : ((G.src e = v ∧ G.dst e = w ∧ 0 < z e) ∨
    (G.dst e = v ∧ G.src e = w ∧ z e < 0))) (hf : ((G.src f = w ∧ G.dst f = v ∧ 0 < z f) ∨
    (G.dst f = w ∧ G.src f = v ∧ z f < 0))) : False := by
  have hef : e = f := by
    apply G.simple e f
    rcases he with ⟨he1, he2, _⟩ | ⟨he1, he2, _⟩ <;>
      rcases hf with ⟨hf1, hf2, _⟩ | ⟨hf1, hf2, _⟩
    · exact Or.inr ⟨he1.trans hf2.symm, he2.trans hf1.symm⟩
    · exact Or.inl ⟨he1.trans hf2.symm, he2.trans hf1.symm⟩
    · exact Or.inl ⟨he2.trans hf1.symm, he1.trans hf2.symm⟩
    · exact Or.inr ⟨he2.trans hf1.symm, he1.trans hf2.symm⟩
  subst f
  rcases he with ⟨he1, he2, hp⟩ | ⟨he1, he2, hp⟩ <;>
    rcases hf with ⟨hf1, hf2, hq⟩ | ⟨hf1, hf2, hq⟩
  · exact G.loopless e (he1.trans hf2.symm)
  · linarith
  · linarith
  · exact G.loopless e (hf2.trans he1.symm)

lemma exists_positive_period {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    ∃ a, 0 < Function.minimalPeriod f a := by
  let x : α := Classical.arbitrary α
  obtain ⟨m, n, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => f^[i] x)
  have helper {m n : ℕ} (hmn : m < n) (h : f^[m] x = f^[n] x) :
      ∃ a, 0 < Function.minimalPeriod f a := by
    have hperiod : Function.IsPeriodicPt f (n - m) (f^[m] x) := by
      change f^[n-m] (f^[m] x) = f^[m] x
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hmn.le]
      exact h.symm
    exact ⟨f^[m] x, hperiod.minimalPeriod_pos (Nat.sub_pos_of_lt hmn)⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact helper hlt heq
  · exact helper hlt heq.symm

end Paper170

end
end

section

/-! Directed traversals of the fixed edges of an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170Geometry
open Paper170 (Graph)
variable {V E : Type} {G : Graph V E}

structure OrientedDart (G : Graph V E) where
  edge : E
  forward : Bool

namespace OrientedDart

def fst (d : OrientedDart G) : V := if d.forward then G.src d.edge else G.dst d.edge

def snd (d : OrientedDart G) : V := if d.forward then G.dst d.edge else G.src d.edge

def symm (d : OrientedDart G) : OrientedDart G := ⟨d.edge,!d.forward⟩

@[simp] theorem symm_fst (d : OrientedDart G) : d.symm.fst = d.snd := by
  cases d with | mk e b => cases b <;> rfl

@[simp] theorem symm_snd (d : OrientedDart G) : d.symm.snd = d.fst := by
  cases d with | mk e b => cases b <;> rfl

@[simp] theorem symm_symm (d : OrientedDart G) : d.symm.symm = d := by
  cases d with | mk e b => cases b <;> rfl

theorem fst_ne_snd (d : OrientedDart G) : d.fst ≠ d.snd := by
  cases d with
  | mk e b =>
    cases b
    · exact (G.loopless e).symm
    · exact G.loopless e

end OrientedDart

def forwardDart (G : Graph V E) (e : E) : OrientedDart G := ⟨e,true⟩

def backwardDart (G : Graph V E) (e : E) : OrientedDart G := ⟨e,false⟩

def dartSign (d : OrientedDart G) : ℝ := if d.forward then 1 else -1

theorem orientedDart_cases (d : OrientedDart G) :
    (∃ e, d = forwardDart G e) ∨ (∃ e, d = backwardDart G e) := by
  cases d with
  | mk e b =>
    cases b
    · exact Or.inr ⟨e,rfl⟩
    · exact Or.inl ⟨e,rfl⟩

theorem dart_source_incident (d : OrientedDart G) :
    d.fst = G.src d.edge ∨ d.fst = G.dst d.edge := by
  cases d with
  | mk e b =>
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem dart_target_incident (d : OrientedDart G) :
    d.snd = G.src d.edge ∨ d.snd = G.dst d.edge := by
  cases d with
  | mk e b =>
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

@[simp] theorem dartSign_symm (d : OrientedDart G) : dartSign d.symm = -dartSign d := by
  cases d with | mk e b => cases b <;> norm_num [dartSign,OrientedDart.symm]

end Paper170Geometry

end
end

section

/-! Support reduction spans the real kernel of the graph boundary map by simple cycles. -/
noncomputable section
open scoped BigOperators Classical
namespace Paper170
variable {V E : Type} [Fintype E] (G : Graph V E)

def boundaryLinear : (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun z := boundary G z
  map_add' z w := by
    funext v
    simp [boundary, add_mul, Finset.sum_add_distrib]
  map_smul' a z := by
    funext v
    simp [boundary, mul_assoc, Finset.mul_sum]

def chainSupport (z : E → ℝ) : Finset E := Finset.univ.filter fun e => z e≠0

theorem mem_chainSupport (z : E → ℝ) (e : E) : e∈chainSupport z ↔ z e≠0 := by
  simp [chainSupport]

theorem simple_cycles_balanced (z : E → ℝ)
    (hz : z∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain))) :
    ∀v, boundary G z v=0 := by
  have hle : Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) ≤
      LinearMap.ker (boundaryLinear G) := by
    rw [Submodule.span_le]
    rintro _ ⟨C,rfl⟩
    exact funext C.boundary_edgeChain
  exact fun v => congrFun (hle hz) v

theorem simple_cycles_span_of_supported_cycle
    (hex : ∀z : E → ℝ, (∀v, boundary G z v=0) → z≠0 →
      ∃C : SimpleCycle G, ∀i, z (C.edge i)≠0) (z : E → ℝ) :
    (∀v, boundary G z v=0) ↔ z∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) := by
  constructor
  · intro hz
    suffices h : ∀m (w : E → ℝ), (chainSupport w).card=m → (∀v, boundary G w v=0) →
        w∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) from
      h _ z rfl hz
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro w hm hw
      by_cases hw0 : w=0
      · simp [hw0]
      obtain ⟨C,hC⟩ := hex w hw hw0
      let i : Fin C.length := ⟨0,by have := C.three_le; omega⟩
      let e := C.edge i
      have hc : C.edgeChain e≠0 := C.edgeChain_at_edge_ne_zero i
      let a := w e / C.edgeChain e
      let w' := w-a • C.edgeChain
      have hw' : ∀v, boundary G w' v=0 := by
        have hmapw : boundaryLinear G w=0 := funext hw
        have hmapC : boundaryLinear G C.edgeChain=0 := funext C.boundary_edgeChain
        have hmap : boundaryLinear G w'=0 := by
          simp only [w',map_sub,map_smul,hmapw,hmapC,smul_zero,sub_self]
        exact fun v => congrFun hmap v
      have he0 : w' e=0 := by
        change w e-(w e/C.edgeChain e)*C.edgeChain e=0
        rw [div_mul_cancel₀ _ hc,sub_self]
      have hsub : chainSupport w' ⊆ chainSupport w := by
        intro f hf
        rw [mem_chainSupport] at hf ⊢
        by_contra hwf
        have hCf : C.edgeChain f=0 := by
          by_contra hh
          obtain ⟨j,hj⟩ := (C.edgeChain_support f).mp hh
          exact hC j (hj ▸ hwf)
        apply hf
        change w f-a*C.edgeChain f=0
        rw [hwf,hCf,mul_zero,sub_self]
      have hproper : chainSupport w' ⊂ chainSupport w := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub,?_⟩
        intro heq
        have hew : e∈chainSupport w := (mem_chainSupport w e).mpr (hC i)
        rw [← heq,mem_chainSupport] at hew
        exact hew he0
      have hcard : (chainSupport w').card<m := by
        rw [← hm]
        exact Finset.card_lt_card hproper
      have hind := ih _ hcard w' rfl hw'
      have hchain : C.edgeChain∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) :=
        Submodule.subset_span ⟨C,rfl⟩
      have hsum := (Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain))).add_mem
        hind ((Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain))).smul_mem a hchain)
      simpa only [w',sub_add_cancel] using hsum
  · exact simple_cycles_balanced G z

end Paper170

end
end

section

noncomputable section
open scoped Classical
namespace Paper170

variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

omit [Fintype V] in
lemma flow_period_three (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (a : FlowVertex G z) (hp : 0 < Function.minimalPeriod (flowNext G z hz) a) :
    3 ≤ Function.minimalPeriod (flowNext G z hz) a := by
  let f := flowNext G z hz
  have hone : Function.minimalPeriod f a ≠ 1 := by
    intro h
    have heq : f a = a := by
      simpa [h] using (Function.iterate_minimalPeriod (f := f) (x := a))
    have hs := flowEdge_spec G z hz a
    change ((G.src (flowEdge G z hz a) = a.val ∧ G.dst (flowEdge G z hz a) = (f a).val ∧ 0 < z (flowEdge G z hz a)) ∨
      (G.dst (flowEdge G z hz a) = a.val ∧ G.src (flowEdge G z hz a) = (f a).val ∧ z (flowEdge G z hz a) < 0)) at hs
    rw [heq] at hs
    exact flowArc_irrefl G z a.val _ hs
  have htwo : Function.minimalPeriod f a ≠ 2 := by
    intro h
    have heq : f (f a) = a := by
      simpa [h, Function.iterate_succ_apply'] using
        (Function.iterate_minimalPeriod (f := f) (x := a))
    have hs := flowEdge_spec G z hz (f a)
    change ((G.src (flowEdge G z hz (f a)) = (f a).val ∧ G.dst (flowEdge G z hz (f a)) = (f (f a)).val ∧ 0 < z (flowEdge G z hz (f a))) ∨
      (G.dst (flowEdge G z hz (f a)) = (f a).val ∧ G.src (flowEdge G z hz (f a)) = (f (f a)).val ∧ z (flowEdge G z hz (f a)) < 0)) at hs
    rw [heq] at hs
    exact flowArc_not_reverse G z a.val (f a).val _ _ (flowEdge_spec G z hz a) hs
  change 0 < Function.minimalPeriod f a at hp
  change 3 ≤ Function.minimalPeriod f a
  omega

theorem exists_supported_simple_cycle (z : E → ℝ) (hz : ∀ v, boundary G z v = 0)
    (hne : z ≠ 0) : ∃ C : SimpleCycle G, ∀ i, z (C.edge i) ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  have hnonempty : Nonempty (FlowVertex G z) := by
    rcases lt_or_gt_of_ne he with h | h
    · exact ⟨⟨G.dst e, e, Or.inr ⟨rfl, h⟩⟩⟩
    · exact ⟨⟨G.src e, e, Or.inl ⟨rfl, h⟩⟩⟩
  let := hnonempty
  let f := flowNext G z hz
  obtain ⟨a, ha⟩ := exists_positive_period f
  let n := Function.minimalPeriod f a
  have hn : 3 ≤ n := flow_period_three G z hz a ha
  have hstep (i : Fin n) :
      f^[((i.val + 1) % n)] a = f (f^[i.val] a) := by
    rw [Function.iterate_mod_minimalPeriod_eq]
    exact Function.iterate_succ_apply' _ _ _
  let C : SimpleCycle G :=
    { length := n
      three_le := hn
      vertex := fun i => (f^[i.val] a).val
      vertex_injective := by
        intro i j hij
        apply Fin.ext
        exact Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt (Subtype.ext hij)
      edge := fun i => flowEdge G z hz (f^[i.val] a)
      follows := by
        intro i
        change (G.src (flowEdge G z hz (f^[i.val] a)) = (f^[i.val] a).val ∧
          G.dst (flowEdge G z hz (f^[i.val] a)) = (f^[((i.val + 1) % n)] a).val) ∨
          (G.dst (flowEdge G z hz (f^[i.val] a)) = (f^[i.val] a).val ∧
          G.src (flowEdge G z hz (f^[i.val] a)) = (f^[((i.val + 1) % n)] a).val)
        rw [hstep]
        rcases flowEdge_spec G z hz (f^[i.val] a) with ⟨hs, hd, _⟩ | ⟨hd, hs, _⟩
        · exact Or.inl ⟨hs, hd⟩
        · exact Or.inr ⟨hd, hs⟩ }
  refine ⟨C, ?_⟩
  intro i
  rcases flowEdge_spec G z hz (f^[i.val] a) with ⟨_, _, hp⟩ | ⟨_, _, hn⟩
  · exact ne_of_gt hp
  · exact ne_of_lt hn

end Paper170

end
end

section

/-! A frozen simple cycle gives a periodic sequence of actual oriented edge traversals. -/
noncomputable section
open scoped Classical
namespace Paper170.SimpleCycle
open Paper170Geometry
variable {V E : Type} {G : Graph V E}

def dart (C : SimpleCycle G) (i : Fin C.length) : OrientedDart G :=
  ⟨C.edge i,decide (G.src (C.edge i)=C.vertex i)⟩

theorem dart_fst (C : SimpleCycle G) (i : Fin C.length) : (C.dart i).fst = C.vertex i := by
  rcases C.follows_next i with h | h
  · simp [dart,OrientedDart.fst,h.1]
  · have hn : G.src (C.edge i) ≠ C.vertex i := by
      rw [h.2]
      exact fun he => C.next_ne_self i (C.vertex_injective he)
    simp [dart,OrientedDart.fst,hn,h.1]

theorem dart_snd (C : SimpleCycle G) (i : Fin C.length) : (C.dart i).snd = C.vertex (C.next i) := by
  rcases C.follows_next i with h | h
  · simp [dart,OrientedDart.snd,h.1,h.2]
  · have hn : G.src (C.edge i) ≠ C.vertex i := by
      rw [h.2]
      exact fun he => C.next_ne_self i (C.vertex_injective he)
    simpa only [dart,OrientedDart.snd,decide_eq_true_eq,ite_eq_right hn] using h.2

theorem dart_edge (C : SimpleCycle G) (i : Fin C.length) : (C.dart i).edge = C.edge i := rfl

theorem dart_sign (C : SimpleCycle G) (i : Fin C.length) :
    dartSign (C.dart i) = if G.src (C.edge i)=C.vertex i then 1 else -1 := by
  simp [dart,dartSign]

def modIndex (C : SimpleCycle G) (i : ℕ) : Fin C.length :=
  ⟨i % C.length,Nat.mod_lt _ (by have := C.three_le; omega)⟩

theorem modIndex_succ (C : SimpleCycle G) (i : ℕ) : C.modIndex (i+1)=C.next (C.modIndex i) := by
  apply Fin.ext
  simp [modIndex,next,Nat.add_mod]

theorem modIndex_period (C : SimpleCycle G) : C.modIndex C.length=C.modIndex 0 := by
  apply Fin.ext
  simp [modIndex]

def cyclicDart (C : SimpleCycle G) (i : ℕ) : OrientedDart G := C.dart (C.modIndex i)

theorem cyclicDart_seam (C : SimpleCycle G) (i : ℕ) :
    (C.cyclicDart i).snd = (C.cyclicDart (i+1)).fst := by
  simp only [cyclicDart,dart_snd,dart_fst,modIndex_succ]

theorem cyclicDart_period (C : SimpleCycle G) : C.cyclicDart C.length = C.cyclicDart 0 := by
  rw [cyclicDart,cyclicDart,modIndex_period]

theorem cyclicDart_next_edge_ne (C : SimpleCycle G) (i : ℕ) :
    (C.cyclicDart (i+1)).edge ≠ (C.cyclicDart i).edge := by
  simp only [cyclicDart,dart_edge,modIndex_succ]
  exact fun he => C.next_ne_self _ (C.edge_injective he)

end Paper170.SimpleCycle

end
end

section

/-! The real cycle space of an arbitrary finite simple graph. -/
noncomputable section
namespace Paper170
variable {V E : Type} [Fintype V] [Fintype E] (G : Graph V E)

theorem simple_cycles_span (z : E → ℝ) :
    (∀v, boundary G z v=0) ↔
      z∈Submodule.span ℝ (Set.range (fun C : SimpleCycle G => C.edgeChain)) :=
  simple_cycles_span_of_supported_cycle G (exists_supported_simple_cycle G) z

end Paper170

end
end

end OAI
