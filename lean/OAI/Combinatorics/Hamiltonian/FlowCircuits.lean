import OAI.Combinatorics.Hamiltonian.CutSpaces

namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure FlowCircuit (x : E → ℝ) : Prop where
  conserved : N.boundary x = 0
  nonzero : x ≠ 0
  minimal : ∀ y, N.boundary y = 0 → N.flowSupport y ⊆ N.flowSupport x →
    y = 0 ∨ N.flowSupport y = N.flowSupport x

omit [Fintype V] in
lemma flowSupport_eq_empty_iff (x : E → ℝ) : N.flowSupport x = ∅ ↔ x = 0 := by
  simp only [Finset.eq_empty_iff_forall_notMem, mem_flowSupport, not_not,
    funext_iff, Pi.zero_apply]

omit [Fintype V] [Fintype F] in
lemma Duality.dual_conserved_gradient (h : N.Duality D) (f : V → ℝ) :
    D.boundary (N.gradient f) = 0 := by
  have hh : N.gradient f ∈ N.gradient.range := ⟨f,rfl⟩
  rwa [← h.dual_cycles_eq_cuts] at hh

omit [Fintype V] [Fintype F] in
lemma Duality.gradient_of_dual_conserved (h : N.Duality D) {x : E → ℝ}
    (hx : D.boundary x = 0) : ∃ f, N.gradient f = x := by
  have hh : x ∈ D.boundary.ker := hx
  rwa [h.dual_cycles_eq_cuts] at hh

omit [Fintype V] [Fintype F] in

theorem Duality.circuit_two_levels (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (f : V → ℝ) (hf : N.gradient f = x)
    {e : E} (he : x e ≠ 0) :
    ∀ v, f v = f (N.tail e) ∨ f v = f (N.head e) := by
  have he' : f (N.head e) ≠ f (N.tail e) := by
    simpa only [← hf, gradient_apply, sub_ne_zero] using he
  intro v
  by_contra hv
  obtain ⟨hvt,hvh⟩ := not_or.mp hv
  let g : V → ℝ := fun w => if f w = f v then 1 else 0
  have hgsub : D.flowSupport (N.gradient g) ⊆ D.flowSupport x := by
    intro k hk
    apply (D.mem_flowSupport x k).mpr
    intro hxk
    have hfk : f (N.head k) = f (N.tail k) := by
      apply sub_eq_zero.mp
      simpa only [← hf, gradient_apply] using hxk
    have hgk : N.gradient g k = 0 := by simp only [gradient_apply, g, hfk, sub_self]
    exact (D.mem_flowSupport _ k).mp hk hgk
  have hg : N.gradient g ≠ 0 := by
    intro hg
    have hh := N.gradient_zero_reachable hg (h.connected v (N.tail e))
    have htv : f (N.tail e) ≠ f v := Ne.symm hvt
    norm_num [g,htv] at hh
  have hgs := (hx.minimal (N.gradient g) (h.dual_conserved_gradient N D g) hgsub).resolve_left hg
  have hek : N.gradient g e ≠ 0 := (D.mem_flowSupport _ e).mp (by
    rw [hgs]; exact (D.mem_flowSupport _ e).mpr he)
  have htv : f (N.tail e) ≠ f v := Ne.symm hvt
  have hhv : f (N.head e) ≠ f v := Ne.symm hvh
  exact hek (by simp [gradient_apply, g, htv, hhv])

omit [Fintype F] in

theorem Duality.circuit_cut (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (root : V) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ c ≠ 0 ∧
      x = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.flowSupport x := by
  obtain ⟨f,hf⟩ := h.gradient_of_dual_conserved N D hx.conserved
  obtain ⟨e,he⟩ : ∃ e, x e ≠ 0 := by
    by_contra hn
    apply hx.nonzero
    ext e
    exact not_not.mp (fun he => hn ⟨e,he⟩)
  have he' : f (N.head e) ≠ f (N.tail e) := by
    simpa only [← hf, gradient_apply, sub_ne_zero] using he
  have hall := h.circuit_two_levels N D x hx f hf he
  let a := f root
  let b := if a = f (N.tail e) then f (N.head e) else f (N.tail e)
  have hab : b ≠ a := by
    dsimp [b,a]
    split_ifs with ha
    · rw [ha]; exact he'
    · exact Ne.symm ha
  have hlevels (v : V) : f v = a ∨ f v = b := by
    dsimp [b,a] at ⊢
    rcases hall root with ht | hh
    · rw [ite_eq_left ht,ht]; exact hall v
    · have ht : f root ≠ f (N.tail e) := hh ▸ he'
      rw [ite_eq_right ht,hh]
      exact (hall v).symm
  have hb : ∃ v, f v = b := by
    dsimp [b]
    split_ifs
    · exact ⟨N.head e,rfl⟩
    · exact ⟨N.tail e,rfl⟩
  let A := Finset.univ.filter fun v => f v = b
  have fform (v : V) : f v = a + (b-a) * (if v ∈ A then 1 else 0) := by
    rcases hlevels v with hv | hv
    · have hvA : v ∉ A := by simp [A,hv,Ne.symm hab]
      simp [hvA,hv]
    · have hvA : v ∈ A := by simp [A,hv]
      simp [hvA,hv]
  refine ⟨A,b-a,?_,?_,sub_ne_zero.mpr hab,?_,?_⟩
  · obtain ⟨v,hv⟩ := hb; exact ⟨v,by simp [A,hv]⟩
  · simp [A,show f root = a from rfl, Ne.symm hab]
  · rw [← hf]
    ext k
    simp only [gradient_apply, Pi.smul_apply, smul_eq_mul]
    rw [fform (N.head k), fform (N.tail k)]
    ring
  · ext k
    simp only [mem_cut, mem_flowSupport, ← hf, gradient_apply, sub_ne_zero]
    rw [fform (N.head k), fform (N.tail k)]
    by_cases ht : N.tail k ∈ A <;> by_cases hh : N.head k ∈ A <;>
      simp [ht,hh,hab,Ne.symm hab]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
def star (v : V) : Finset E := Finset.univ.filter fun e => N.Incident e v

omit [Fintype V] in
@[simp] lemma mem_star (e : E) (v : V) : e ∈ N.star v ↔ N.Incident e v := by
  simp [star]

omit [Fintype V] in
def otherEnd (e : E) (v : V) : V := if N.tail e = v then N.head e else N.tail e

omit [Fintype V] [Fintype E] in
lemma otherEnd_spec (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    v ≠ N.otherEnd e v ∧ s(N.tail e,N.head e) = s(v,N.otherEnd e v) := by
  rcases hi with ht | hh
  · rw [otherEnd,ite_eq_left ht]
    exact ⟨ht ▸ h.loopless e, by rw [ht]⟩
  · by_cases ht : N.tail e = v
    · exact (h.loopless e (ht.trans hh.symm)).elim
    · rw [otherEnd,ite_eq_right ht]
      exact ⟨hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

omit [Fintype V] [Fintype E] in
lemma otherEnd_adj (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    N.graph.Adj v (N.otherEnd e v) := by
  obtain ⟨hne,he⟩ := N.otherEnd_spec h hi
  exact ⟨hne,e,Sym2.eq_iff.mp he⟩

lemma card_star (h : N.Simple) (v : V) : (N.star v).card = N.graph.degree v := by
  let f : {e // e ∈ N.star v} → N.graph.neighborSet v := fun e =>
    ⟨N.otherEnd e.val v, N.otherEnd_adj h ((N.mem_star _ _).mp e.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e k hek
      apply Subtype.ext
      apply h.pair_injective
      change s(N.tail e.val, N.head e.val) = s(N.tail k.val, N.head k.val)
      rw [(N.otherEnd_spec h ((N.mem_star _ _).mp e.property)).2,
        (N.otherEnd_spec h ((N.mem_star _ _).mp k.property)).2]
      exact congrArg (fun w => s(v,w)) (congrArg Subtype.val hek)
    · intro w
      obtain ⟨hne,e,he⟩ := w.property
      have hi : N.Incident e v := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      refine ⟨⟨e,(N.mem_star _ _).mpr hi⟩,Subtype.ext ?_⟩
      change N.otherEnd e v = w.val
      rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
      · simp only [otherEnd,ht,ite_true,hh]
      · have ht' : N.tail e ≠ v := by rw [ht]; exact hne.symm
        rw [otherEnd,ite_eq_right ht',ht]
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_coe, SimpleGraph.card_neighborSet_eq_degree] using hh

omit [Fintype V] [Fintype F] in
lemma gradient_indicator_support (h : N.Simple) (v : V) :
    D.flowSupport (N.gradient (fun w => if w = v then 1 else 0)) = N.star v := by
  ext e
  simp only [mem_flowSupport, mem_star, gradient_apply, Incident]
  have hne := h.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp [ht,hh] at *

omit [Fintype F] in

theorem Duality.cubic_face_triangles (h : N.Duality D) (hN : N.Simple)
    (h3 : ThreeVertexConnected N.graph) (hV : 5 ≤ Fintype.card V)
    (hc : N.graph.IsRegularOfDegree 3) : ∀ v, Nonempty (D.Triangle (N.star v)) := by
  intro v
  have hD := h.simple_dual N D h3 hV
  have hx := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : (D.flowSupport (N.gradient (fun w => if w = v then 1 else 0))).card = 3 := by
    rw [N.gradient_indicator_support D hN, N.card_star hN, hc v]
  simpa only [N.gradient_indicator_support D hN] using D.triangle_of_flow hD _ hx hs

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

theorem cyclic_propagation {n : ℕ} [NeZero n] (P : Fin n → Prop)
    (hstep : ∀ i, P (i + 1) → P i) {q : Fin n} (hq : P q) : ∀ i, P i := by
  have h : ∀ k : ℕ, P (q - (k : Fin n)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k hk =>
      apply hstep (q - ((k + 1 : ℕ) : Fin n))
      simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, sub_add_cancel] using hk
  intro i
  simpa only [Fin.cast_val_eq_self, sub_sub_cancel] using h (q - i).val

theorem cyclic_one_ne_zero (n : ℕ) : (1 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem cyclic_two_ne_zero (n : ℕ) : (2 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at this

structure CycleCoordinates {V : Type*} (G : SimpleGraph V) where
  n : ℕ
  vertex : Fin (n + 3) ↪ V
  adjacent : ∀ i, G.Adj (vertex i) (vertex (i + 1))

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

theorem edge_indices_unique (i j : Fin (C.n + 3))
    (h : (C.vertex i = C.vertex j ∧ C.vertex (i + 1) = C.vertex (j + 1)) ∨
      (C.vertex i = C.vertex (j + 1) ∧ C.vertex (i + 1) = C.vertex j)) : i = j := by
  rcases h with h | h
  · exact C.vertex.injective h.1
  · have hi := C.vertex.injective h.1
    have hj := C.vertex.injective h.2
    have hh : (2 : Fin (C.n + 3)) = 0 := by
      have : j + (1 + 1) = j + 0 := by simpa [hi, add_assoc] using hj
      simpa only [show (1 : Fin (C.n + 3)) + 1 = 2 by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < C.n + 3 by omega)]] using (add_left_cancel this)
    exact (cyclic_two_ne_zero C.n hh).elim

theorem tail_orientation {A : Type*} (face : Fin (C.n + 3) ↪ A)
    (tail : A → V) (htail : Function.Injective tail)
    (hend : ∀ i, tail (face i) = C.vertex i ∨ tail (face i) = C.vertex (i + 1)) :
    (∀ i, tail (face i) = C.vertex i) ∨
      (∀ i, tail (face i) = C.vertex (i + 1)) := by
  classical
  by_cases h : ∃ q, tail (face q) = C.vertex q
  · obtain ⟨q, hq⟩ := h
    left
    apply cyclic_propagation (fun i => tail (face i) = C.vertex i) _ hq
    intro i hi
    rcases hend i with h | h
    · exact h
    · have heq : face i = face (i + 1) := htail (h.trans hi.symm)
      have hi1 := face.injective heq
      have hbad : (1 : Fin (C.n + 3)) = 0 := by
        exact add_left_cancel (by simpa using hi1.symm : i + 1 = i + 0)
      exact (cyclic_one_ne_zero C.n hbad).elim
  · right
    intro i
    exact (hend i).resolve_left (fun hi => h ⟨i, hi⟩)

end CycleCoordinates
end Barnette

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
def cycleEdge (i : Fin (C.n+3)) : E := (C.adjacent i).2.choose

omit [Fintype V] [Fintype E] in
lemma cycleEdge_ends (i : Fin (C.n+3)) :
    s(N.tail (N.cycleEdge C i),N.head (N.cycleEdge C i)) = s(C.vertex i,C.vertex (i+1)) :=
  Sym2.eq_iff.mpr (C.adjacent i).2.choose_spec

omit [Fintype V] [Fintype E] in
lemma cycleEdge_injective : Function.Injective (N.cycleEdge C) := by
  intro i j hij
  apply C.edge_indices_unique i j
  apply Sym2.eq_iff.mp
  rw [← N.cycleEdge_ends C i, ← N.cycleEdge_ends C j, hij]

omit [Fintype V] [Fintype E] in
lemma cycleEdge_incident (i : Fin (C.n+3)) (v : V) :
    N.Incident (N.cycleEdge C i) v ↔ v = C.vertex i ∨ v = C.vertex (i+1) := by
  rw [N.incident_iff_mem_pair, N.cycleEdge_ends]
  exact Sym2.mem_iff

omit [Fintype V] [Fintype E] in
def cycleEdges : Finset E := Finset.univ.image (N.cycleEdge C)

omit [Fintype V] [Fintype E] in
@[simp] lemma mem_cycleEdges (e : E) : e ∈ N.cycleEdges C ↔ ∃ i, N.cycleEdge C i = e := by
  simp [cycleEdges]

omit [Fintype V] in

lemma cycle_support_minimal (hN : N.Simple) (y : E → ℝ) (hy : N.boundary y = 0)
    (hsub : N.flowSupport y ⊆ N.cycleEdges C) (hne : y ≠ 0) :
    N.flowSupport y = N.cycleEdges C := by
  have hs : (N.flowSupport y).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    exact fun h => hne ((N.flowSupport_eq_empty_iff y).mp h))
  obtain ⟨e,he⟩ := hs
  obtain ⟨q,hq⟩ := (N.mem_cycleEdges C e).mp (hsub he)
  have hq' : y (N.cycleEdge C q) ≠ 0 := by rw [hq]; exact (N.mem_flowSupport _ _).mp he
  have hall : ∀ i, y (N.cycleEdge C i) ≠ 0 := by
    apply Barnette.cyclic_propagation (fun i => y (N.cycleEdge C i) ≠ 0) _ hq'
    intro i hi
    have hv : N.Incident (N.cycleEdge C (i+1)) (C.vertex (i+1)) :=
      (N.cycleEdge_incident C _ _).mpr (Or.inl rfl)
    obtain ⟨f,hfe,hyf,hfv⟩ := N.flow_no_leaf hN y hy hi hv
    obtain ⟨j,rfl⟩ := (N.mem_cycleEdges C f).mp (hsub ((N.mem_flowSupport y f).mpr hyf))
    rcases (N.cycleEdge_incident C j _).mp hfv with hj | hj
    · have hj' := C.vertex.injective hj
      exact (hfe (congrArg (N.cycleEdge C) hj'.symm)).elim
    · have hj' := add_right_cancel (C.vertex.injective hj)
      simpa only [← hj'] using hyf
  apply Finset.Subset.antisymm hsub
  intro e he
  obtain ⟨i,rfl⟩ := (N.mem_cycleEdges C e).mp he
  exact (N.mem_flowSupport y _).mpr (hall i)

omit [Fintype V] in
lemma flowCircuit_of_cycle (hN : N.Simple) (x : E → ℝ)
    (hx : N.boundary x = 0) (hs : N.flowSupport x = N.cycleEdges C) : N.FlowCircuit x := by
  have hcs : (N.cycleEdges C).Nonempty := ⟨N.cycleEdge C 0, by simp⟩
  refine ⟨hx,?_,?_⟩
  · intro hz; subst x
    have he := (N.flowSupport_eq_empty_iff 0).mpr rfl
    rw [he] at hs
    exact hcs.ne_empty hs.symm
  · intro y hy hsub
    by_cases hzero : y = 0
    · exact Or.inl hzero
    · right
      rw [hs] at hsub ⊢
      exact N.cycle_support_minimal C hN y hy hsub hzero

end
end Barnette.Network

end OAI
