import OAI.Combinatorics.Hamiltonian.ThreeCuts

namespace OAI

/-! Exact duals of capped graphs and Hamiltonian walks in degree-two graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E W K : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  [Fintype W] [Fintype K]

omit [Fintype E] in
lemma push_pull_injective {j : K → E} (hj : Function.Injective j) (x : E → ℝ) :
    push j (pull j x) = fun e => if e ∈ Set.range j then x e else 0 := by
  ext e
  by_cases he : e ∈ Set.range j
  · obtain ⟨k, rfl⟩ := he
    have h := congrFun (pull_push_injective hj (pull j x)) k
    simpa only [pull_apply, Set.mem_range_self, ite_true] using h
  · rw [push_eq_zero_outside _ he]
    simp only [he, ite_false]

omit [Fintype K] in
lemma pull_push_disjoint {j : K → E} (r : Set E)
    (hr : ∀ k, j k ∉ r) (x : r → ℝ) :
    pull j (push (Subtype.val : r → E) x) = 0 := by
  ext k
  exact push_eq_zero_outside x (by simpa using hr k)

lemma split_support {j : K → E} (hj : Function.Injective j) (r : Set E)
    (hr : ∀ k, j k ∉ r) (x : E → ℝ)
    (hx : ∀ e, e ∉ r → e ∉ Set.range j → x e = 0) :
    x = push j (pull j x) + push (Subtype.val : r → E) (pull Subtype.val x) := by
  rw [push_pull_injective hj, push_pull_subtype]
  ext e
  by_cases he : e ∈ r
  · have hj' : e ∉ Set.range j := by
      rintro ⟨k, rfl⟩
      exact hr k he
    simp only [Pi.add_apply, he, hj', ite_true, ite_false, zero_add]
  · by_cases hj' : e ∈ Set.range j
    · simp only [Pi.add_apply, he, hj', ite_true, ite_false, add_zero]
    · simp only [Pi.add_apply, he, hj', ite_false, hx e he hj', zero_add]

lemma push_boundary_on_internal (N : Network V E) (q : V → W) (r : Set E)
    (hr : r ⊆ N.internal q) (x : r → ℝ) :
    push q ((N.restrict Subtype.val).boundary x) = 0 := by
  apply eq_of_dot_eq
  intro f
  rw [push_adjoint, (N.restrict _).boundary_adjoint]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro e _
  have he : (N.restrict (Subtype.val : r → E)).gradient (pull q f) e = 0 := by
    change f (q (N.head e.val)) - f (q (N.tail e.val)) = 0
    rw [show q (N.tail e.val) = q (N.head e.val) from hr e.property]
    exact sub_self _
  rw [he, mul_zero]

theorem Duality.minor (N : Network V E) (D : Network F E) (h : N.Duality D)
    (q : V → W) (hq : Function.Surjective q) (hc : N.ConnectedFibers q)
    (j : K → E) (hj : Function.Injective j)
    (hjext : ∀ k, q (N.tail (j k)) ≠ q (N.head (j k)))
    (hM : ((N.mapVertices q).restrict j).graph.Connected) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L K),
      ((N.mapVertices q).restrict j).Duality dual := by
  obtain ⟨r, hr, hir, her⟩ := N.exists_independent_restriction (N.internal q)
  have hrj : ∀ k, j k ∉ r := fun k hk => hjext k (hr hk)
  let d : Set E := {e | e ∉ r ∧ e ∉ Set.range j}
  let H := D.restrict (Subtype.val : d → E)
  let qD := H.componentMap
  let L := (D.mapVertices qD).restrict j
  let M := (N.mapVertices q).restrict j
  have hqD : Function.Surjective qD := H.componentMap_surjective
  have zeroD (f : H.Components → ℝ) (e : E) (he : e ∈ d) :
      D.gradient (pull qD f) e = 0 := congrFun (H.gradient_componentMap f) ⟨e, he⟩
  have orth (f : F → ℝ) : N.boundary (D.gradient f) = 0 := by
    change D.gradient f ∈ N.boundary.ker
    rw [h.cycles_eq_cuts]
    exact ⟨f, rfl⟩
  have hle : L.gradient.range ≤ M.boundary.ker := by
    rintro _ ⟨f, rfl⟩
    have hs := split_support hj r hrj (D.gradient (pull qD f))
      (fun e he hej => zeroD f e ⟨he, hej⟩)
    have hz := congrArg (push q) (orth (pull qD f))
    rw [hs, map_add, map_add, map_zero,
      ← boundary_restrict, ← boundary_restrict,
      push_boundary_on_internal N q r hr, add_zero] at hz
    change M.boundary (L.gradient f) = 0
    rw [boundary_restrict, boundary_mapVertices]
    simpa only [boundary_restrict, L, gradient_restrict, gradient_mapVertices] using hz
  have hge : M.boundary.ker ≤ L.gradient.range := by
    intro x hx
    have hz : push q (N.boundary (push j x)) = 0 := by
      have he : M.boundary x = 0 := hx
      simpa only [M, boundary_restrict, boundary_mapVertices] using he
    have hy : N.boundary (push j x) ∈ (N.restrict (Subtype.val : r → E)).boundary.range := by
      rw [her, N.range_internal_boundary hq hc]
      exact hz
    obtain ⟨y, hy⟩ := hy
    let z := push j x - push (Subtype.val : r → E) y
    have hzb : N.boundary z = 0 := by
      rw [map_sub, ← N.boundary_restrict (Subtype.val : r → E) y, hy, sub_self]
    have hzg : z ∈ D.gradient.range := by rw [← h.cycles_eq_cuts]; exact hzb
    obtain ⟨g, hg⟩ := hzg
    have hgH : H.gradient g = 0 := by
      ext e
      change D.gradient g e.val = 0
      rw [hg]
      have he : e.val ∉ Set.range (Subtype.val : r → E) := by simpa using e.property.1
      simp only [z, Pi.sub_apply, push_eq_zero_outside x e.property.2,
        push_eq_zero_outside y he, sub_self]
    obtain ⟨f, hf⟩ := H.descends_components g hgH
    refine ⟨f, ?_⟩
    change pull j (D.gradient (pull qD f)) = x
    rw [hf, hg, map_sub, pull_push_injective hj, pull_push_disjoint r hrj, sub_zero]
  have hLc : L.graph.Connected := by
    have : Nonempty F := h.dual_connected.nonempty
    have : Nonempty H.Components := Nonempty.map qD inferInstance
    apply L.connected_of_kernel_constants
    intro f hf a b
    have hs := split_support hj r hrj (D.gradient (pull qD f))
      (fun e he hej => zeroD f e ⟨he, hej⟩)
    have hjzero : pull j (D.gradient (pull qD f)) = 0 := hf
    rw [hjzero, map_zero, zero_add] at hs
    have hz := orth (pull qD f)
    rw [hs, ← boundary_restrict] at hz
    have hrzero : pull (Subtype.val : r → E) (D.gradient (pull qD f)) = 0 := by
      apply hir
      simpa only [map_zero] using hz
    rw [hrzero, map_zero] at hs
    obtain ⟨a', rfl⟩ := hqD a
    obtain ⟨b', rfl⟩ := hqD b
    exact D.gradient_zero_reachable hs (h.dual_connected a' b')
  exact ⟨H.Components, inferInstance, L, M.duality_of_first_exact L hM hLc (le_antisymm hge hle)⟩

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma cap_duality (h : N.Duality D) (hN : N.Simple) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (ha : A.Nonempty) (ho : Aᶜ.Nonempty) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L (N.regionEdges A)), (N.cap A).Duality dual := by
  have hshore : (N.graph.induce {v | v ∉ A}).Connected := by
    have hh := (N.threeCut_bond h3 A hcut).compl.connected_shore N h.connected ho
      (by obtain ⟨v,hv⟩ := ha; exact ⟨v,by simpa only [Finset.mem_compl,not_not] using hv⟩)
    change (N.graph.induce {v | v ∈ Aᶜ}).Connected at hh
    have heq : {v | v ∈ Aᶜ} = {v | v ∉ A} := by ext v; simp
    rw [heq] at hh
    exact hh
  exact h.minor N D (N.capMap A) (N.capMap_surjective A ho)
    (N.cap_connectedFibers A hshore) Subtype.val Subtype.val_injective
    (N.cap_loopless hN A) ((N.cap_threeConnected h3 A ho).connected (N.cap A))

lemma cap_card_lt (A : Finset V) (ho : 2 ≤ Aᶜ.card) : Fintype.card (Option A) < Fintype.card V := by
  simp only [Fintype.card_option,Fintype.card_coe]
  have hh := Finset.card_add_card_compl A
  omega

lemma nontrivial_threeCut (h : ¬N.TrivialThreeCuts) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
  unfold TrivialThreeCuts at h
  push Not at h
  obtain ⟨A,hcut,ha,ho⟩ := h
  have he : (N.cut A).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e,he⟩ := he
  have hh := (N.mem_cut A e).mp he
  have hi : A.Nonempty := hh.elim (fun h => ⟨_,h.1⟩) (fun h => ⟨_,h.1⟩)
  have hout : Aᶜ.Nonempty := hh.elim (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩) (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩)
  have hi' := Finset.card_pos.mpr hi
  have ho' := Finset.card_pos.mpr hout
  exact ⟨A,hcut,by omega,by omega⟩
end
end Barnette.Network
namespace Barnette.SimpleCycle
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

lemma cycle_at_of_connected_two [DecidableEq V] (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  have hi : G.IsCycles := by
    intro w _
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hd w
  have hn : (G.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have hh : (G.neighborSet v).ncard = 2 := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
      exact hd v
    omega
  obtain ⟨p,hp,hs⟩ := hi.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk v) rfl hn
  refine ⟨p,hp,hp.isPath_tail.isHamiltonian_of_mem ?_⟩
  intro w
  by_cases hw : w = v
  · subst w
    exact p.tail.end_mem_support
  · have hm : w ∈ p.support := by
      rw [← p.mem_verts_toSubgraph, hs]
      exact SimpleGraph.ConnectedComponent.eq.mpr (hc w v)
    rw [← p.cons_support_tail hp.not_nil] at hm
    exact (List.mem_cons.mp hm).resolve_left hw

omit [Fintype V] in
lemma induced_support_connected {a b : V} (p : G.Walk a b) (s : Set V)
    (hs : ∀ v, v ∈ s ↔ v ∈ p.support) : (G.induce s).Connected := by
  have hw : ∀ v ∈ p.support, v ∈ s := fun v hv => (hs v).mpr hv
  let q := p.induce s hw
  have hq (v : s) : v ∈ q.support := by
    simp only [q, SimpleGraph.Walk.support_induce, List.mem_attachWith]
    exact (hs v).mp v.property
  let : Nonempty s := ⟨⟨a,hw a p.start_mem_support⟩⟩
  exact ⟨fun x y => ((q.takeUntil x (hq x)).reverse.append (q.takeUntil y (hq y))).reachable⟩

lemma delete_vertex_connected (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    (G.induce {w | w ≠ v}).Connected := by
  obtain ⟨p,hp⟩ := cycle_at_of_connected_two G hc hd v
  have hn : ¬p.tail.Nil := by
    intro hh
    have hl := hp.isCycle.three_le_length
    have ht := SimpleGraph.Walk.length_eq_zero_iff.mpr hh
    simp only [SimpleGraph.Walk.length_tail] at ht
    omega
  have heq := p.tail.support_dropLast_concat hn
  have hnmem : v ∉ p.tail.dropLast.support := by
    have hnd := hp.isHamiltonian_tail.isPath.support_nodup
    rw [← heq] at hnd
    intro hm
    exact (List.nodup_append.mp hnd).2.2 v hm v (by simp) rfl
  apply induced_support_connected G p.tail.dropLast
  intro w
  constructor
  · intro hw
    have hm := hp.isHamiltonian_tail.mem_support w
    rw [←heq, List.mem_append, List.mem_singleton] at hm
    exact hm.resolve_right hw
  · intro hw h
    subst w
    exact hnmem hw
end
end Barnette.SimpleCycle

end OAI
