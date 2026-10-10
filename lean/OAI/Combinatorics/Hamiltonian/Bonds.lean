import OAI.Combinatorics.Hamiltonian.FlowCircuits

namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
def arcSign (e : E) (v : V) : ℝ := if N.tail e = v then 1 else -1

omit [Fintype V] [Fintype E] in
lemma arcSign_ne_zero (e : E) (v : V) : N.arcSign e v ≠ 0 := by
  simp only [arcSign]; split_ifs <;> norm_num

omit [Fintype V] in
lemma boundary_directed_unit {e : E} {v w : V} (hne : v ≠ w)
    (he : s(N.tail e,N.head e) = s(v,w)) :
    N.boundary (N.arcSign e v • basisVec e) =
      fun z => (if z = w then 1 else 0) - (if z = v then 1 else 0) := by
  rw [map_smul, N.boundary_basis]
  ext z
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp only [Pi.smul_apply, smul_eq_mul, incidence, arcSign, ht, hh, ite_true, one_mul]
    congr 1 <;> simp only [eq_comm]
  · have htv : N.tail e ≠ v := by rw [ht]; exact hne.symm
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [arcSign, ite_eq_right htv]
    simp only [incidence, ht, hh, neg_one_mul, neg_sub]
    congr 1 <;> simp only [eq_comm]

omit [Fintype V] [Fintype E] in
def cycleFlow : E → ℝ :=
  ∑ i, N.arcSign (N.cycleEdge C i) (C.vertex i) • basisVec (N.cycleEdge C i)

omit [Fintype V] in
lemma cycleFlow_conserved : N.boundary (N.cycleFlow C) = 0 := by
  rw [cycleFlow,map_sum]
  have hi (i : Fin (C.n+3)) :
      N.boundary (N.arcSign (N.cycleEdge C i) (C.vertex i) • basisVec (N.cycleEdge C i)) =
        fun z => (if z = C.vertex (i+1) then 1 else 0) - (if z = C.vertex i then 1 else 0) :=
    N.boundary_directed_unit (C.adjacent i).ne (N.cycleEdge_ends C i)
  simp_rw [hi]
  ext z
  simp only [Finset.sum_apply, Pi.zero_apply, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (C.n+3))) (fun i => if z = C.vertex i then (1:ℝ) else 0)

omit [Fintype V] [Fintype E] in
lemma cycleFlow_apply_edge (i : Fin (C.n+3)) :
    N.cycleFlow C (N.cycleEdge C i) = N.arcSign (N.cycleEdge C i) (C.vertex i) := by
  simp only [cycleFlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : N.cycleEdge C i ≠ N.cycleEdge C j := fun h => hji ((N.cycleEdge_injective C h).symm)
    simp [hne]
  · simp

omit [Fintype V] [Fintype E] in
lemma cycleFlow_zero_outside {e : E} (he : e ∉ N.cycleEdges C) : N.cycleFlow C e = 0 := by
  have hi : ∀ i, e ≠ N.cycleEdge C i := by
    intro i h
    apply he
    exact (N.mem_cycleEdges C e).mpr ⟨i,h.symm⟩
  simp only [cycleFlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec, hi,
    ite_false, mul_zero, Finset.sum_const_zero]

omit [Fintype V] in
lemma cycleFlow_support : N.flowSupport (N.cycleFlow C) = N.cycleEdges C := by
  ext e
  constructor
  · intro he
    by_contra hn
    exact (N.mem_flowSupport _ _).mp he (N.cycleFlow_zero_outside C hn)
  · intro he
    obtain ⟨i,rfl⟩ := (N.mem_cycleEdges C e).mp he
    rw [mem_flowSupport, N.cycleFlow_apply_edge]
    exact N.arcSign_ne_zero _ _

omit [Fintype V] in
lemma cycleFlow_circuit (hN : N.Simple) : N.FlowCircuit (N.cycleFlow C) :=
  N.flowCircuit_of_cycle C hN _ (N.cycleFlow_conserved C) (N.cycleFlow_support C)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma support_cut (A : Finset V) :
    D.flowSupport (N.gradient (fun v => if v ∈ A then 1 else 0)) = N.cut A := by
  ext e
  simp only [mem_flowSupport,mem_cut,gradient_apply]
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;> simp [ht,hh]

structure Bond (A : Finset V) : Prop where
  nonempty : (N.cut A).Nonempty
  minimal : ∀ B, N.cut B ⊆ N.cut A → N.cut B = ∅ ∨ N.cut B = N.cut A

omit [Fintype V] [Fintype F] in
lemma Duality.bond_of_circuit (h : N.Duality D) (x : E → ℝ) (hx : D.FlowCircuit x)
    (A : Finset V) (hA : N.cut A = D.flowSupport x) : N.Bond A := by
  refine ⟨?_,?_⟩
  · rw [hA]
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun he => hx.nonzero ((D.flowSupport_eq_empty_iff x).mp he)
  · intro B hB
    let y := N.gradient (fun v => if v ∈ B then 1 else 0)
    have hy : D.flowSupport y = N.cut B := N.support_cut D B
    have hys : D.flowSupport y ⊆ D.flowSupport x := by rwa [hy,← hA]
    rcases hx.minimal y (h.dual_conserved_gradient N D _) hys with hzero | heq
    · left
      rw [← hy]
      exact (D.flowSupport_eq_empty_iff y).mpr hzero
    · right
      rwa [hy,← hA] at heq

omit [Fintype V] in
lemma cuts_equal_subset (h : N.graph.Connected) {A B : Finset V} (hBA : B ⊆ A)
    (hout : ∃ v, v ∉ A) (hc : N.cut B = N.cut A) : B = A := by
  let f : V → ℝ := fun v => (if v ∈ A then 1 else 0) - (if v ∈ B then 1 else 0)
  have hf : N.gradient f = 0 := by
    ext e
    have he := Finset.ext_iff.mp hc e
    simp only [mem_cut] at he
    have ht := hBA (x := N.tail e)
    have hh := hBA (x := N.head e)
    dsimp only [gradient_apply,f,Pi.zero_apply]
    by_cases hta : N.tail e ∈ A <;> by_cases hha : N.head e ∈ A <;>
      by_cases htb : N.tail e ∈ B <;> by_cases hhb : N.head e ∈ B <;>
      simp_all
  obtain ⟨r,hr⟩ := hout
  have hrB : r ∉ B := fun h => hr (hBA h)
  apply Finset.Subset.antisymm hBA
  intro v hv
  have hh := N.gradient_zero_reachable hf (h r v)
  by_contra hvB
  norm_num [f,hr,hrB,hv,hvB] at hh

omit [Fintype V] in
lemma cut_nonempty (h : N.graph.Connected) (A : Finset V) (hin : A.Nonempty)
    (hout : ∃ v, v ∉ A) : (N.cut A).Nonempty := by
  by_contra hc
  have hc' : N.cut A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
  have hf : N.gradient (fun v => if v ∈ A then (1:ℝ) else 0) = 0 := by
    apply (N.flowSupport_eq_empty_iff _).mp
    rwa [N.support_cut N A]
  obtain ⟨v,hv⟩ := hin
  obtain ⟨w,hw⟩ := hout
  have hh := N.gradient_zero_reachable hf (h v w)
  norm_num [hv,hw] at hh

omit [Fintype V] in

lemma Bond.connected_shore (h : N.graph.Connected) {A : Finset V} (hA : N.Bond A)
    (hin : A.Nonempty) (hout : ∃ v, v ∉ A) :
    (N.graph.induce {v | v ∈ A}).Connected := by
  obtain ⟨a,ha⟩ := hin
  let H := N.graph.induce {v | v ∈ A}
  let B := A.filter fun v => ∃ hv : v ∈ A, H.Reachable ⟨a,ha⟩ ⟨v,hv⟩
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have haB : a ∈ B := Finset.mem_filter.mpr ⟨ha,ha,SimpleGraph.Reachable.refl _⟩
  have hsub : N.cut B ⊆ N.cut A := by
    intro e he
    have step {v w : V} (hv : v ∈ B) (hw : w ∈ A) (hvw : N.graph.Adj v w) : w ∈ B := by
      obtain ⟨hvA,hvR⟩ := Finset.mem_filter.mp hv
      obtain ⟨hv',hp⟩ := hvR
      exact Finset.mem_filter.mpr ⟨hw,hw,hp.trans (show H.Adj ⟨v,hv'⟩ ⟨w,hw⟩ from hvw).reachable⟩
    rcases (N.mem_cut B e).mp he with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply (N.mem_cut A e).mpr
      refine Or.inl ⟨hBA ht,?_⟩
      intro hha
      have hne : N.tail e ≠ N.head e := fun heq => hh (heq ▸ ht)
      exact hh (step ht hha ⟨hne,e,Or.inl ⟨rfl,rfl⟩⟩)
    · apply (N.mem_cut A e).mpr
      refine Or.inr ⟨hBA hh,?_⟩
      intro hta
      have hne : N.head e ≠ N.tail e := fun heq => ht (heq ▸ hh)
      exact ht (step hh hta ⟨hne,e,Or.inr ⟨rfl,rfl⟩⟩)
  have hBout : ∃ v, v ∉ B := by
    obtain ⟨r,hr⟩ := hout
    exact ⟨r,fun h => hr (hBA h)⟩
  have hc := (hA.minimal B hsub).resolve_left (N.cut_nonempty h B ⟨a,haB⟩ hBout).ne_empty
  have hEq := N.cuts_equal_subset h hBA hout hc
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨⟨a,ha⟩,?_⟩
  intro v
  have hvB : v.val ∈ B := by rw [hEq]; exact v.property
  obtain ⟨_,hv,hp⟩ := Finset.mem_filter.mp hvB
  exact hp

lemma Bond.compl {A : Finset V} (hA : N.Bond A) : N.Bond Aᶜ where
  nonempty := by simpa only [cut_compl] using hA.nonempty
  minimal B hB := by
    rw [cut_compl] at hB ⊢
    exact hA.minimal B hB

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype E] [Fintype F] in
lemma Triangle.corner_iff_incident {s : Finset E} (t : D.Triangle s) (v : F) :
    v ∈ Set.range t.corner ↔ ∃ e ∈ s, D.Incident e v := by
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨t.edge i,?_,?_⟩
    · have hm : t.edge i ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rwa [t.edge_range] at hm
    · rw [D.incident_iff_mem_pair,t.edge_ends]; simp
  · rintro ⟨e,he,hv⟩
    rw [← t.edge_range] at he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    rw [D.incident_iff_mem_pair,t.edge_ends,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨i,rfl⟩
    · exact ⟨i+1,rfl⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.clique {s : Finset E} (t : D.Triangle s) {i j : Fin 3} (hij : i ≠ j) :
    D.graph.Adj (t.corner i) (t.corner j) := by
  have hne : t.corner i ≠ t.corner j := fun h => hij (t.corner_injective h)
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  have h := hfin i j hij
  rcases h with rfl | rfl
  · exact ⟨hne,t.edge i,Sym2.eq_iff.mp (t.edge_ends i)⟩
  · exact ⟨hne,t.edge j,(Sym2.eq_iff.mp (t.edge_ends j)).symm⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.corner_avoiding {s : Finset E} (t : D.Triangle s) (z : F) :
    ∃ w, w ∈ Set.range t.corner ∧ w ≠ z := by
  by_cases h : t.corner 0 = z
  · refine ⟨t.corner 1,⟨1,rfl⟩,?_⟩
    intro hh
    have hi := t.corner_injective (h.trans hh.symm)
    norm_num at hi
  · exact ⟨t.corner 0,⟨0,rfl⟩,h⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.reachable_avoiding {s : Finset E} (t : D.Triangle s) (z : F)
    {v w : F} (hv : v ∈ Set.range t.corner) (hw : w ∈ Set.range t.corner)
    (hvz : v ≠ z) (hwz : w ≠ z) :
    (D.graph.induce {v | v ≠ z}).Reachable ⟨v,hvz⟩ ⟨w,hwz⟩ := by
  obtain ⟨i,rfl⟩ := hv
  obtain ⟨j,rfl⟩ := hw
  by_cases hij : i = j
  · subst j; exact SimpleGraph.Reachable.refl _
  · exact (show (D.graph.induce {v | v ≠ z}).Adj ⟨t.corner i,hvz⟩ ⟨t.corner j,hwz⟩ from
      t.clique D hij).reachable

omit [Fintype V] [Fintype F] in

theorem faces_vertex_deleted_connected (hN : N.graph.Connected) (hD : D.graph.Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) (z : F) :
    (D.graph.induce {v | v ≠ z}).Connected := by
  obtain ⟨v₀⟩ := hN.nonempty
  let : Nontrivial F := ⟨⟨(face v₀).corner 0,(face v₀).corner 1,by
    intro he; have hi := (face v₀).corner_injective he; norm_num at hi⟩⟩
  let H := D.graph.induce {v | v ≠ z}
  choose anchor ha hz using fun v => (face v).corner_avoiding D z
  let a (v : V) : {w : F | w ≠ z} := ⟨anchor v,hz v⟩
  have in_face (v : V) (e : E) (he : N.Incident e v) (w : F) (hw : D.Incident e w) :
      w ∈ Set.range (face v).corner :=
    ((face v).corner_iff_incident D w).mpr ⟨e,(N.mem_star e v).mpr he,hw⟩
  have step {v w : V} (hvw : N.graph.Adj v w) : H.Reachable (a v) (a w) := by
    obtain ⟨_,e,he⟩ := hvw
    have hv : N.Incident e v := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hw : N.Incident e w := he.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
    obtain ⟨u,hu,huz⟩ : ∃ u, D.Incident e u ∧ u ≠ z := by
      by_cases ht : D.tail e = z
      · exact ⟨D.head e,Or.inr rfl,fun hh => sD.loopless e (ht.trans hh.symm)⟩
      · exact ⟨D.tail e,Or.inl rfl,ht⟩
    have p := (face v).reachable_avoiding D z (ha v) (in_face v e hv u hu) (hz v) huz
    have q := (face w).reachable_avoiding D z (in_face w e hw u hu) (ha w) huz (hz w)
    exact p.trans q
  have all_faces {v w : V} : H.Reachable (a v) (a w) := by
    obtain ⟨p⟩ := hN v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hvw p ih => exact (step hvw).trans ih
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨a v₀,?_⟩
  intro w
  obtain ⟨u,hu⟩ := hD.preconnected.exists_adj_of_nontrivial w.val
  obtain ⟨_,e,he⟩ := hu
  have hw : D.Incident e w.val := he.elim (fun he => Or.inl he.1) (fun he => Or.inr he.2)
  have hf := in_face (N.tail e) e (Or.inl rfl) w.val hw
  exact all_faces.trans ((face (N.tail e)).reachable_avoiding D z (ha _) hf (hz _) w.property)

end
end Barnette.Network

end OAI
