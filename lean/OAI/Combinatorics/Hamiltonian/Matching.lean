import OAI.Combinatorics.Hamiltonian.BMatching

namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
include C in
lemma not_acyclic : ¬ G.IsAcyclic := by
  intro ha
  apply (SimpleGraph.isAcyclic_iff_free_cycleGraph.mp ha) (C.n+3) (by omega)
  refine ⟨⟨⟨C.vertex,?_⟩,C.vertex.injective⟩⟩
  intro i j hij
  rcases SimpleGraph.cycleGraph_adj.mp hij with hij | hij
  · have hi : i = j+1 := (sub_eq_iff_eq_add.mp hij).trans (add_comm _ _)
    rw [hi]; exact (C.adjacent j).symm
  · have hj : j = i+1 := (sub_eq_iff_eq_add.mp hij).trans (add_comm _ _)
    rw [hj]; exact C.adjacent i
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma acyclic_conserved_zero (hN : N.Simple) (ha : N.graph.IsAcyclic)
    (x : E → ℝ) (hx : N.boundary x = 0) : x = 0 := by
  ext e
  let K := N.graph.deleteEdges {s(N.tail e,N.head e)}
  have he : N.graph.Adj (N.tail e) (N.head e) := ⟨hN.loopless e,e,Or.inl ⟨rfl,rfl⟩⟩
  have hb : ¬K.Reachable (N.tail e) (N.head e) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha he)
  let f : V → ℝ := fun v => if K.Reachable (N.tail e) v then 1 else 0
  have hg : N.gradient f e = -1 := by simp [gradient_apply,f,hb]
  have hk : ∀ k, k ≠ e → N.gradient f k = 0 := by
    intro k hke
    have hp : s(N.tail k,N.head k) ≠ s(N.tail e,N.head e) :=
      fun h => hke (hN.pair_injective h)
    have hadj : K.Adj (N.tail k) (N.head k) := by
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨⟨hN.loopless k,k,Or.inl ⟨rfl,rfl⟩⟩,by simpa only [Set.mem_singleton_iff] using hp⟩
    have hh : K.Reachable (N.tail e) (N.head k) ↔ K.Reachable (N.tail e) (N.tail k) :=
      ⟨fun h => h.trans hadj.reachable.symm,fun h => h.trans hadj.reachable⟩
    simp [gradient_apply,f,hh]
  have hi := N.boundary_adjoint x f
  rw [hx] at hi
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hi
  rw [Finset.sum_eq_single e] at hi
  · simpa [hg] using hi.symm
  · intro k _ hke; rw [hk k hke,mul_zero]
  · simp

omit [Fintype V] [Fintype E] in
lemma Simple.restrict (hN : N.Simple) {K : Type*} (j : K → E) (hj : Function.Injective j) :
    (N.restrict j).Simple where
  loopless k := hN.loopless (j k)
  pair_injective _ _ h := hj (hN.pair_injective h)

omit [Fintype E] in
lemma extend_restriction (S : Finset E) (x : E → ℝ) (hx : ∀ e, e ∉ S → x e = 0) :
    push (Subtype.val : S → E) (fun e => x e.val) = x := by
  ext e
  by_cases he : e ∈ S
  · exact push_subtype_apply S (fun e => x e.val) ⟨e,he⟩
  · rw [push_subtype_outside S _ he,hx e he]

lemma conserved_supported_acyclic (hN : N.Simple) (S : Finset E)
    (ha : (N.restrict (Subtype.val : S → E)).graph.IsAcyclic)
    (x : E → ℝ) (hx : N.boundary x = 0) (hs : ∀ e, e ∉ S → x e = 0) : x = 0 := by
  have hz : (N.restrict (Subtype.val : S → E)).boundary (fun e => x e.val) = 0 := by
    rw [boundary_restrict,extend_restriction S x hs,hx]
  have hh := (N.restrict (Subtype.val : S → E)).acyclic_conserved_zero
    (hN.restrict N _ Subtype.val_injective) ha _ hz
  rw [← extend_restriction S x hs,hh,map_zero]

variable {F : Type*} [Fintype F] (D : Network F E)
omit [Fintype V] in
lemma Duality.complement_connected (h : N.Duality D) (hD : D.Simple) (S : Finset E)
    (ha : (D.restrict (Subtype.val : S → E)).graph.IsAcyclic) :
    (N.restrict (Subtype.val : ↥(Sᶜ) → E)).graph.Connected := by
  have : Nonempty V := h.connected.nonempty
  apply (N.restrict (Subtype.val : ↥(Sᶜ) → E)).connected_of_kernel_constants
  intro f hf v w
  have hz : D.boundary (N.gradient f) = 0 := by
    rw [← LinearMap.mem_ker,h.dual_cycles_eq_cuts]
    exact ⟨f,rfl⟩
  have hs : ∀ e, e ∉ S → N.gradient f e = 0 := by
    intro e he
    exact congrFun hf ⟨e,Finset.mem_compl.mpr he⟩
  exact N.gradient_zero_reachable (D.conserved_supported_acyclic hD S ha _ hz hs) (h.connected v w)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

def addSink (r : Fin 2 → V) (z : V) : Network V (A ⊕ Fin 2) where
  tail := Sum.elim Q.tail r
  head := Sum.elim Q.head (fun _ => z)

lemma addSink_tail_injective (ht : Function.Injective Q.tail) (r : Fin 2 → V)
    (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i) (z : V) :
    Function.Injective (Q.addSink r z).tail := by
  rintro (a|i) (b|j) h
  · exact congrArg Sum.inl (ht h)
  · exact (hd a j h).elim
  · exact (hd b i h.symm).elim
  · exact congrArg Sum.inr (hr h)

lemma addSink_acyclic (ha : Q.graph.IsAcyclic) (ht : Function.Injective Q.tail)
    (r : Fin 2 → V) (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i)
    (z : V) (hz : z ∉ Set.range (Q.addSink r z).tail) : (Q.addSink r z).graph.IsAcyclic := by
  classical
  by_contra hnot
  obtain ⟨C⟩ := Barnette.cycleCoordinates_of_not_acyclic hnot
  let L := Q.addSink r z
  let edge : Fin (C.n+3) ↪ A ⊕ Fin 2 := ⟨L.cycleEdge C,L.cycleEdge_injective C⟩
  have hend (i) : L.tail (edge i) = C.vertex i ∨ L.tail (edge i) = C.vertex (i+1) := by
    rcases Sym2.eq_iff.mp (L.cycleEdge_ends C i) with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hor := C.tail_orientation edge L.tail (Q.addSink_tail_injective ht r hr hd z) hend
  have hrange (i) : C.vertex i ∈ Set.range L.tail := by
    rcases hor with hf|hb
    · exact ⟨edge i,hf i⟩
    · refine ⟨edge (i-1),?_⟩
      simpa using hb (i-1)
  have hbase (i) : ∃ a, edge i = Sum.inl a := by
    cases he : edge i with
    | inl a => exact ⟨a,rfl⟩
    | inr j =>
      have hh : L.head (edge i) = z := by rw [he]; rfl
      rcases Sym2.eq_iff.mp (L.cycleEdge_ends C i) with h|h
      · exact (hz (hh ▸ (h.2 ▸ hrange (i+1)))).elim
      · exact (hz (hh ▸ (h.2 ▸ hrange i))).elim
  have hc : Nonempty (Barnette.CycleCoordinates Q.graph) := by
    refine ⟨⟨C.n,C.vertex,?_⟩⟩
    intro i
    obtain ⟨a,hea⟩ := hbase i
    refine ⟨(C.adjacent i).1,a,?_⟩
    have he := L.cycleEdge_ends C i
    change s(L.tail (edge i),L.head (edge i)) = _ at he
    rw [hea] at he
    exact Sym2.eq_iff.mp he
  exact hc.elim (fun C' => C'.not_acyclic ha)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma boundary_injective_of_tree_card (hc : N.graph.Connected)
    (he : Fintype.card E + 1 = Fintype.card V) : Function.Injective N.boundary := by
  have hh := N.dim_cycles hc
  have hz : Module.finrank ℝ N.boundary.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

lemma boundary_restrict_injective (hi : Function.Injective N.boundary)
    {K : Type*} [Fintype K] (j : K → E) (hj : Function.Injective j) :
    Function.Injective (N.restrict j).boundary := by
  intro x y h
  rw [boundary_restrict,boundary_restrict] at h
  have hh := congrArg (pull j) (hi h)
  simpa only [pull_push_injective hj] using hh

omit [Fintype V] [Fintype E] in
lemma boundary_supported_vertices {K : Type*} [Fintype K] (j : K → E)
    (U : Finset V) (hU : ∀ k, N.tail (j k) ∈ U ∧ N.head (j k) ∈ U)
    (x : K → ℝ) {v : V} (hv : v ∉ U) : (N.restrict j).boundary x v = 0 := by
  rw [boundary_apply]
  apply Finset.sum_eq_zero
  intro k _
  have ht : (N.restrict j).tail k ≠ v := fun hh => hv (hh ▸ (hU k).1)
  have hh : (N.restrict j).head k ≠ v := fun hh => hv (hh ▸ (hU k).2)
  simp [ht,hh]

lemma independent_edges_bound (hi : Function.Injective N.boundary)
    (S : Finset E) (U : Finset V) (hne : U.Nonempty)
    (hU : ∀ e ∈ S, N.tail e ∈ U ∧ N.head e ∈ U) : S.card + 1 ≤ U.card := by
  obtain ⟨v,hv⟩ := hne
  let H := N.restrict (Subtype.val : S → E)
  let L : (S → ℝ) →ₗ[ℝ] (U.erase v → ℝ) := (pull Subtype.val).comp H.boundary
  have hL : Function.Injective L := by
    intro x y hxy
    apply N.boundary_restrict_injective hi Subtype.val Subtype.val_injective
    have hrow : ∀ w, w ≠ v → H.boundary x w = H.boundary y w := by
      intro w hw
      by_cases hwU : w ∈ U
      · exact congrFun hxy ⟨w,Finset.mem_erase.mpr ⟨hw,hwU⟩⟩
      · rw [N.boundary_supported_vertices Subtype.val U (fun e => hU e.val e.property) x hwU,
          N.boundary_supported_vertices Subtype.val U (fun e => hU e.val e.property) y hwU]
    ext w
    by_cases hw : w = v
    · subst w
      have hsx := H.sum_boundary x
      have hsy := H.sum_boundary y
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hsx hsy
      have hh : (∑ w ∈ Finset.univ.erase v, H.boundary x w) =
          ∑ w ∈ Finset.univ.erase v, H.boundary y w := by
        apply Finset.sum_congr rfl
        intro w hw; exact hrow w (Finset.mem_erase.mp hw).1
      linarith
    · exact hrow w hw
  have hc := LinearMap.finrank_le_finrank_of_injective hL
  simp only [Module.finrank_pi,Fintype.card_coe] at hc
  rw [Finset.card_erase_of_mem hv] at hc
  have hvp : 0 < U.card := Finset.card_pos.mpr ⟨v,hv⟩
  omega

end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

abbrev QNet (P : (M.system root).Pair (M.nonroots root)) : Network F (M.Black root) where
  tail t := P.left.value t
  head t := (M.face t.val).corner (thirdIndex (P.left.val t) (P.right.val t))

omit [Fintype F] in
lemma pair_val_ne (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    P.left.val t ≠ P.right.val t := fun h => P.partner t ((State.value_eq_iff _ _ _).mpr h)

omit [Fintype F] in
lemma q_graph (P : (M.system root).Pair (M.nonroots root)) :
    (M.QNet P).graph = (M.system root).oppositeGraph P.right := by
  ext v w
  rw [(M.system root).oppositeGraph_adj_iff P.partner]
  constructor
  · rintro ⟨_,t,h|h⟩
    · exact ⟨t,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨t,Or.inr ⟨h.1.symm,h.2.symm⟩⟩
  · rintro ⟨t,h|h⟩
    all_goals have hn := (thirdIndex_distinct _ _ (M.pair_val_ne P t)).1
    · exact ⟨fun he => hn ((M.face t.val).corner_injective (h.2.symm.trans (he.symm.trans h.1))),
        t,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨fun he => hn ((M.face t.val).corner_injective (h.2.symm.trans (he.trans h.1))),
        t,Or.inr ⟨h.1.symm,h.2.symm⟩⟩

def qLabel (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) : E :=
  (M.face t.val).side D (P.left.val t) (thirdIndex (P.left.val t) (P.right.val t))

omit [Fintype F] in
lemma qLabel_ends (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    s(D.tail (M.qLabel P t),D.head (M.qLabel P t)) =
      s((M.QNet P).tail t,(M.QNet P).head t) :=
  (M.face t.val).side_ends D (thirdIndex_distinct _ _ (M.pair_val_ne P t)).1.symm

omit [Fintype F] in
lemma qLabel_black (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    N.blackEndpoint M.black (M.qLabel P t) = t.val :=
  N.blackEndpoint_eq M.black M.coloring t.property.1
    ((N.mem_star _ _).mp ((M.face t.val).side_mem D _ _))

omit [Fintype F] in
lemma qLabel_inj (P : (M.system root).Pair (M.nonroots root)) :
    Function.Injective (M.qLabel P) := by
  intro t u h
  apply Subtype.ext
  exact (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) h).trans (M.qLabel_black P u))

def rootStart (i : Fin 3) (j : Fin 2) : Fin 3 := i + j.castLE (by decide)

lemma rootStart_inj (i : Fin 3) : Function.Injective (rootStart i) := by revert i; decide
lemma rootStart_ne (i : Fin 3) (j : Fin 2) : rootStart i j ≠ i+2 := by revert i j; decide

abbrev augQ (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) :
    Network F (M.Black root ⊕ Fin 2) :=
  (M.QNet P).addSink (fun j => (M.face root).corner (rootStart i j)) ((M.face root).corner (i+2))

omit [Fintype F] in
lemma augQ_acyclic (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (M.augQ P i).graph.IsAcyclic := by
  apply (M.QNet P).addSink_acyclic (M.q_graph P ▸ ha) P.left.value_injective _
    ((M.face root).corner_injective.comp (rootStart_inj i))
  · intro t j h
    exact P.left.value_mem t ⟨rootStart i j,h.symm⟩
  · rintro ⟨t|j,h⟩
    · exact P.left.value_mem t ⟨i+2,h.symm⟩
    · exact rootStart_ne i j ((M.face root).corner_injective h)

def augLabel (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) :
    M.Black root ⊕ Fin 2 → E :=
  Sum.elim (M.qLabel P) (fun j => (M.face root).side D (rootStart i j) (i+2))

omit [Fintype F] in
lemma augLabel_ends (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3)
    (t : M.Black root ⊕ Fin 2) :
    s(D.tail (M.augLabel P i t),D.head (M.augLabel P i t)) =
      s((M.augQ P i).tail t,(M.augQ P i).head t) := by
  cases t with
  | inl t => exact M.qLabel_ends P t
  | inr j => exact (M.face root).side_ends D (rootStart_ne i j)

omit [Fintype F] in
lemma augLabel_inj (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) : Function.Injective (M.augLabel P i) := by
  have hb (j : Fin 2) : N.blackEndpoint M.black (M.augLabel P i (.inr j)) = root :=
    N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp ((M.face root).side_mem D _ _))
  rintro (t|j) (u|k) he
  · exact congrArg Sum.inl (M.qLabel_inj P he)
  · have hh := congrArg (N.blackEndpoint M.black) he
    change N.blackEndpoint M.black (M.qLabel P t) = _ at hh
    rw [M.qLabel_black P t,hb] at hh
    exact (t.property.2 hh).elim
  · have hh := congrArg (N.blackEndpoint M.black) he
    change _ = N.blackEndpoint M.black (M.qLabel P u) at hh
    rw [hb,M.qLabel_black P u] at hh
    exact (u.property.2 hh.symm).elim
  · have hh := (M.augLabel_ends P i (.inr j)).symm.trans
      ((congrArg (fun e => s(D.tail e,D.head e)) he).trans (M.augLabel_ends P i (.inr k)))
    rcases Sym2.eq_iff.mp hh with h|h
    · exact congrArg Sum.inr (rootStart_inj i ((M.face root).corner_injective h.1))
    · exact (rootStart_ne i j ((M.face root).corner_injective h.1)).elim

def removed (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) : Finset E :=
  Finset.univ.image (M.augLabel P i)

omit [Fintype F] in
lemma removed_acyclic (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (D.restrict (Subtype.val : M.removed P i → E)).graph.IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti ?_ (M.augQ_acyclic P ha i)
  rintro v w ⟨hv,e,he⟩
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp e.property
  refine ⟨hv,k,?_⟩
  apply Sym2.eq_iff.mp
  have hh : s(D.tail e.val,D.head e.val) = s(v,w) := Sym2.eq_iff.mpr he
  rw [← hk,M.augLabel_ends] at hh
  exact hh

lemma remainder_connected (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (N.restrict (Subtype.val : ↥((M.removed P i)ᶜ) → E)).graph.Connected :=
  M.duality.complement_connected N D M.dual_simple _ (M.removed_acyclic P ha i)

omit [Fintype F] in
lemma removed_card (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root) (i : Fin 3) :
    (M.removed P i).card = (Finset.univ.filter M.black).card + 1 := by
  rw [removed,Finset.card_image_of_injective _ (M.augLabel_inj P hr i),Finset.card_univ,Fintype.card_sum]
  have hb : Fintype.card (M.Black root) + 1 = (Finset.univ.filter M.black).card := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun v => M.black v ∧ v ≠ root) =
        (Finset.univ.filter M.black).erase root := by ext; simp [and_comm]
    rw [he,Finset.card_erase_add_one (by simp [hr])]
  change Fintype.card (M.Black root) + 2 = _
  omega
end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

lemma Triangle.edge_incident {S : Finset E} (t : D.Triangle S) (i j : Fin 3) :
    D.Incident (t.edge i) (t.corner j) ↔ j = i ∨ j = i+1 := by
  rw [D.incident_iff_mem_pair,t.edge_ends,Sym2.mem_iff]
  exact or_congr t.corner_injective.eq_iff t.corner_injective.eq_iff

lemma Triangle.other_root_sides {S : Finset E} (t : D.Triangle S) (i : Fin 3) {e : E}
    (he : e ∈ S) :
    (∃ j : Fin 2, t.side D (ColoredDual.rootStart i j) (i+2) = e) ↔ e ≠ t.edge i := by
  have he' := he
  rw [← t.edge_range] at he'
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
  have hh : ∀ i k : Fin 3,
      (∃ j : Fin 2, (if i+2 = ColoredDual.rootStart i j+1 then ColoredDual.rootStart i j else i+2) = k) ↔ k ≠ i := by decide
  have hs (a b : Fin 3) : t.side D a b = t.edge (if b = a+1 then a else b) := by
    unfold Triangle.side; split_ifs <;> rfl
  simp only [hs, ne_eq, t.edge_injective.eq_iff]
  exact hh i k

lemma Triangle.opposite_characteristic {S : Finset E} (t : D.Triangle S)
    {a b : Fin 3} (hab : a ≠ b) {e : E} (he : e ∈ S) :
    e ≠ t.side D a (Barnette.TriangleSystem.thirdIndex a b) ↔ D.Incident e (t.corner b) := by
  have he' := he
  rw [← t.edge_range] at he'
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
  rw [t.edge_incident]
  have hh : ∀ a b k : Fin 3, a ≠ b →
      (k ≠ (if Barnette.TriangleSystem.thirdIndex a b = a+1 then a else Barnette.TriangleSystem.thirdIndex a b) ↔
        b = k ∨ b = k+1) := by decide
  have hs (a b : Fin 3) : t.side D a b = t.edge (if b = a+1 then a else b) := by
    unfold Triangle.side; split_ifs <;> rfl
  simp only [hs, ne_eq, t.edge_injective.eq_iff]
  exact hh a b k hab

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma removed_at_black (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) {e : E} (he : e ∈ N.star v) :
    (e ∈ M.removed P i ↔
      if h : v = root then e ≠ (M.face root).edge i else e = M.qLabel P ⟨v,hv,h⟩) := by
  have hb : N.blackEndpoint M.black e = v := N.blackEndpoint_eq M.black M.coloring hv ((N.mem_star _ _).mp he)
  by_cases hh : v = root
  · clear hb
    subst v
    simp only
    have hb : N.blackEndpoint M.black e = root := N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp he)
    constructor
    · intro hmem
      obtain ⟨t|j,_,ht⟩ := Finset.mem_image.mp hmem
      · have hbr : (t : V) = root := (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) ht).trans hb)
        exact (t.property.2 hbr).elim
      · exact ((M.face root).other_root_sides D i he).mp ⟨j,ht⟩
    · intro hne
      obtain ⟨j,hj⟩ := ((M.face root).other_root_sides D i he).mpr hne
      exact Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,hj⟩
  · simp only [dite_eq_right hh]
    constructor
    · intro hmem
      obtain ⟨t|j,_,ht⟩ := Finset.mem_image.mp hmem
      · have htv : t.val = v := (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) ht).trans hb)
        have ht' : t = ⟨v,hv,hh⟩ := Subtype.ext htv
        change M.qLabel P t = e at ht
        rw [ht'] at ht
        exact ht.symm
      · have hbr : N.blackEndpoint M.black (M.augLabel P i (.inr j)) = root :=
          N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp ((M.face root).side_mem D _ _))
        exact (hh (hb.symm.trans ((congrArg (N.blackEndpoint M.black) ht).symm.trans hbr))).elim
    · intro heq
      exact Finset.mem_image.mpr ⟨Sum.inl ⟨v,hv,hh⟩,Finset.mem_univ _,heq.symm⟩

omit [Fintype F] in
lemma remainder_black_degree (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) :
    ((N.star v).filter fun e => e ∈ (M.removed P i)ᶜ).card = if v = root then 1 else 2 := by
  by_cases hh : v = root
  · subst v
    rw [ite_eq_left rfl]
    have he : (N.star root).filter (fun e => e ∈ (M.removed P i)ᶜ) = {(M.face root).edge i} := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_compl,Finset.mem_singleton]
      constructor
      · rintro ⟨he,hn⟩
        have hm := M.removed_at_black P hr i root hr he
        simpa using (not_congr hm).mp hn
      · intro heq; subst e
        have hm : (M.face root).edge i ∈ N.star root := by
          have hx : (M.face root).edge i ∈ Finset.univ.image (M.face root).edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
          simpa only [(M.face root).edge_range] using hx
        exact ⟨hm,by rw [M.removed_at_black P hr i root hr hm]; simp⟩
    rw [he,Finset.card_singleton]
  · rw [ite_eq_right hh]
    have he : (N.star v).filter (fun e => e ∈ (M.removed P i)ᶜ) =
        (N.star v).erase (M.qLabel P ⟨v,hv,hh⟩) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_compl,Finset.mem_erase]
      constructor
      · rintro ⟨he,hn⟩
        have hm := M.removed_at_black P hr i v hv he
        simp only [dite_eq_right hh] at hm
        exact ⟨(not_congr hm).mp hn,he⟩
      · rintro ⟨hn,he⟩
        exact ⟨he,by rw [M.removed_at_black P hr i v hv he]; simpa [hh]⟩
    rw [he,Finset.card_erase_of_mem (show M.qLabel P ⟨v,hv,hh⟩ ∈ N.star v from (M.face v).side_mem D _ _),N.card_star M.simple,M.cubic v]

lemma cubic_cards : Fintype.card E = 3*(Finset.univ.filter M.black).card ∧
    Fintype.card V = 2*(Finset.univ.filter M.black).card := by
  have hdeg : ∀ v, N.graph.degree v = 3 := M.cubic
  have he := N.black_edge_partition M.black M.coloring Finset.univ
  simp only [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _),N.card_star M.simple,
    hdeg,Finset.sum_const,smul_eq_mul,Finset.card_univ] at he
  have hf := N.black_dual_card D M.duality M.simple M.cubic M.black M.coloring
  have heu := M.duality.euler N D
  constructor <;> omega

lemma remainder_independent (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    Function.Injective (N.restrict (Subtype.val : ↥((M.removed P i)ᶜ) → E)).boundary := by
  apply boundary_injective_of_tree_card _ (M.remainder_connected P ha i)
  rw [Fintype.card_coe]
  have hc := Finset.card_add_card_compl (M.removed P i)
  rw [M.removed_card P hr i] at hc
  have hE := M.cubic_cards.1
  have hV := M.cubic_cards.2
  omega

omit [Fintype F] in
lemma remainder_incident (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (t : M.Black root) {e : E} (he : e ∈ N.star t.val)
    (hm : e ∈ (M.removed P i)ᶜ) : D.Incident e (P.right.value t) := by
  have hn := (not_congr (M.removed_at_black P hr i t.val t.property.1 he)).mp (Finset.mem_compl.mp hm)
  simp only [dite_eq_right t.property.2] at hn
  exact ((M.face t.val).opposite_characteristic D (M.pair_val_ne P t) he).mp hn

end
end Barnette.Network.ColoredDual

end OAI
