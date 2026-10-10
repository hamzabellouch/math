import OAI.Combinatorics.Hamiltonian.DiskRegions

namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Duality.symm (h : N.Duality D) : D.Duality N :=
  ⟨h.dual_connected,h.connected,h.dual_cycles_eq_cuts,h.cycles_eq_cuts⟩

omit [Fintype V] [Fintype F] in

lemma Duality.vertex_flow_circuit (h : N.Duality D) (z : F)
    (hz : (D.graph.induce {v | v ≠ z}).Connected) :
    N.FlowCircuit (D.gradient (fun w => if w = z then 1 else 0)) := by
  obtain ⟨r⟩ := hz.nonempty
  let x := D.gradient (fun w => if w = z then (1:ℝ) else 0)
  have hx : N.boundary x = 0 := (h.symm N D).dual_conserved_gradient D N _
  have hn : x ≠ 0 := by
    intro he
    have hh := D.gradient_zero_reachable he (h.dual_connected z r.val)
    norm_num at hh
    exact r.property hh
  refine ⟨hx,hn,?_⟩
  intro y hy hs
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  right
  obtain ⟨f,hf⟩ := (h.symm N D).gradient_of_dual_conserved D N hy
  have fstep {v w : {v // v ≠ z}}
      (hvw : (D.graph.induce {v | v ≠ z}).Adj v w) : f v.val = f w.val := by
    obtain ⟨_,e,he⟩ := hvw
    have hxe : x e = 0 := by
      dsimp only [x,gradient_apply]
      rcases he with he | he <;> rw [he.1,he.2] <;> simp [v.property,w.property]
    have hye : y e = 0 := by
      by_contra he
      exact (N.mem_flowSupport x e).mp (hs ((N.mem_flowSupport y e).mpr he)) hxe
    have heq := congrFun hf e
    rw [hye,gradient_apply,sub_eq_zero] at heq
    exact he.elim (fun he => by rw [he.1,he.2] at heq; exact heq.symm)
      (fun he => by rwa [he.1,he.2] at heq)
  have fconstant (v : {v // v ≠ z}) : f v.val = f r.val := by
    obtain ⟨p⟩ := hz v r
    induction p with
    | nil => rfl
    | cons h p ih => exact (fstep h).trans ih
  have hne : f z ≠ f r.val := by
    intro he
    apply hy0
    rw [← hf]
    apply (D.gradient_eq_zero_iff f).mpr
    have hall (v : F) : f v = f r.val := by
      by_cases hv : v = z
      · rwa [hv]
      · exact fconstant ⟨v,hv⟩
    intro e
    exact (hall _).trans (hall _).symm
  apply Finset.Subset.antisymm hs
  intro e he
  apply (N.mem_flowSupport y e).mpr
  rw [← hf,gradient_apply]
  have hxe := (N.mem_flowSupport x e).mp he
  dsimp only [x,gradient_apply] at hxe
  by_cases ht : D.tail e = z <;> by_cases hh : D.head e = z
  · simp [ht,hh] at hxe
  · rw [ht,fconstant ⟨D.head e,hh⟩]
    exact sub_ne_zero.mpr hne.symm
  · rw [hh,fconstant ⟨D.tail e,ht⟩]
    exact sub_ne_zero.mpr hne
  · simp [ht,hh] at hxe

omit [Fintype V] in

lemma cut_restrict_conserved (x : E → ℝ) (hx : N.boundary x = 0) (A : Finset V)
    (hcut : ∀ e ∈ N.cut A, x e = 0) :
    N.boundary (fun e => if N.tail e ∈ A then x e else 0) = 0 := by
  ext v
  have hb : N.boundary (fun e => if N.tail e ∈ A then x e else 0) v =
      if v ∈ A then N.boundary x v else 0 := by
    simp only [boundary_apply]
    trans ∑ e, if v ∈ A then
      ((if N.head e = v then x e else 0) - (if N.tail e = v then x e else 0)) else 0
    swap
    · by_cases hv : v ∈ A <;> simp [hv]
    apply Finset.sum_congr rfl
    intro e _
    have hcross : N.tail e ∈ A ∨ N.head e ∈ A →
        ¬(N.tail e ∈ A ∧ N.head e ∈ A) → x e = 0 := by
      intro h1 h2
      apply hcut e
      rw [N.mem_cut]
      tauto
    by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;>
      by_cases ha : N.tail e ∈ A <;> by_cases hb : N.head e ∈ A <;>
      by_cases hv : v ∈ A <;> simp_all
  rw [hb,hx]
  simp

omit [Fintype V] in

lemma FlowCircuit.no_split (x : E → ℝ) (hx : N.FlowCircuit x) (A : Finset V)
    (hcut : ∀ e ∈ N.cut A, x e = 0)
    {e : E} (he : x e ≠ 0) (heA : N.tail e ∈ A) :
    ∀ k, x k ≠ 0 → N.tail k ∈ A := by
  let y : E → ℝ := fun k => if N.tail k ∈ A then x k else 0
  have hy := N.cut_restrict_conserved x hx.conserved A hcut
  have hs : N.flowSupport y ⊆ N.flowSupport x := by
    intro k hk
    simp only [mem_flowSupport,y] at hk ⊢
    split_ifs at hk <;> tauto
  have hyn : y ≠ 0 := by
    intro hy0
    have hh := congrFun hy0 e
    apply he
    simpa [y,heA] using hh
  have hEq := (hx.minimal y hy hs).resolve_left hyn
  intro k hk
  have hyk := (N.mem_flowSupport y k).mp (by rw [hEq]; exact (N.mem_flowSupport x k).mpr hk)
  by_contra hn
  exact hyk (by simp [y,hn])

theorem mixed_corner_on_boundary (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (A : Finset V) {z : F}
    (hzin : z ∈ N.regionVertices D A) (hzout : z ∈ N.regionVertices D Aᶜ) :
    ∃ e ∈ N.cut A, D.Incident e z := by
  by_contra hn
  have hc := h.vertex_flow_circuit N D z
    (faces_vertex_deleted_connected N D h.connected h.dual_connected sD face z)
  let x := D.gradient (fun w => if w = z then (1:ℝ) else 0)
  have hs : N.flowSupport x = D.star z := D.gradient_indicator_support N sD z
  have hcut : ∀ e ∈ N.cut A, x e = 0 := by
    intro e he
    by_contra hx
    have hh : D.Incident e z := (D.mem_star e z).mp (by
      rw [← hs]; exact (N.mem_flowSupport x e).mpr hx)
    exact hn ⟨e,he,hh⟩
  obtain ⟨e,he,hez⟩ := (N.mem_regionVertices D A z).mp hzin
  have hex : x e ≠ 0 := (N.mem_flowSupport x e).mp (by rw [hs]; exact (D.mem_star e z).mpr hez)
  have heA : N.tail e ∈ A := by
    rcases (N.mem_regionEdges A e).mp he with ht | hh
    · exact ht
    · by_contra ht
      exact hex (hcut e ((N.mem_cut A e).mpr (Or.inr ⟨hh,ht⟩)))
  have hall := hc.no_split N x A hcut hex heA
  obtain ⟨k,hk,hkz⟩ := (N.mem_regionVertices D Aᶜ z).mp hzout
  have hkx : x k ≠ 0 := (N.mem_flowSupport x k).mp (by rw [hs]; exact (D.mem_star k z).mpr hkz)
  have hkA := hall k hkx
  rcases (N.mem_regionEdges Aᶜ k).mp hk with ht | hh
  · exact (Finset.mem_compl.mp ht) hkA
  · exact hkx (hcut k ((N.mem_cut A k).mpr (Or.inl ⟨hkA,Finset.mem_compl.mp hh⟩)))

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] in
def cycleVertices (C : Barnette.CycleCoordinates D.graph) : Finset F :=
  Finset.univ.image C.vertex

omit [Fintype V] [Fintype E] [Fintype F] in
lemma mem_cycleVertices (C : Barnette.CycleCoordinates D.graph) (z : F) :
    z ∈ D.cycleVertices C ↔ ∃ i, C.vertex i = z := by
  simp [cycleVertices]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma incident_cycle_iff (C : Barnette.CycleCoordinates D.graph) (z : F) :
    (∃ e ∈ D.cycleEdges C, D.Incident e z) ↔ z ∈ D.cycleVertices C := by
  constructor
  · rintro ⟨e,he,hz⟩
    obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C e).mp he
    rw [D.incident_iff_mem_pair,D.cycleEdge_ends,Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (D.mem_cycleVertices C _).mpr ⟨i,rfl⟩
    · exact (D.mem_cycleVertices C _).mpr ⟨i+1,rfl⟩
  · intro hz
    obtain ⟨i,rfl⟩ := (D.mem_cycleVertices C z).mp hz
    refine ⟨D.cycleEdge C i,(D.mem_cycleEdges C _).mpr ⟨i,rfl⟩,?_⟩
    rw [D.incident_iff_mem_pair,D.cycleEdge_ends]; simp

omit [Fintype V] in
lemma regionVertices_iff_face (face : ∀ v, D.Triangle (N.star v))
    (A : Finset V) (z : F) :
    z ∈ N.regionVertices D A ↔ ∃ v ∈ A, z ∈ Set.range (face v).corner := by
  constructor
  · intro hz
    obtain ⟨e,he,hez⟩ := (N.mem_regionVertices D A z).mp hz
    rcases (N.mem_regionEdges A e).mp he with ht | hh
    · exact ⟨N.tail e,ht,((face _).corner_iff_incident D z).mpr
        ⟨e,(N.mem_star e _).mpr (Or.inl rfl),hez⟩⟩
    · exact ⟨N.head e,hh,((face _).corner_iff_incident D z).mpr
        ⟨e,(N.mem_star e _).mpr (Or.inr rfl),hez⟩⟩
  · rintro ⟨v,hv,hz⟩
    obtain ⟨e,he,hez⟩ := ((face v).corner_iff_incident D z).mp hz
    refine (N.mem_regionVertices D A z).mpr ⟨e,?_,hez⟩
    rcases (N.mem_star e v).mp he with ht | hh
    · exact (N.mem_regionEdges A e).mpr (Or.inl (ht ▸ hv))
    · exact (N.mem_regionEdges A e).mpr (Or.inr (hh ▸ hv))

omit [Fintype V] [Fintype E] [Fintype F] in
def blackEndpoint (black : V → Prop) (e : E) : V :=
  if black (N.tail e) then N.tail e else N.head e

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_spec (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    black (N.blackEndpoint black e) ∧ N.Incident e (N.blackEndpoint black e) := by
  by_cases ht : black (N.tail e)
  · simp only [blackEndpoint,ite_eq_left ht]; exact ⟨ht,Or.inl rfl⟩
  · simp only [blackEndpoint,ite_eq_right ht]
    exact ⟨not_not.mp (fun hh => ht ((hc e).mpr hh)),Or.inr rfl⟩

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_eq (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    {e : E} {v : V} (hv : black v) (he : N.Incident e v) :
    N.blackEndpoint black e = v := by
  rcases he with ht | hh
  · simp [blackEndpoint,ht,hv]
  · have hnt : ¬black (N.tail e) := fun ht => (hc e).mp ht (hh ▸ hv)
    simp [blackEndpoint,hnt,hh]

omit [Fintype V] [Fintype F] in
def blackCut (black : V → Prop) (A : Finset V) : Finset E :=
  (N.cut A).filter fun e => N.blackEndpoint black e ∈ A

omit [Fintype F] in
lemma cubic_black_region_count (sN : N.Simple) (hdeg : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) :
    3 * (A.filter black).card + (N.cut A).card =
      (N.regionEdges A).card + (N.blackCut black A).card := by
  have hs := N.sum_stars sN (A.filter black)
  have hd : ∀ v, N.graph.degree v = 3 := hdeg
  have hh : (∑ v ∈ A.filter black, (N.star v).card) = 3 * (A.filter black).card := by
    simp only [N.card_star sN,hd]
    simp [Nat.mul_comm]
  rw [hh] at hs
  rw [hs]
  simp only [cut,regionEdges,blackCut,Finset.card_filter,Finset.mem_filter,
    Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hcol := hc e
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;>
    by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
    simp_all [blackEndpoint]

theorem state_disk_count (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i)
    (A : Finset V) (hroot : root ∉ A) (hcut : N.cut A = D.cycleEdges C) :
    (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card := by
  let U := N.regionVertices D A
  let Z := D.cycleVertices C
  let B := A.filter black
  let M := B.image m
  let J := Finset.univ.filter fun i : Fin (C.n+3) =>
    N.blackEndpoint black (D.cycleEdge C i) ∈ A
  have face_region {v : V} (hv : v ∈ A) {z : F}
      (hz : z ∈ Set.range (face v).corner) : z ∈ U :=
    (N.regionVertices_iff_face D face A z).mpr ⟨v,hv,hz⟩
  have hZroot : ∀ z ∈ Z, z ∉ Set.range (face root).corner := by
    intro z hz
    obtain ⟨i,rfl⟩ := (D.mem_cycleVertices C z).mp hz
    apply (hm_range _).mpr
    exact ⟨_,(N.blackEndpoint_spec black hc _).1,(hchoice i).1,(hchoice i).2⟩
  have hZU : Z ⊆ U := by
    intro z hz
    obtain ⟨e,he,hez⟩ := (D.incident_cycle_iff C z).mpr hz
    rw [← hcut] at he
    refine (N.mem_regionVertices D A z).mpr ⟨e,?_,hez⟩
    rcases (N.mem_cut A e).mp he with ht | hh
    · exact (N.mem_regionEdges A e).mpr (Or.inl ht.1)
    · exact (N.mem_regionEdges A e).mpr (Or.inr hh.1)
  have hUroot : ∀ z ∈ U, z ∉ Set.range (face root).corner := by
    intro z hz hr
    have hzout : z ∈ N.regionVertices D Aᶜ :=
      (N.regionVertices_iff_face D face Aᶜ z).mpr ⟨root,Finset.mem_compl.mpr hroot,hr⟩
    have hh := N.mixed_corner_on_boundary D h sD face A hz hzout
    rw [hcut] at hh
    exact hZroot z ((D.incident_cycle_iff C z).mp hh) hr
  have hMU : M ⊆ U := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
    exact face_region hvA (hm_face v hvb (fun he => hroot (he ▸ hvA)))
  have h_union : M ∪ Z = U := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hMU hZU
    · intro z hz
      by_cases hzZ : z ∈ Z
      · exact Finset.mem_union_right _ hzZ
      obtain ⟨v,hvb,hvr,hvz⟩ := (hm_range z).mp (hUroot z hz)
      have hvA : v ∈ A := by
        by_contra hvA
        have hzout : z ∈ N.regionVertices D Aᶜ :=
          (N.regionVertices_iff_face D face Aᶜ z).mpr
            ⟨v,Finset.mem_compl.mpr hvA,hvz ▸ hm_face v hvb hvr⟩
        have hh := N.mixed_corner_on_boundary D h sD face A hz hzout
        rw [hcut] at hh
        exact hzZ ((D.incident_cycle_iff C z).mp hh)
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨v,Finset.mem_filter.mpr ⟨hvA,hvb⟩,hvz⟩)
  have h_inter : M ∩ Z = J.image C.vertex := by
    ext z
    constructor
    · rintro hz
      obtain ⟨hzM,hzZ⟩ := Finset.mem_inter.mp hz
      obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hzM
      obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi⟩ := (D.mem_cycleVertices C z).mp hzZ
      have heq : v = N.blackEndpoint black (D.cycleEdge C i) :=
        hm_inj ⟨hvb,fun he => hroot (he ▸ hvA)⟩
          ⟨(N.blackEndpoint_spec black hc _).1,(hchoice i).1⟩
          (hvz.trans (hi.symm.trans (hchoice i).2.symm))
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq ▸ hvA⟩,hi⟩
    · rintro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have hiA := (Finset.mem_filter.mp hi).2
      refine Finset.mem_inter.mpr ⟨?_,(D.mem_cycleVertices C _).mpr ⟨i,rfl⟩⟩
      exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr
        ⟨hiA,(N.blackEndpoint_spec black hc _).1⟩,(hchoice i).2⟩
  have hCJ : J.image (D.cycleEdge C) = N.blackCut black A := by
    ext e
    simp only [blackCut,Finset.mem_filter]
    constructor
    · intro he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      refine ⟨?_,(Finset.mem_filter.mp hi).2⟩
      rw [hcut]
      exact (D.mem_cycleEdges C _).mpr ⟨i,rfl⟩
    · rintro ⟨he,hb⟩
      rw [hcut] at he
      obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C e).mp he
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
  have hMcard : M.card = B.card := Finset.card_image_iff.mpr (by
    intro v hv w hw he
    obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwA,hwb⟩ := Finset.mem_filter.mp hw
    exact hm_inj ⟨hvb,fun he => hroot (he ▸ hvA)⟩
      ⟨hwb,fun he => hroot (he ▸ hwA)⟩ he)
  have hZcard : Z.card = (N.cut A).card := by
    rw [hcut]
    simp only [Z,cycleVertices,cycleEdges,Finset.card_image_of_injective _ C.vertex.injective,
      Finset.card_image_of_injective _ (D.cycleEdge_injective C)]
  have hIcard : (M ∩ Z).card = (N.blackCut black A).card := by
    rw [h_inter,← hCJ]
    rw [Finset.card_image_of_injective _ C.vertex.injective,
      Finset.card_image_of_injective _ (D.cycleEdge_injective C)]
  have hh := Finset.card_union_add_card_inter M Z
  rw [h_union,hMcard,hZcard,hIcard] at hh
  exact hh.symm

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
def blackDelta (black : V → Prop) (C : Barnette.CycleCoordinates D.graph) : ℝ :=
  ∑ i, N.gradient (fun v => if black v then 1 else 0) (D.cycleEdge C i) *
    D.arcSign (D.cycleEdge C i) (C.vertex i)

omit [Fintype V] [Fintype F] in
lemma blackDelta_cut (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (C : Barnette.CycleCoordinates D.graph) (A : Finset V) (c : ℝ)
    (hx : D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0))
    (hcut : N.cut A = D.cycleEdges C) :
    N.blackDelta D black C = c * (2 * (N.blackCut black A).card - (N.cut A).card) := by
  have hsum : N.blackDelta D black C = ∑ e ∈ N.cut A,
      N.gradient (fun v => if black v then 1 else 0) e * D.cycleFlow C e := by
    rw [hcut,cycleEdges,Finset.sum_image (D.cycleEdge_injective C).injOn]
    simp only [blackDelta,D.cycleFlow_apply_edge]
  rw [hsum]
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  have heq (e : E) (he : e ∈ N.cut A) :
      N.gradient (fun v => if black v then (1:ℝ) else 0) e *
        (c * N.gradient (fun v => if v ∈ A then 1 else 0) e) =
      c * (2 * (if N.blackEndpoint black e ∈ A then 1 else 0) - 1) := by
    have hcol := hc e
    have he' := (N.mem_cut A e).mp he
    by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;>
      by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
      simp_all [gradient_apply,blackEndpoint] <;> ring
  rw [Finset.sum_congr rfl heq,← Finset.mul_sum,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Finset.sum_boole]
  simp [blackCut]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma cycle_cut_scalar (C : Barnette.CycleCoordinates D.graph) (A : Finset V) (c : ℝ)
    (hx : D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    c = 1 ∨ c = -1 := by
  have hh := congrFun hx (D.cycleEdge C 0)
  rw [D.cycleFlow_apply_edge] at hh
  simp only [Pi.smul_apply,smul_eq_mul,gradient_apply] at hh
  by_cases ht : N.tail (D.cycleEdge C 0) ∈ A <;>
    by_cases hh' : N.head (D.cycleEdge C 0) ∈ A <;>
    by_cases hd : D.tail (D.cycleEdge C 0) = C.vertex 0 <;>
    simp [arcSign,ht,hh',hd] at hh <;>
    first | exact Or.inl (by linarith) | exact Or.inr (by linarith)

lemma disk_boundary_imbalance (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (hm : (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card) :
    (N.cut A).card = 2 * (N.blackCut black A).card + 3 := by
  have he := N.region_euler D h A hA hAc sD face
  have ht := N.cubic_region_count sN hdeg A
  have hb := N.cubic_black_region_count sN hdeg black hc A
  omega

theorem state_disk_delta (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut black A).card + 3 ∧
      N.blackDelta D black C = -3*c := by
  have hx := D.cycleFlow_circuit C sD
  obtain ⟨A,c,ha,hr,_hc0,he,hcut⟩ := h.circuit_cut N D (D.cycleFlow C) hx root
  rw [D.cycleFlow_support] at hcut
  have hb : N.Bond A := h.bond_of_circuit N D (D.cycleFlow C) hx A (by
    rw [D.cycleFlow_support]; exact hcut)
  have hA := hb.connected_shore N h.connected ha ⟨root,hr⟩
  have hAc := hb.compl.connected_shore N h.connected
    (Finset.mem_compl.mpr hr |> fun hh => ⟨root,hh⟩) (by
      obtain ⟨v,hv⟩ := ha
      exact ⟨v,by simpa using hv⟩)
  have hsides : {v : V | v ∈ Aᶜ} = {v : V | v ∉ A} := by
    ext v
    exact Finset.mem_compl
  rw [hsides] at hAc
  have hm := N.state_disk_count D h sD face black hc root m hm_inj hm_face hm_range C hchoice A hr hcut
  have hcount := N.disk_boundary_imbalance D h sN hdeg sD face black hc A hA hAc hm
  refine ⟨A,c,ha,hr,N.cycle_cut_scalar D C A c he,he,hcut,hcount,?_⟩
  rw [N.blackDelta_cut D black hc C A c he hcut,hcount]
  push_cast
  ring

end
end Barnette.Network

end OAI
