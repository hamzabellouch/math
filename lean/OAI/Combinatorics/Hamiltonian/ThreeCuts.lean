import OAI.Combinatorics.Hamiltonian.ForestMatching

namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma gradient_small_support_edge (h : N.ThreeEdgeConnected) (f : V → ℝ) (s : Finset E) (hs : s.card ≤ 2)
    (hf : ∀ e, e ∉ s → N.gradient f e = 0) : N.gradient f = 0 := by
  ext e
  by_contra he
  have hne : f (N.head e) ≠ f (N.tail e) := by
    simpa only [gradient_apply, Pi.zero_apply, sub_eq_zero] using he
  let A := Finset.univ.filter fun v => f v = f (N.tail e)
  have hin : A.Nonempty := ⟨N.tail e, by simp [A]⟩
  have hout : ∃ w, w ∉ A := ⟨N.head e, by simp [A, hne]⟩
  have hsub : N.cut A ⊆ s := by
    intro k hk
    by_contra hks
    have hg : f (N.head k) = f (N.tail k) := sub_eq_zero.mp (hf k hks)
    rcases (N.mem_cut A k).mp hk with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply hh; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact hg.trans ht
    · apply ht; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact hg.symm.trans hh
  have h₁ := h A hin (by obtain ⟨w,hw⟩ := hout; exact ⟨w,Finset.mem_compl.mpr hw⟩)
  have h₂ := Finset.card_le_card hsub
  omega

variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in
theorem Duality.simple_dual_edge (h : N.Duality D)
    (h3 : N.ThreeEdgeConnected) : D.Simple := by
  have lift_zero (x : E → ℝ) (hx : D.boundary x = 0)
      (s : Finset E) (hs : s.card ≤ 2) (hxs : ∀ e, e ∉ s → x e = 0) : x = 0 := by
    have hx' : x ∈ N.gradient.range := by rw [← h.dual_cycles_eq_cuts]; exact hx
    obtain ⟨f,hf⟩ := hx'
    rw [← hf]
    exact N.gradient_small_support_edge h3 f s hs (by simpa only [hf] using hxs)
  refine ⟨?_, ?_⟩
  · intro e he
    have hz : D.boundary (basisVec e) = 0 := by
      rw [D.boundary_basis]
      ext v
      simp [incidence, he]
    have hzero := lift_zero (basisVec e) hz {e} (by simp) (by
      intro k hk; simp only [Finset.mem_singleton] at hk; simp [basisVec, hk])
    have hh := congrFun hzero e
    norm_num [basisVec] at hh
  · intro e f hef
    by_contra hne
    rcases Sym2.eq_iff.mp hef with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · have hz : D.boundary (basisVec e - basisVec f) = 0 := by
        rw [map_sub, D.boundary_basis, D.boundary_basis]
        ext v
        simp [incidence, ht, hh]
      have hzero := lift_zero (basisVec e - basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv
    · have hz : D.boundary (basisVec e + basisVec f) = 0 := by
        rw [map_add, D.boundary_basis, D.boundary_basis]
        ext v
        dsimp [incidence]
        rw [ht, hh]
        ring
      have hzero := lift_zero (basisVec e + basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv

omit [Fintype F] in
theorem Duality.cubic_face_triangles_edge (h : N.Duality D) (hN : N.Simple)
    (h3 : N.ThreeEdgeConnected)
    (hc : N.graph.IsRegularOfDegree 3) : ∀ v, Nonempty (D.Triangle (N.star v)) := by
  intro v
  have hD := h.simple_dual_edge N D h3
  have hx := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : (D.flowSupport (N.gradient (fun w => if w = v then 1 else 0))).card = 3 := by
    rw [N.gradient_indicator_support D hN, N.card_star hN, hc v]
  simpa only [N.gradient_indicator_support D hN] using D.triangle_of_flow hD _ hx hs

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma make_coloredDual (h : N.Duality D) (hN : N.Simple) (h3 : N.ThreeEdgeConnected)
    (hc : N.graph.IsRegularOfDegree 3) (black : V → Prop)
    (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) : Nonempty (N.ColoredDual D) := by
  have hs := h.simple_dual_edge N D h3
  have ht := h.cubic_face_triangles_edge N D hN h3 hc
  choose t ho using fun v => N.oriented_face D h hN hs v (ht v).some
  exact ⟨⟨h,hN,hs,hc,black,hb,t,ho⟩⟩

lemma irreducible_matching (M : N.ColoredDual D)
    (h3 : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts) (e : E) :
    ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) ∧
      (N.restrict (Subtype.val : ↥(Pᶜ) → E)).graph.Connected := by
  let root := N.blackEndpoint M.black e
  have hr := (N.blackEndpoint_spec M.black M.coloring e).1
  have he : e ∈ N.star root := (N.mem_star _ _).mpr (N.blackEndpoint_spec M.black M.coloring e).2
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ((M.face root).edge_range.symm ▸ he)
  obtain ⟨Q,hQ⟩ := M.forest_pair (M.pair_nonempty h3 htr root hr)
  simpa only [hi] using M.recover_connected_complement Q hr hQ i
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def capMap (_N : Network V E) (A : Finset V) (v : V) : Option A := if h : v ∈ A then some ⟨v,h⟩ else none

omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_some (A : Finset V) (v : A) : N.capMap A v.val = some v := by
  simp [capMap,v.property]
omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_eq_none (A : Finset V) (v : V) : N.capMap A v = none ↔ v ∉ A := by
  simp [capMap]
omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_eq_some (A : Finset V) (v : V) (w : A) :
    N.capMap A v = some w ↔ v = w.val := by
  by_cases h : v ∈ A
  · simp [capMap,h,Subtype.ext_iff]
  · simp only [capMap,dite_eq_right h,reduceCtorEq,false_iff]
    exact fun he => h (he ▸ w.property)

omit [Fintype E] in
lemma capMap_surjective (A : Finset V) (hA : Aᶜ.Nonempty) : Function.Surjective (N.capMap A) := by
  rintro (_|v)
  · obtain ⟨v,hv⟩ := hA
    exact ⟨v,(N.capMap_eq_none A v).mpr (Finset.mem_compl.mp hv)⟩
  · exact ⟨v.val,N.capMap_some A v⟩

abbrev cap (A : Finset V) : Network (Option A) (N.regionEdges A) :=
  (N.mapVertices (N.capMap A)).restrict Subtype.val

omit [Fintype V] in
lemma cap_loopless (hN : N.Simple) (A : Finset V) (e : N.regionEdges A) :
    (N.cap A).tail e ≠ (N.cap A).head e := by
  change N.capMap A (N.tail e.val) ≠ N.capMap A (N.head e.val)
  intro he
  rcases (N.mem_regionEdges A e.val).mp e.property with ht|hh
  · have ht' := N.capMap_some A ⟨N.tail e.val,ht⟩
    rw [ht'] at he
    exact hN.loopless e.val (((N.capMap_eq_some A _ _).mp he.symm).symm)
  · have hh' := N.capMap_some A ⟨N.head e.val,hh⟩
    rw [hh'] at he
    exact hN.loopless e.val ((N.capMap_eq_some A _ _).mp he)

omit [Fintype V] in
lemma cap_star_some (A : Finset V) (v : A) :
    ((N.cap A).star (some v)).image Subtype.val = N.star v.val := by
  ext e
  simp only [Finset.mem_image,mem_star,Incident]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact hk.elim (fun h => Or.inl ((N.capMap_eq_some A _ v).mp h))
      (fun h => Or.inr ((N.capMap_eq_some A _ v).mp h))
  · intro he
    have hm : e ∈ N.regionEdges A := (N.mem_regionEdges A e).mpr
      (he.elim (fun h => Or.inl (h ▸ v.property)) (fun h => Or.inr (h ▸ v.property)))
    refine ⟨⟨e,hm⟩,?_,rfl⟩
    exact he.elim (fun h => Or.inl ((N.capMap_eq_some A _ v).mpr h))
      (fun h => Or.inr ((N.capMap_eq_some A _ v).mpr h))

omit [Fintype V] in
lemma cap_star_none (A : Finset V) :
    ((N.cap A).star none).image Subtype.val = N.cut A := by
  ext e
  simp only [Finset.mem_image,mem_star,Incident,mem_cut]
  constructor
  · rintro ⟨k,hk,rfl⟩
    have hm := (N.mem_regionEdges A k.val).mp k.property
    change N.capMap A (N.tail k.val) = none ∨ N.capMap A (N.head k.val) = none at hk
    simp only [capMap_eq_none] at hk
    tauto
  · intro he
    have hm : e ∈ N.regionEdges A := (N.mem_regionEdges A e).mpr (he.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
    refine ⟨⟨e,hm⟩,?_,rfl⟩
    change N.capMap A (N.tail e) = none ∨ N.capMap A (N.head e) = none
    simp only [capMap_eq_none]
    tauto

lemma cap_star_card (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (A : Finset V) (hA : (N.cut A).card = 3) (v : Option A) : ((N.cap A).star v).card = 3 := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  cases v with
  | none => rw [N.cap_star_none,hA]
  | some v => rw [N.cap_star_some,N.card_star hN,hc v.val]

def capPreimage (A : Finset V) (B : Finset (Option A)) : Finset V :=
  Finset.univ.filter fun v => N.capMap A v ∈ B

omit [Fintype E] in
@[simp] lemma mem_capPreimage (A : Finset V) (B : Finset (Option A)) (v : V) :
    v ∈ N.capPreimage A B ↔ N.capMap A v ∈ B := by simp [capPreimage]

lemma cap_cut (A : Finset V) (B : Finset (Option A)) :
    ((N.cap A).cut B).image Subtype.val = N.cut (N.capPreimage A B) := by
  ext e
  simp only [Finset.mem_image,mem_cut,mem_capPreimage]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact hk
  · intro he
    have hm : e ∈ N.regionEdges A := by
      apply (N.mem_regionEdges A e).mpr
      by_contra hn
      have ht := (N.capMap_eq_none A (N.tail e)).mpr (not_or.mp hn).1
      have hh := (N.capMap_eq_none A (N.head e)).mpr (not_or.mp hn).2
      rw [ht,hh] at he
      tauto
    exact ⟨⟨e,hm⟩,he,rfl⟩

lemma cap_threeConnected (hN : N.ThreeEdgeConnected) (A : Finset V) (hA : Aᶜ.Nonempty) :
    (N.cap A).ThreeEdgeConnected := by
  intro B hB hBc
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,N.cap_cut]
  apply hN
  · obtain ⟨v,hv⟩ := hB
    obtain ⟨w,rfl⟩ := N.capMap_surjective A hA v
    exact ⟨w,(N.mem_capPreimage A B w).mpr hv⟩
  · obtain ⟨v,hv⟩ := hBc
    obtain ⟨w,rfl⟩ := N.capMap_surjective A hA v
    exact ⟨w,by simpa only [Finset.mem_compl,mem_capPreimage] using hv⟩

lemma ThreeEdgeConnected.connected [Nonempty V] (h : N.ThreeEdgeConnected) : N.graph.Connected := by
  apply N.connected_of_kernel_constants
  intro f hf v w
  by_contra hn
  let A := Finset.univ.filter fun z => f z = f v
  have hA : (N.cut A).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hh := (N.gradient_eq_zero_iff f).mp hf e
    have hc := (N.mem_cut A e).mp he
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,hh] at hc
    tauto
  have hc := h A ⟨v,by simp [A]⟩ ⟨w,by simp [A,Ne.symm hn]⟩
  omega

lemma threeCut_bond (h : N.ThreeEdgeConnected) (A : Finset V) (hA : (N.cut A).card = 3) : N.Bond A := by
  refine ⟨Finset.card_pos.mp (by omega),?_⟩
  intro B hB
  by_cases hn : (N.cut B).Nonempty
  · right
    obtain ⟨e,he⟩ := hn
    have hc := (N.mem_cut B e).mp he
    have hi : B.Nonempty := hc.elim (fun h => ⟨_,h.1⟩) (fun h => ⟨_,h.1⟩)
    have ho : Bᶜ.Nonempty := hc.elim (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩) (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩)
    exact Finset.eq_of_subset_of_card_le hB (by have hh := h B hi ho; omega)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hn)

omit [Fintype V] [Fintype E] in
lemma cap_connectedFibers (A : Finset V)
    (hc : (N.graph.induce {v | v ∉ A}).Connected) : N.ConnectedFibers (N.capMap A) := by
  intro v w he
  by_cases hv : v ∈ A
  · have hv' := N.capMap_some A ⟨v,hv⟩
    rw [hv'] at he
    have hh : w = v := (N.capMap_eq_some A _ _).mp he.symm
    subst w
    exact SimpleGraph.Reachable.refl v
  · have hw : w ∉ A := (N.capMap_eq_none A w).mp (he.symm.trans ((N.capMap_eq_none A v).mpr hv))
    let f : (N.graph.induce {v | v ∉ A}) →g (N.restrict (Subtype.val : N.internal (N.capMap A) → E)).graph := {
      toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        obtain ⟨hne,e,hee⟩ := hxy
        change (N.tail e = x.val ∧ N.head e = y.val) ∨ (N.tail e = y.val ∧ N.head e = x.val) at hee
        have hm : e ∈ N.internal (N.capMap A) := by
          rcases hee with ⟨ht,hh⟩|⟨ht,hh⟩ <;>
            change N.capMap A (N.tail e) = N.capMap A (N.head e) <;>
            rw [ht,hh,(N.capMap_eq_none A _).mpr x.property,(N.capMap_eq_none A _).mpr y.property]
        exact ⟨hne,⟨e,hm⟩,hee⟩ }
    exact (hc ⟨v,hv⟩ ⟨w,hw⟩).map f
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma simple_of_cubic_stars (hl : ∀ e, N.tail e ≠ N.head e)
    (hc : ∀ v, (N.star v).card = 3) (h3 : N.ThreeEdgeConnected)
    (hV : 3 ≤ Fintype.card V) : N.Simple := by
  refine ⟨hl,?_⟩
  intro e f hef
  by_contra hne
  dsimp only at hef
  let a := N.tail e
  let b := N.head e
  have hab : a ≠ b := hl e
  have hfa : N.Incident f a := (N.incident_iff_mem_pair f a).mpr (by rw [← hef]; simp [a])
  have hfb : N.Incident f b := (N.incident_iff_mem_pair f b).mpr (by rw [← hef]; simp [b])
  have hsa : ({e,f} : Finset E) ⊆ N.star a := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (N.mem_star _ _).mpr (Or.inl rfl)
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact (N.mem_star _ _).mpr hfa
  have hsb : ({e,f} : Finset E) ⊆ N.star b := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (N.mem_star _ _).mpr (Or.inr rfl)
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact (N.mem_star _ _).mpr hfb
  have hein : e ∉ N.cut {a,b} := by simp [mem_cut,a,b]
  have hfin : f ∉ N.cut {a,b} := by
    have hh := Sym2.eq_iff.mp hef
    rcases hh with ⟨ht,hh⟩|⟨ht,hh⟩ <;> simp [mem_cut,← ht,← hh,a,b]
  have hsub : N.cut {a,b} ⊆ (N.star a \ {e,f}) ∪ (N.star b \ {e,f}) := by
    intro k hk
    have hke : k ∉ ({e,f} : Finset E) := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨fun hh => hein (hh ▸ hk),fun hh => hfin (hh ▸ hk)⟩
    have hi : N.Incident k a ∨ N.Incident k b := by
      have hh := (N.mem_cut {a,b} k).mp hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      simp only [Incident]
      tauto
    exact hi.elim (fun hi => Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(N.mem_star _ _).mpr hi,hke⟩))
      (fun hi => Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(N.mem_star _ _).mpr hi,hke⟩))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset hsa,Finset.card_sdiff_of_subset hsb,hc,hc] at hcard
  simp only [Finset.card_pair hne] at hcard
  have hout : ({a,b} : Finset V)ᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,Finset.card_pair hab]
    omega
  have hh := h3 {a,b} (by simp) hout
  omega

lemma cap_simple (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (hA : 2 ≤ A.card) (ho : Aᶜ.Nonempty) :
    (N.cap A).Simple := by
  apply (N.cap A).simple_of_cubic_stars (N.cap_loopless hN A)
    (N.cap_star_card hN hc A hcut) (N.cap_threeConnected h3 A ho)
  simp only [Fintype.card_option,Fintype.card_coe]
  omega

lemma cap_cubic (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (hA : 2 ≤ A.card) (ho : Aᶜ.Nonempty) :
    (N.cap A).graph.IsRegularOfDegree 3 := by
  intro v
  rw [← (N.cap A).card_star (N.cap_simple hN hc h3 A hcut hA ho)]
  exact N.cap_star_card hN hc A hcut v

lemma threeCut_black_card (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    (N.blackCut black A).card = 0 ∨ (N.blackCut black A).card = 3 := by
  have h₁ := N.cubic_region_count hN hc A
  have h₂ := N.cubic_black_region_count hN hc black hb A
  have h₃ := Finset.card_le_card (Finset.filter_subset (fun e => N.blackEndpoint black e ∈ A) (N.cut A))
  change (N.blackCut black A).card ≤ (N.cut A).card at h₃
  omega

def capBlack (black : V → Prop) (A : Finset V) : Option A → Prop
  | none => (N.blackCut black A).card = 0
  | some v => black v.val

lemma cap_coloring (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    ∀ e, N.capBlack black A ((N.cap A).tail e) ↔ ¬N.capBlack black A ((N.cap A).head e) := by
  intro e
  have hm := (N.mem_regionEdges A e.val).mp e.property
  have hcol := hb e.val
  have hboundary : e.val ∈ N.cut A →
      ((N.blackCut black A).card = 0 ↔ N.blackEndpoint black e.val ∉ A) := by
    intro he
    rcases N.threeCut_black_card hN hc black hb A hA with hz|hf
    · have hn : N.blackEndpoint black e.val ∉ A := by
        intro hh
        have hh' : e.val ∈ N.blackCut black A := Finset.mem_filter.mpr ⟨he,hh⟩
        rw [Finset.card_eq_zero.mp hz] at hh'
        exact Finset.notMem_empty _ hh'
      simp [hz,hn]
    · have heq : N.blackCut black A = N.cut A :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hh := (Finset.mem_filter.mp (show e.val ∈ N.blackCut black A by rw [heq]; exact he)).2
      simp [hf,hh]
  change N.capBlack black A (N.capMap A (N.tail e.val)) ↔ ¬N.capBlack black A (N.capMap A (N.head e.val))
  by_cases ht : N.tail e.val ∈ A <;> by_cases hh : N.head e.val ∈ A
  · simpa only [capMap,dite_eq_left ht,dite_eq_left hh,capBlack] using hcol
  · have he : e.val ∈ N.cut A := (N.mem_cut A e.val).mpr (Or.inl ⟨ht,hh⟩)
    simp only [capMap,dite_eq_left ht,dite_eq_right hh,capBlack,hboundary he]
    by_cases hb' : black (N.tail e.val) <;> simp [blackEndpoint,hb',ht,hh]
  · have he : e.val ∈ N.cut A := (N.mem_cut A e.val).mpr (Or.inr ⟨hh,ht⟩)
    simp only [capMap,dite_eq_right ht,dite_eq_left hh,capBlack,hboundary he]
    by_cases hb' : black (N.tail e.val) <;> simp [blackEndpoint,hb',ht,hh] at hcol ⊢ <;> tauto
  · exact (hm.elim ht hh).elim
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
lemma boundary_range_restrict (s : Set E) :
    (N.restrict (Subtype.val : s → E)).boundary.range =
      Submodule.span ℝ (N.incidence.col '' s) := by
  let : DecidableEq s := Classical.decEq _
  rw [boundary, Matrix.range_toLin']
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.val, e.property, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

omit [Fintype V] in

lemma exists_independent_restriction (s : Set E) :
    ∃ r ⊆ s,
      Function.Injective (N.restrict (Subtype.val : r → E)).boundary ∧
      (N.restrict (Subtype.val : r → E)).boundary.range =
        (N.restrict (Subtype.val : s → E)).boundary.range := by
  obtain ⟨r, hrs, _, hspan, hi⟩ := exists_linearIndepOn_extension
    (v := N.incidence.col) (linearIndepOn_empty ℝ _) (Set.empty_subset s)
  refine ⟨r, hrs, ?_, ?_⟩
  · exact Matrix.mulVec_injective_iff.mpr hi
  · rw [N.boundary_range_restrict, N.boundary_range_restrict]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hrs)
    · exact Submodule.span_le.mpr hspan

variable {F : Type*} [Fintype F] (D : Network F E)

lemma duality_of_first_exact (hN : N.graph.Connected) (hD : D.graph.Connected)
    (he : N.boundary.ker = D.gradient.range) : N.Duality D := by
  have ho : ∀ f, N.boundary (D.gradient f) = 0 := by
    intro f
    change D.gradient f ∈ N.boundary.ker
    rw [he]
    exact ⟨f, rfl⟩
  have h₁ := N.dim_cycles hN
  rw [he] at h₁
  have h₂ := D.rank_gradient hD
  exact N.duality_of_orth_card D hN hD (by omega) ho

end
end Barnette.Network

end OAI
