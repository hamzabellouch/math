import OAI.Combinatorics.Hamiltonian.Network

namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def cut (A : Finset V) : Finset E := Finset.univ.filter fun e =>
  (N.tail e ∈ A ∧ N.head e ∉ A) ∨ (N.head e ∈ A ∧ N.tail e ∉ A)

omit [Fintype V] in
@[simp] lemma mem_cut (A : Finset V) (e : E) : e ∈ N.cut A ↔
    (N.tail e ∈ A ∧ N.head e ∉ A) ∨ (N.head e ∈ A ∧ N.tail e ∉ A) := by
  simp [cut]

@[simp] lemma cut_compl (A : Finset V) : N.cut Aᶜ = N.cut A := by
  ext e
  simp only [mem_cut, Finset.mem_compl]
  tauto

lemma region_card_le_cut (h : ThreeVertexConnected N.graph)
    (A : Finset V) (hout : ∃ w, w ∉ A) (hc : (N.cut A).card ≤ 2) :
    A.card ≤ (N.cut A).card := by
  let p : E → V := fun e => if N.tail e ∈ A then N.tail e else N.head e
  let S := (N.cut A).image p
  have hS : S.card ≤ 2 := (Finset.card_image_le).trans hc
  have hSA : S ⊆ A := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    rcases (N.mem_cut A e).mp he with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · simpa only [p, ite_eq_left ht] using ht
    · simpa only [p, ite_eq_right ht] using hh
  have hsubset : A ⊆ S := by
    apply boundary_cover_of_threeConnected h A S hS hSA hout
    intro v hv w hw hvw
    obtain ⟨_, e, he⟩ := hvw
    apply Finset.mem_image.mpr
    rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · refine ⟨e, (N.mem_cut A e).mpr (Or.inl ?_), ?_⟩
      · simpa only [ht,hh] using And.intro hv hw
      · simp only [p, ht, hv, ite_true]
    · refine ⟨e, (N.mem_cut A e).mpr (Or.inr ?_), ?_⟩
      · simpa only [ht,hh] using And.intro hv hw
      · simp only [p, ht, hh, hw, ite_false]
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

lemma cut_card_three (h : ThreeVertexConnected N.graph)
    (hV : 5 ≤ Fintype.card V) (A : Finset V) (hin : A.Nonempty)
    (hout : ∃ w, w ∉ A) : 3 ≤ (N.cut A).card := by
  by_contra hc
  have hc' : (N.cut A).card ≤ 2 := by omega
  have ha := N.region_card_le_cut h A hout hc'
  have hccompl : (N.cut Aᶜ).card ≤ 2 := by simpa only [cut_compl] using hc'
  have hb := N.region_card_le_cut h Aᶜ (by
    obtain ⟨v,hv⟩ := hin; exact ⟨v, by simpa only [Finset.mem_compl, not_not] using hv⟩) hccompl
  rw [cut_compl] at hb
  have he := Finset.card_add_card_compl A
  omega

lemma gradient_small_support (h : ThreeVertexConnected N.graph)
    (hV : 5 ≤ Fintype.card V) (f : V → ℝ) (s : Finset E) (hs : s.card ≤ 2)
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
  have h₁ := N.cut_card_three h hV A hin hout
  have h₂ := Finset.card_le_card hsub
  omega

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

structure Simple : Prop where
  loopless : ∀ e, N.tail e ≠ N.head e
  pair_injective : Function.Injective (fun e => s(N.tail e, N.head e))

def basisVec (e : E) : E → ℝ := fun k => if k = e then 1 else 0

variable [Fintype V] [Fintype E]
omit [Fintype V] in
lemma boundary_basis (e : E) : N.boundary (basisVec e) = fun v => N.incidence v e := by
  ext v
  rw [boundary_apply, Finset.sum_eq_single e]
  · simp [basisVec, incidence]
  · intro k _ hke; simp [basisVec, hke]
  · simp

variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in

theorem Duality.simple_dual (h : N.Duality D)
    (h3 : ThreeVertexConnected N.graph) (hV : 5 ≤ Fintype.card V) : D.Simple := by
  have lift_zero (x : E → ℝ) (hx : D.boundary x = 0)
      (s : Finset E) (hs : s.card ≤ 2) (hxs : ∀ e, e ∉ s → x e = 0) : x = 0 := by
    have hx' : x ∈ N.gradient.range := by rw [← h.dual_cycles_eq_cuts]; exact hx
    obtain ⟨f,hf⟩ := hx'
    rw [← hf]
    exact N.gradient_small_support h3 hV f s hs (by simpa only [hf] using hxs)
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

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
def Incident (e : E) (v : V) : Prop := N.tail e = v ∨ N.head e = v

omit [Fintype V] [Fintype E] in
lemma incident_iff_mem_pair (e : E) (v : V) :
    N.Incident e v ↔ v ∈ s(N.tail e, N.head e) := by
  simp only [Incident, Sym2.mem_iff]
  tauto

omit [Fintype V] [Fintype E] in
lemma pair_eq_of_incident {e : E} {v w : V} (hne : v ≠ w)
    (hv : N.Incident e v) (hw : N.Incident e w) : s(N.tail e,N.head e) = s(v,w) := by
  rcases hv with ht | hh <;> rcases hw with ht' | hh'
  · exact (hne (ht.symm.trans ht')).elim
  · rw [ht,hh']
  · rw [ht',hh,Sym2.eq_swap]
  · exact (hne (hh.symm.trans hh')).elim

omit [Fintype V] [Fintype E] in
lemma Simple.incident_other (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    ∃ w, v ≠ w ∧ s(N.tail e,N.head e) = s(v,w) := by
  rcases hi with ht | hh
  · exact ⟨N.head e, ht ▸ h.loopless e, by rw [ht]⟩
  · exact ⟨N.tail e, hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

def flowSupport (_N : Network V E) (x : E → ℝ) : Finset E := Finset.univ.filter fun e => x e ≠ 0

omit [Fintype V] in
@[simp] lemma mem_flowSupport (x : E → ℝ) (e : E) :
    e ∈ N.flowSupport x ↔ x e ≠ 0 := by simp [flowSupport]

omit [Fintype V] in

lemma flow_no_leaf (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    {e : E} {v : V} (he : x e ≠ 0) (hev : N.Incident e v) :
    ∃ f, f ≠ e ∧ x f ≠ 0 ∧ N.Incident f v := by
  by_contra hn
  have other (f : E) (hfe : f ≠ e) :
      (if N.head f = v then x f else 0) - (if N.tail f = v then x f else 0) = 0 := by
    by_cases hxf : x f = 0
    · simp [hxf]
    · have hif : ¬N.Incident f v := fun hf => hn ⟨f,hfe,hxf,hf⟩
      have hh : N.head f ≠ v := fun h => hif (Or.inr h)
      have ht : N.tail f ≠ v := fun h => hif (Or.inl h)
      simp [hh,ht]
  have hz := congrFun hx v
  rw [boundary_apply, Finset.sum_eq_single e] at hz
  · rcases hev with ht | hh
    · have hh : N.head e ≠ v := fun hh => (hN.loopless e) (ht.trans hh.symm)
      simp only [hh, ht, ite_false, ite_true, zero_sub, Pi.zero_apply, neg_eq_zero] at hz
      exact he hz
    · have ht : N.tail e ≠ v := fun ht => (hN.loopless e) (ht.trans hh.symm)
      simp only [hh, ht, ite_false, ite_true, sub_zero, Pi.zero_apply] at hz
      exact he hz
  · intro f _ hfe; exact other f hfe
  · simp

structure Triangle (s : Finset E) where
  corner : Fin 3 → V
  corner_injective : Function.Injective corner
  edge : Fin 3 → E
  edge_injective : Function.Injective edge
  edge_range : Finset.univ.image edge = s
  edge_ends : ∀ i, s(N.tail (edge i), N.head (edge i)) = s(corner i, corner (i+1))

omit [Fintype V] in

theorem triangle_of_flow (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    (hs : (N.flowSupport x).card = 3) : Nonempty (N.Triangle (N.flowSupport x)) := by
  let s := N.flowSupport x
  have hspos : s.Nonempty := Finset.card_pos.mp (by dsimp [s]; omega)
  obtain ⟨e,he⟩ := hspos
  have hxe : x e ≠ 0 := (N.mem_flowSupport x e).mp he
  let a := N.tail e
  let b := N.head e
  have hab : a ≠ b := hN.loopless e
  obtain ⟨f,hfe,hxf,hfa⟩ := N.flow_no_leaf hN x hx hxe (Or.inl rfl)
  have hf : f ∈ s := (N.mem_flowSupport x f).mpr hxf
  obtain ⟨c,hac,hfc⟩ := hN.incident_other N hfa
  have hbc : b ≠ c := by
    intro hbc
    have hef : e = f := hN.pair_injective (by dsimp [a,b] at hfc ⊢; rw [hfc, ← hbc])
    exact hfe hef.symm
  have hferase : f ∈ s.erase e := Finset.mem_erase.mpr ⟨hfe,hf⟩
  have hrest : ((s.erase e).erase f).card = 1 := by
    rw [Finset.card_erase_of_mem hferase, Finset.card_erase_of_mem he]
    dsimp [s]; omega
  obtain ⟨g,hg⟩ := Finset.card_eq_one.mp hrest
  have hsEq : s = {e,f,g} := by
    calc s = insert e (s.erase e) := (Finset.insert_erase he).symm
         _ = insert e (insert f ((s.erase e).erase f)) := by rw [Finset.insert_erase hferase]
         _ = _ := by rw [hg]
  have hgmem : g ∈ (s.erase e).erase f := by rw [hg]; simp
  obtain ⟨hgf,hge,hgs⟩ := by
    simpa only [Finset.mem_erase, and_assoc] using hgmem
  have fnotb : ¬N.Incident f b := by
    rw [N.incident_iff_mem_pair, hfc]
    simp only [Sym2.mem_iff]
    exact fun h => h.elim (fun h => hab h.symm) hbc
  have enotc : ¬N.Incident e c := by
    rw [N.incident_iff_mem_pair]
    show ¬(c ∈ s(a,b))
    simp only [Sym2.mem_iff]
    exact fun h => h.elim (fun h => hac h.symm) (fun h => hbc h.symm)
  have hgb : N.Incident g b := by
    obtain ⟨k,hke,hxk,hkb⟩ := N.flow_no_leaf hN x hx hxe (Or.inr rfl)
    have hk : k ∈ s := (N.mem_flowSupport x k).mpr hxk
    rw [hsEq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (hke rfl).elim
    · exact (fnotb hkb).elim
    · exact hkb
  have hgc : N.Incident g c := by
    have hfc' : N.Incident f c := (N.incident_iff_mem_pair f c).mpr (by rw [hfc]; simp)
    obtain ⟨k,hkf,hxk,hkc⟩ := N.flow_no_leaf hN x hx hxf hfc'
    have hk : k ∈ s := (N.mem_flowSupport x k).mpr hxk
    rw [hsEq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (enotc hkc).elim
    · exact (hkf rfl).elim
    · exact hkc
  have hgend := N.pair_eq_of_incident hbc hgb hgc
  refine ⟨{
    corner := ![a,b,c]
    corner_injective := ?_
    edge := ![e,g,f]
    edge_injective := ?_
    edge_range := ?_
    edge_ends := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij <;> first | rfl | exact (hab hij).elim | exact (hab hij.symm).elim | exact (hac hij).elim | exact (hac hij.symm).elim | exact (hbc hij).elim | exact (hbc hij.symm).elim
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij <;> first | rfl | exact (hge hij).elim | exact (hge hij.symm).elim | exact (hfe hij).elim | exact (hfe hij.symm).elim | exact (hgf hij).elim | exact (hgf hij.symm).elim
  · change Finset.univ.image ![e,g,f] = s
    rw [hsEq]
    ext k
    simp [Fin.exists_fin_succ]
    tauto
  · intro i
    fin_cases i
    · rfl
    · exact hgend
    · change s(N.tail f, N.head f) = s(c,a)
      exact hfc.trans Sym2.eq_swap

end
end Barnette.Network

end OAI
