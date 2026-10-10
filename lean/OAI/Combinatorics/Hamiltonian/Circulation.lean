import OAI.Combinatorics.Hamiltonian.StateDisk

namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in

lemma FlowCircuit.proportional (x : E → ℝ) (hx : N.FlowCircuit x)
    (y : E → ℝ) (hy : N.boundary y = 0)
    (hs : N.flowSupport y ⊆ N.flowSupport x) : ∃ c : ℝ, y = c • x := by
  obtain ⟨e,he⟩ : ∃ e, x e ≠ 0 := by
    by_contra hn
    apply hx.nonzero
    ext e
    exact not_not.mp (fun he => hn ⟨e,he⟩)
  let c := y e / x e
  let z := y - c • x
  have hz : N.boundary z = 0 := by simp [z,map_sub,map_smul,hy,hx.conserved]
  have hzs : N.flowSupport z ⊆ N.flowSupport x := by
    intro k hk
    by_contra hn
    have hxk : x k = 0 := not_not.mp (by simpa only [mem_flowSupport] using hn)
    have hyk : y k = 0 := by
      by_contra hyk
      exact hn (hs ((N.mem_flowSupport y k).mpr hyk))
    exact (N.mem_flowSupport z k).mp hk (by simp [z,hxk,hyk])
  have hze : z e = 0 := by simp [z,c,div_mul_cancel₀ _ he]
  have hz0 : z = 0 := (hx.minimal z hz hzs).resolve_right (by
    intro hh
    have hem : e ∈ N.flowSupport z := hh ▸ (N.mem_flowSupport x e).mpr he
    exact (N.mem_flowSupport z e).mp hem hze)
  exact ⟨c,sub_eq_zero.mp hz0⟩

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.coordinates {s : Finset E} (t : D.Triangle s) : Barnette.CycleCoordinates D.graph where
  n := 0
  vertex := ⟨t.corner,t.corner_injective⟩
  adjacent i := t.clique D (by
    intro hh
    have h1 : (1 : Fin 3) = 0 := add_left_cancel (by simpa using hh.symm : i+1=i+0)
    norm_num at h1)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.coordinates_edge (sD : D.Simple) {s : Finset E} (t : D.Triangle s) (i : Fin 3) :
    D.cycleEdge (t.coordinates D) i = t.edge i := by
  apply sD.pair_injective
  exact (D.cycleEdge_ends (t.coordinates D) i).trans (t.edge_ends i).symm

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.coordinates_edges (sD : D.Simple) {s : Finset E} (t : D.Triangle s) :
    D.cycleEdges (t.coordinates D) = s := by
  have hf : D.cycleEdge (t.coordinates D) = t.edge := funext (t.coordinates_edge D sD)
  change Finset.univ.image (D.cycleEdge (t.coordinates D)) = s
  rw [hf]
  exact t.edge_range

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.reverse {s : Finset E} (t : D.Triangle s) : D.Triangle s where
  corner i := t.corner (-i)
  corner_injective := t.corner_injective.comp neg_injective
  edge i := t.edge (-i-1)
  edge_injective := t.edge_injective.comp (by
    intro i j hh
    apply neg_injective
    simpa only [sub_add_cancel] using congrArg (fun k : Fin 3 => k+1) hh)
  edge_range := by
    have hh : Finset.univ.image (fun i : Fin 3 => t.edge (-i-1)) = Finset.univ.image t.edge := by
      ext e
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩; exact ⟨-i-1,rfl⟩
      · rintro ⟨i,rfl⟩
        refine ⟨-i-1,?_⟩
        congr 1
        abel
    exact hh.trans t.edge_range
  edge_ends i := by
    rw [t.edge_ends]
    have h1 : -i-1+1 = -i := sub_add_cancel _ _
    have h2 : -(i+1) = -i-1 := by abel
    rw [h1,h2,Sym2.eq_swap]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma arcSign_opposite {e : E} {v w : F}
    (hne : v ≠ w) (he : s(D.tail e,D.head e) = s(v,w)) :
    D.arcSign e w = - D.arcSign e v := by
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp [arcSign,ht,hne]
  · simp [arcSign,ht,hne.symm]

omit [Fintype V] [Fintype F] in

theorem oriented_face (h : N.Duality D) (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v)) :
    ∃ u : D.Triangle (N.star v), ∀ i,
      N.gradient (fun w => if w = v then 1 else 0) (u.edge i) =
        D.arcSign (u.edge i) (u.corner i) := by
  let x := D.cycleFlow (t.coordinates D)
  let y := N.gradient (fun w => if w = v then 1 else 0)
  have hx := D.cycleFlow_circuit (t.coordinates D) sD
  have hy := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : D.flowSupport y = D.flowSupport x := by
    rw [D.cycleFlow_support,t.coordinates_edges D sD]
    exact N.gradient_indicator_support D sN v
  obtain ⟨c,hc⟩ := hx.proportional D x y hy hs.subset
  have hxi (i : Fin 3) : x (t.edge i) = D.arcSign (t.edge i) (t.corner i) := by
    have hh := D.cycleFlow_apply_edge (t.coordinates D) i
    change x (D.cycleEdge (t.coordinates D) i) = D.arcSign (D.cycleEdge (t.coordinates D) i) (t.corner i) at hh
    rw [t.coordinates_edge D sD i] at hh
    exact hh
  have hci (i : Fin 3) : y (t.edge i) = c * D.arcSign (t.edge i) (t.corner i) := by
    rw [hc,Pi.smul_apply,smul_eq_mul,hxi]
  have he : t.edge 0 ∈ N.star v := by
    have hh : t.edge 0 ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    rwa [t.edge_range] at hh
  have hcv : c = 1 ∨ c = -1 := by
    have hh := hci 0
    have hne := sN.loopless (t.edge 0)
    rcases (N.mem_star _ _).mp he with ht | hh'
    · have hhead : N.head (t.edge 0) ≠ v := fun h => hne (ht.trans h.symm)
      simp only [y,gradient_apply,ht,hhead,ite_true,ite_false,zero_sub] at hh
      by_cases hd : D.tail (t.edge 0) = t.corner 0 <;> simp [arcSign,hd] at hh <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
    · have htail : N.tail (t.edge 0) ≠ v := fun h => hne (h.trans hh'.symm)
      simp only [y,gradient_apply,hh',htail,ite_true,ite_false,sub_zero] at hh
      by_cases hd : D.tail (t.edge 0) = t.corner 0 <;> simp [arcSign,hd] at hh <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
  rcases hcv with rfl | rfl
  · exact ⟨t,fun i => by simpa only [one_mul] using hci i⟩
  · refine ⟨t.reverse D,?_⟩
    intro i
    change y (t.edge (-i-1)) = D.arcSign (t.edge (-i-1)) (t.corner (-i))
    have hh := hci (-i-1)
    have ha := D.arcSign_opposite ((t.coordinates D).adjacent (-i-1 : Fin 3)).ne (t.edge_ends (-i-1))
    change D.arcSign (t.edge (-i-1)) (t.corner (-i-1+1)) =
      - D.arcSign (t.edge (-i-1)) (t.corner (-i-1)) at ha
    rw [sub_add_cancel] at ha
    rw [ha]
    simpa only [neg_one_mul] using hh

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma boundary_of_sum_zero (h : N.graph.Connected) (b : V → ℝ)
    (hb : ∑ v, b v = 0) : ∃ x, N.boundary x = b := by
  let q : V → Unit := fun _ => ()
  have hq : Function.Surjective q := by
    obtain ⟨v⟩ := h.nonempty
    intro u
    exact ⟨v,Subsingleton.elim _ _⟩
  have hg : (N.restrict (Subtype.val : N.internal q → E)).graph = N.graph := by
    ext v w
    constructor
    · rintro ⟨hne,e,he⟩
      exact ⟨hne,e.val,he⟩
    · rintro ⟨hne,e,he⟩
      exact ⟨hne,⟨e,rfl⟩,he⟩
  have hc : N.ConnectedFibers q := by
    intro v w _
    rw [hg]
    exact h v w
  have hz : push q b = 0 := by
    ext u
    cases u
    simpa [push,q] using hb
  have hm : b ∈ (N.restrict (Subtype.val : N.internal q → E)).boundary.range := by
    rw [N.range_internal_boundary hq hc]
    exact hz
  obtain ⟨x,hx⟩ := hm
  refine ⟨push (Subtype.val : N.internal q → E) x,?_⟩
  rw [← boundary_restrict,hx]

def whiteCharge (black : V → Prop) (root : V) : V → ℝ := fun v =>
  (if black v then 0 else 1) -
    (if v = root then ((Finset.univ.filter fun w => ¬black w).card : ℝ) else 0)

lemma whiteCharge_sum (black : V → Prop) (root : V) :
    ∑ v, whiteCharge black root v = 0 := by
  simp only [whiteCharge,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [show (fun v => if black v then (0:ℝ) else 1) =
    (fun v => if ¬black v then 1 else 0) by ext v; by_cases hv : black v <;> simp [hv]]
  rw [Finset.sum_boole,sub_self]

lemma whiteCharge_black (black : V → Prop) (root v : V)
    (hv : black v) (hvr : v ≠ root) : whiteCharge black root v = 0 := by
  simp [whiteCharge,hv,hvr]

lemma whiteCharge_inside (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) :
    ∑ v ∈ A, whiteCharge black root v = ((A.filter fun v => ¬black v).card : ℝ) := by
  trans ∑ v ∈ A, if ¬black v then (1:ℝ) else 0
  · apply Finset.sum_congr rfl
    intro v hv
    have hvr : v ≠ root := fun hh => hr (hh ▸ hv)
    by_cases hb : black v <;> simp [whiteCharge,hb,hvr]
  · exact Finset.sum_boole _ _

lemma whiteCharge_cut_integral (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) (α : E → ℝ) (hα : N.boundary α = whiteCharge black root)
    (c : ℝ) (x : E → ℝ)
    (hx : x = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    ∑ e, α e * x e = c * ((A.filter fun v => ¬black v).card : ℝ) := by
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  have hh : ∑ e, α e * (c * N.gradient (fun v => if v ∈ A then 1 else 0) e) =
      c * ∑ e, α e * N.gradient (fun v => if v ∈ A then 1 else 0) e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hh,← N.boundary_adjoint,hα]
  congr 1
  simp only [mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using whiteCharge_inside black root A hr

omit [Fintype V] [Fintype F] in
lemma white_positive_of_boundary (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (A : Finset V)
    (hcount : (N.cut A).card = 2 * (N.blackCut black A).card + 3) :
    0 < (A.filter fun v => ¬black v).card := by
  by_contra hn
  have hz : (A.filter fun v => ¬black v) = ∅ := Finset.card_eq_zero.mp (by omega)
  have hb : ∀ v ∈ A, black v := by
    intro v hv
    by_contra hnv
    have hh : v ∈ A.filter (fun v => ¬black v) := Finset.mem_filter.mpr ⟨hv,hnv⟩
    rw [hz] at hh
    exact Finset.notMem_empty _ hh
  have hEq : N.blackCut black A = N.cut A := by
    apply Finset.filter_eq_self.mpr
    intro e he
    rcases (N.mem_cut A e).mp he with ht | hh
    · rw [N.blackEndpoint_eq black hc (hb _ ht.1) (Or.inl rfl)]
      exact ht.1
    · rw [N.blackEndpoint_eq black hc (hb _ hh.1) (Or.inr rfl)]
      exact hh.1
  rw [hEq] at hcount
  omega

end
end Barnette.Network

end OAI
