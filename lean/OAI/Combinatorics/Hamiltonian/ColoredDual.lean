import OAI.Combinatorics.Hamiltonian.TriangleSystem

namespace OAI

/-! Colored dual networks and signed directed state cycles. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure ColoredDual where
  duality : N.Duality D
  simple : N.Simple
  dual_simple : D.Simple
  cubic : N.graph.IsRegularOfDegree 3
  black : V → Prop
  coloring : ∀ e, black (N.tail e) ↔ ¬black (N.head e)
  face : ∀ v, D.Triangle (N.star v)
  oriented : ∀ v i, N.gradient (fun w => if w = v then 1 else 0) ((face v).edge i) =
    D.arcSign ((face v).edge i) ((face v).corner i)

namespace ColoredDual
variable {N D} (M : N.ColoredDual D)

abbrev Black (root : V) := {v : V // M.black v ∧ v ≠ root}

def system (root : V) : Barnette.TriangleSystem (M.Black root) F where
  vertex t := (M.face t.val).corner
  vertex_injective t := (M.face t.val).corner_injective
  edge_unique t u i j k l hij hkl hik hjl := by
    have he : (M.face t.val).side D i j = (M.face u.val).side D k l := by
      apply M.dual_simple.pair_injective
      dsimp only
      rw [(M.face t.val).side_ends D hij,(M.face u.val).side_ends D hkl,hik,hjl]
    have ht := N.blackEndpoint_eq M.black M.coloring t.property.1
      ((N.mem_star _ _).mp ((M.face t.val).side_mem D i j))
    have hu := N.blackEndpoint_eq M.black M.coloring u.property.1
      ((N.mem_star _ _).mp ((M.face u.val).side_mem D k l))
    apply Subtype.ext
    exact ht.symm.trans (he ▸ hu)

def nonroots (root : V) : Set F := (Set.range (M.face root).corner)ᶜ

abbrev State (root : V) := (M.system root).State (M.nonroots root)

def assignment {root : V} (s : M.State root) (v : V) : F :=
  if hv : M.black v ∧ v ≠ root then s.value ⟨v,hv⟩ else (M.face root).corner 0

omit [Fintype F] in
@[simp] lemma assignment_apply {root : V} (s : M.State root) (v : M.Black root) :
    M.assignment s v.val = s.value v := by simp [assignment,v.property]

omit [Fintype F] in
lemma assignment_inj {root : V} (s : M.State root) :
    Set.InjOn (M.assignment s) {v | M.black v ∧ v ≠ root} := by
  intro v hv w hw h
  have hh : s.value ⟨v,hv⟩ = s.value ⟨w,hw⟩ :=
    (M.assignment_apply s ⟨v,hv⟩).symm.trans (h.trans (M.assignment_apply s ⟨w,hw⟩))
  exact congrArg Subtype.val (s.value_injective hh)

omit [Fintype F] in
lemma assignment_face {root : V} (s : M.State root) (v : V)
    (hv : M.black v) (hr : v ≠ root) :
    M.assignment s v ∈ Set.range (M.face v).corner := by
  rw [M.assignment_apply s ⟨v,hv,hr⟩]
  exact ⟨s.val ⟨v,hv,hr⟩,rfl⟩

omit [Fintype F] in
lemma assignment_range {root : V} (s : M.State root) (z : F) :
    z ∉ Set.range (M.face root).corner ↔
      ∃ v, M.black v ∧ v ≠ root ∧ M.assignment s v = z := by
  constructor
  · intro hz
    have hm : z ∈ M.nonroots root := hz
    obtain ⟨t,ht⟩ := (Set.ext_iff.mp s.value_range z).mpr hm
    exact ⟨t.val,t.property.1,t.property.2,(M.assignment_apply s t).trans ht⟩
  · rintro ⟨v,hv,hr,rfl⟩
    rw [M.assignment_apply s ⟨v,hv,hr⟩]
    exact s.value_mem ⟨v,hv,hr⟩

lemma cycle_disk {root : V} (s : M.State root)
    (C : Barnette.CycleCoordinates D.graph)
    (t : Fin (C.n+3) → M.Black root)
    (he : ∀ i, D.cycleEdge C i ∈ N.star (t i).val)
    (hv : ∀ i, s.value (t i) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut M.black A).card + 3 ∧
      N.blackDelta D M.black C = -3*c := by
  apply N.state_disk_delta D M.duality M.simple M.cubic M.dual_simple M.face
    M.black M.coloring root (M.assignment s) (M.assignment_inj s)
    (M.assignment_face s) (M.assignment_range s) C
  intro i
  have hb := N.blackEndpoint_eq M.black M.coloring (t i).property.1
    ((N.mem_star _ _).mp (he i))
  rw [hb]
  exact ⟨(t i).property.2,(M.assignment_apply s (t i)).trans (hv i)⟩

def weights (α : E → ℝ) (root : V) (t : M.Black root) : Fin 3 → ℝ :=
  (M.face t.val).potential D α

omit [Fintype F] in
lemma weights_diff (root : V) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root)
    (t : M.Black root) {i j : Fin 3} (hij : i ≠ j) :
    M.weights α root t j - M.weights α root t i =
      α ((M.face t.val).side D i j) *
        D.arcSign ((M.face t.val).side D i j) ((M.face t.val).corner i) := by
  apply (M.face t.val).potential_side D α _ hij
  rw [(M.face t.val).oriented_integral N D M.simple M.dual_simple t.val
    (M.oriented t.val) α,hα]
  exact whiteCharge_black M.black root t.val t.property.1 t.property.2

end ColoredDual
end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

structure StateCycle {root : V} (s : M.State root) where
  cycle : Barnette.CycleCoordinates D.graph
  face : Fin (cycle.n+3) → M.Black root
  corner : Fin (cycle.n+3) → Fin 3
  left_eq : ∀ i, s.value (face i) = cycle.vertex i
  right_eq : ∀ i, (M.face (face i).val).corner (corner i) = cycle.vertex (i+1)

namespace StateCycle
variable {M} {root : V} {s : M.State root} (C : M.StateCycle s)

omit [Fintype F] in
lemma corner_ne (i : Fin (C.cycle.n+3)) : s.val (C.face i) ≠ C.corner i := by
  intro hh
  have hv : C.cycle.vertex i = C.cycle.vertex (i+1) :=
    (C.left_eq i).symm.trans ((congrArg (M.face (C.face i).val).corner hh).trans (C.right_eq i))
  exact (C.cycle.adjacent i).1 hv

omit [Fintype F] in
lemma cycleEdge_eq (i : Fin (C.cycle.n+3)) :
    D.cycleEdge C.cycle i = (M.face (C.face i).val).side D (s.val (C.face i)) (C.corner i) := by
  apply (M.face (C.face i).val).side_unique D M.dual_simple (C.corner_ne i)
  rw [D.cycleEdge_ends,C.right_eq]
  change s(C.cycle.vertex i,C.cycle.vertex (i+1)) =
    s(s.value (C.face i),C.cycle.vertex (i+1))
  rw [C.left_eq]

omit [Fintype F] in
lemma edge_mem (i : Fin (C.cycle.n+3)) : D.cycleEdge C.cycle i ∈ N.star (C.face i).val := by
  rw [C.cycleEdge_eq]
  exact (M.face (C.face i).val).side_mem D _ _

def delta : ℤ := ∑ i, Barnette.TriangleSystem.indexDelta (s.val (C.face i)) (C.corner i)

def slope (α : E → ℝ) : ℝ :=
  ∑ i, (M.weights α root (C.face i) (C.corner i) - M.weights α root (C.face i) (s.val (C.face i)))

omit [Fintype F] in
lemma delta_eq : (C.delta : ℝ) = N.blackDelta D M.black C.cycle := by
  simp only [delta,Int.cast_sum,blackDelta]
  apply Finset.sum_congr rfl
  intro i _
  rw [(M.face (C.face i).val).index_delta N D (C.face i).val (M.oriented _)
    M.black M.coloring (C.face i).property.1 (C.corner_ne i),← C.cycleEdge_eq]
  change _ * D.arcSign _ (s.value (C.face i)) = _
  rw [C.left_eq]

omit [Fintype F] in
lemma slope_eq (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    C.slope α = ∑ e, α e * D.cycleFlow C.cycle e := by
  rw [D.cycle_integral]
  unfold slope
  apply Finset.sum_congr rfl
  intro i _
  rw [M.weights_diff root α hα (C.face i) (C.corner_ne i),← C.cycleEdge_eq]
  change _ * D.arcSign _ (s.value (C.face i)) = _
  rw [C.left_eq]

theorem signed (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    (C.delta = -3 ∧ 0 < C.slope α) ∨ (C.delta = 3 ∧ C.slope α < 0) := by
  obtain ⟨A,c,_ha,hr,hc,hflow,_hcut,hcount,hd⟩ :=
    M.cycle_disk s C.cycle C.face C.edge_mem C.left_eq
  have hδ : (C.delta : ℝ) = -3*c := C.delta_eq.trans hd
  have hs : C.slope α = c * ((A.filter fun v => ¬M.black v).card : ℝ) := by
    rw [C.slope_eq α hα]
    exact N.whiteCharge_cut_integral M.black root A hr α hα c _ hflow
  have hpos : (0:ℝ) < (A.filter fun v => ¬M.black v).card := by
    exact_mod_cast N.white_positive_of_boundary M.black M.coloring A hcount
  rcases hc with rfl | rfl
  · left
    constructor
    · have hh : (C.delta : ℝ) = (-3:ℝ) := by simpa using hδ
      exact_mod_cast hh
    · simpa [hs] using hpos
  · right
    constructor
    · have hh : (C.delta : ℝ) = (3:ℝ) := by simpa using hδ
      exact_mod_cast hh
    · simpa [hs] using neg_neg_of_pos hpos

end StateCycle
end
end Barnette.Network.ColoredDual

end OAI
