import OAI.Combinatorics.Hamiltonian.Circulation

namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

structure TriangleSystem (A V : Type*) where
  vertex : A → Fin 3 → V
  vertex_injective : ∀ t, Function.Injective (vertex t)
  edge_unique : ∀ t u i j k l, i ≠ j → k ≠ l →
    vertex t i = vertex u k → vertex t j = vertex u l → t = u

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

def State (X : Set V) :=
  {c : A → Fin 3 // Function.Injective (fun t => T.vertex t (c t)) ∧
    Set.range (fun t => T.vertex t (c t)) = X}

namespace State

variable {T} {X : Set V}

def value (s : T.State X) (t : A) : V := T.vertex t (s.val t)

theorem value_injective (s : T.State X) : Function.Injective s.value := s.property.1

theorem value_range (s : T.State X) : Set.range s.value = X := s.property.2

theorem value_mem (s : T.State X) (t : A) : s.value t ∈ X := by
  exact (Set.ext_iff.mp s.value_range _).mp ⟨t, rfl⟩

noncomputable def toEquiv (s : T.State X) : A ≃ X :=
  Equiv.ofBijective (fun t => ⟨s.value t, s.value_mem t⟩) ⟨by
    intro t u h
    exact s.value_injective (congrArg Subtype.val h), by
    intro v
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp s.value_range v.val).mpr v.property
    exact ⟨t, Subtype.ext ht⟩⟩

@[simp] theorem coe_toEquiv (s : T.State X) (t : A) : (s.toEquiv t : V) = s.value t := rfl

theorem value_eq_iff (r s : T.State X) (t : A) :
    r.value t = s.value t ↔ r.val t = s.val t := T.vertex_injective t |>.eq_iff

@[ext] theorem ext {r s : T.State X} (h : ∀ t, r.value t = s.value t) : r = s := by
  apply Subtype.ext
  funext t
  exact (value_eq_iff r s t).mp (h t)

instance [Finite A] : Finite (T.State X) := inferInstanceAs (Finite (Subtype _))

noncomputable instance [Fintype A] : Fintype (T.State X) := Fintype.ofFinite _

end State

theorem state_nonempty_iff (X : Set V) :
    Nonempty (T.State X) ↔ ∃ r : A ≃ X, ∀ t, (r t : V) ∈ Set.range (T.vertex t) := by
  classical
  constructor
  · rintro ⟨s⟩
    exact ⟨s.toEquiv, fun t => ⟨s.val t, rfl⟩⟩
  · rintro ⟨r, hr⟩
    choose c hc using hr
    refine ⟨⟨c, ?_, ?_⟩⟩
    · intro t u h
      apply r.injective
      exact Subtype.ext (by simpa only [hc] using h)
    · ext v
      constructor
      · rintro ⟨t, rfl⟩
        change T.vertex t (c t) ∈ X
        rw [hc t]
        exact (r t).property
      · intro hv
        obtain ⟨t, ht⟩ := r.surjective ⟨v, hv⟩
        exact ⟨t, (hc t).trans (congrArg Subtype.val ht)⟩

def Partner {X : Set V} (r s : T.State X) : Prop := ∀ t, r.value t ≠ s.value t

def thirdIndex (i j : Fin 3) : Fin 3 := -(i + j)

theorem thirdIndex_distinct : ∀ i j : Fin 3, i ≠ j →
    thirdIndex i j ≠ i ∧ thirdIndex i j ≠ j := by decide

theorem thirdIndex_involution : ∀ i j : Fin 3, thirdIndex (thirdIndex i j) j = i := by
  decide

theorem other_corners : ∀ i j r s : Fin 3,
    i ≠ j → i ≠ s → j ≠ s → r ≠ s →
    (i = r ∧ j = thirdIndex r s) ∨ (j = r ∧ i = thirdIndex r s) := by decide

def indexDelta (i j : Fin 3) : ℤ := if i = j then 0 else if j = i + 1 then 1 else -1

theorem indexDelta_antisymm : ∀ i j : Fin 3, indexDelta i j = -indexDelta j i := by
  decide

theorem indexDelta_third : ∀ i j : Fin 3, i ≠ j →
    indexDelta (thirdIndex i j) j - indexDelta i j =
      2 * indexDelta i (thirdIndex i j) := by decide

def oppositeGraph {X : Set V} (s : T.State X) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ t i j, T.vertex t i = v ∧ T.vertex t j = w ∧
    i ≠ s.val t ∧ j ≠ s.val t
  symm := ⟨by
    rintro v w ⟨hvw, t, i, j, hi, hj, his, hjs⟩
    exact ⟨hvw.symm, t, j, i, hj, hi, hjs, his⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem oppositeGraph_adj_iff {X : Set V} {r s : T.State X} (hrs : T.Partner r s)
    (v w : V) : (T.oppositeGraph s).Adj v w ↔
    ∃ t, (v = r.value t ∧ w = T.vertex t (thirdIndex (r.val t) (s.val t))) ∨
      (w = r.value t ∧ v = T.vertex t (thirdIndex (r.val t) (s.val t))) := by
  constructor
  · rintro ⟨hvw, t, i, j, hi, hj, his, hjs⟩
    have hij : i ≠ j := fun h => hvw (hi.symm.trans (h ▸ hj))
    have hrs' : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
    refine ⟨t, ?_⟩
    rcases other_corners i j (r.val t) (s.val t) hij his hjs hrs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hi.symm, hj.symm⟩
    · exact Or.inr ⟨hj.symm, hi.symm⟩
  · rintro ⟨t, h | h⟩
    all_goals
      have hrs' : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
      have hne := thirdIndex_distinct (r.val t) (s.val t) hrs'
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨fun heq => hne.1 (T.vertex_injective t heq.symm),
        t, r.val t, thirdIndex (r.val t) (s.val t), rfl, rfl, hrs', hne.2⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨fun heq => hne.1 (T.vertex_injective t heq),
        t, thirdIndex (r.val t) (s.val t), r.val t, rfl, rfl, hne.2, hrs'⟩

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Triangle.oriented_cycleFlow (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) :
    D.cycleFlow (t.coordinates D) = N.gradient (fun w => if w = v then 1 else 0) := by
  ext e
  by_cases he : e ∈ N.star v
  · have hh : e ∈ Finset.univ.image t.edge := t.edge_range.symm ▸ he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    have hflow := D.cycleFlow_apply_edge (t.coordinates D) i
    change D.cycleFlow (t.coordinates D) (D.cycleEdge (t.coordinates D) i) =
      D.arcSign (D.cycleEdge (t.coordinates D) i) (t.corner i) at hflow
    rw [t.coordinates_edge D sD i] at hflow
    exact hflow.trans (ht i).symm
  · have heC : e ∉ D.cycleEdges (t.coordinates D) := by
      rw [t.coordinates_edges D sD]; exact he
    rw [D.cycleFlow_zero_outside _ heC]
    have hy : e ∉ D.flowSupport (N.gradient (fun w => if w = v then 1 else 0)) := by
      rw [N.gradient_indicator_support D sN v]; exact he
    have hz : N.gradient (fun w => if w = v then 1 else 0) e = 0 := by
      simpa only [mem_flowSupport,not_not] using hy
    exact hz.symm

omit [Fintype V] [Fintype F] in
lemma cycle_integral (C : Barnette.CycleCoordinates D.graph) (α : E → ℝ) :
    ∑ e, α e * D.cycleFlow C e =
      ∑ i, α (D.cycleEdge C i) * D.arcSign (D.cycleEdge C i) (C.vertex i) := by
  simp only [cycleFlow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [basisVec,mul_ite]

omit [Fintype F] in
lemma Triangle.oriented_integral (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (α : E → ℝ) :
    ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = N.boundary α v := by
  have hh := D.cycle_integral (t.coordinates D) α
  rw [t.oriented_cycleFlow N D sN sD v ht] at hh
  have hb := N.boundary_adjoint α (fun w => if w = v then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hb
  rw [← hb] at hh
  have hf : D.cycleEdge (t.coordinates D) = t.edge := funext (t.coordinates_edge D sD)
  rw [hf] at hh
  exact hh.symm

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.potential {s : Finset E} (t : D.Triangle s) (α : E → ℝ) : Fin 3 → ℝ :=
  ![0, α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0),
    α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0) +
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1)]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.potential_step {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0) (i : Fin 3) :
    t.potential D α (i+1) - t.potential D α i =
      α (t.edge i) * D.arcSign (t.edge i) (t.corner i) := by
  have hs : α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0) +
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1) +
      α (t.edge 2) * D.arcSign (t.edge 2) (t.corner 2) = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hα
  fin_cases i
  · change t.potential D α 1 - t.potential D α 0 =
      α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0)
    simp [potential]
  · change t.potential D α 2 - t.potential D α 1 =
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1)
    simp [potential]
  · change t.potential D α 0 - t.potential D α 2 =
      α (t.edge 2) * D.arcSign (t.edge 2) (t.corner 2)
    simp [potential]
    linarith

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.side {s : Finset E} (t : D.Triangle s) (i j : Fin 3) : E :=
  if j = i+1 then t.edge i else t.edge j

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_mem {s : Finset E} (t : D.Triangle s) (i j : Fin 3) :
    t.side D i j ∈ s := by
  have hh (k : Fin 3) : t.edge k ∈ s := by
    have hm : t.edge k ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    rwa [t.edge_range] at hm
  unfold side
  split_ifs <;> apply hh

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_ends {s : Finset E} (t : D.Triangle s) {i j : Fin 3} (hij : i ≠ j) :
    s(D.tail (t.side D i j),D.head (t.side D i j)) = s(t.corner i,t.corner j) := by
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [side,ite_eq_left hj]
    exact (t.edge_ends i).trans (by rw [hj])
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [side,ite_eq_right hj]
    exact (t.edge_ends j).trans (by rw [hi,Sym2.eq_swap])

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_unique (sD : D.Simple) {s : Finset E} (t : D.Triangle s)
    {i j : Fin 3} (hij : i ≠ j) {e : E}
    (he : s(D.tail e,D.head e) = s(t.corner i,t.corner j)) : e = t.side D i j :=
  sD.pair_injective (he.trans (t.side_ends D hij).symm)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.potential_side {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    t.potential D α j - t.potential D α i =
      α (t.side D i j) * D.arcSign (t.side D i j) (t.corner i) := by
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [side,ite_eq_left hj]
    rw [hj]
    exact t.potential_step D α hα i
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [side,ite_eq_right hj]
    have hne : t.corner j ≠ t.corner i := fun h => hij (t.corner_injective h).symm
    have he : s(D.tail (t.edge j),D.head (t.edge j)) = s(t.corner j,t.corner i) := by
      rw [t.edge_ends,hi]
    rw [D.arcSign_opposite hne he]
    have hs := t.potential_step D α hα j
    rw [← hi] at hs
    linarith

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackGradient_face (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) {v : V}
    (hv : black v) {e : E} (he : N.Incident e v) :
    N.gradient (fun w => if black w then 1 else 0) e =
      N.gradient (fun w => if w = v then 1 else 0) e := by
  have hcol := hc e
  rcases he with ht | hh
  · have hhead : ¬black (N.head e) := (hc e).mp (ht ▸ hv)
    have hne : N.head e ≠ v := fun hh => hhead (hh ▸ hv)
    simp [gradient_apply,ht,hhead,hne,hv]
  · have htail : ¬black (N.tail e) := fun ht => (hc e).mp ht (hh ▸ hv)
    have hne : N.tail e ≠ v := fun ht => htail (ht ▸ hv)
    simp [gradient_apply,hh,htail,hne,hv]

omit [Fintype V] [Fintype F] in
lemma Triangle.index_delta (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (hv : black v)
    {i j : Fin 3} (hij : i ≠ j) :
    (Barnette.TriangleSystem.indexDelta i j : ℝ) =
      N.gradient (fun w => if black w then 1 else 0) (t.side D i j) *
        D.arcSign (t.side D i j) (t.corner i) := by
  rw [N.blackGradient_face black hc hv ((N.mem_star _ _).mp (t.side_mem D i j))]
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [TriangleSystem.indexDelta,ite_eq_right hij,Int.cast_one,side,ite_eq_left hj,ht]
    unfold arcSign
    split_ifs <;> norm_num
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [TriangleSystem.indexDelta,ite_eq_right hij,ite_eq_right hj,Int.cast_neg,Int.cast_one,side,ht]
    have hne : t.corner j ≠ t.corner i := fun h => hij (t.corner_injective h).symm
    have he : s(D.tail (t.edge j),D.head (t.edge j)) = s(t.corner j,t.corner i) := by
      rw [t.edge_ends,hi]
    rw [D.arcSign_opposite hne he]
    unfold arcSign
    split_ifs <;> norm_num

end
end Barnette.Network

end OAI
