import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Corner

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*}

variable (inc : E → V → Prop)

structure IndexedCycle where
  size : ℕ
  four_le : 4 ≤ size
  even : size % 2 = 0
  vertex : Fin size → V
  simple : Function.Injective vertex
  edge : Fin size → E
  incidence : ∀ i v, inc (edge i) v ↔ v = vertex i ∨ v = vertex ⟨(i.val + 1) % size, Nat.mod_lt _ (by omega)⟩

namespace IndexedCycle

variable {inc} (c : IndexedCycle inc)

def index (i : ℕ) : Fin c.size := ⟨i % c.size, Nat.mod_lt i (by have := c.four_le; omega)⟩

def vertexAt (i : ℕ) : V := c.vertex (c.index i)

def edgeAt (i : ℕ) : E := c.edge (c.index i)

lemma index_succ (i : ℕ) : c.index (i + 1) = ⟨((c.index i).val + 1) % c.size, Nat.mod_lt _ (by have := c.four_le; omega)⟩ := by
  apply Fin.ext
  simp only [index, Nat.add_mod, Nat.mod_mod]

lemma vertexAt_mod (i : ℕ) : c.vertexAt (i % c.size) = c.vertexAt i := by
  exact congrArg c.vertex (Fin.ext (Nat.mod_mod i c.size))

lemma vertexAt_periodic (i : ℕ) : c.vertexAt (i + c.size) = c.vertexAt i := by
  simp [vertexAt, index]

lemma edgeAt_incidence (i : ℕ) (v : V) :
    inc (c.edgeAt i) v ↔ v = c.vertexAt i ∨ v = c.vertexAt (i + 1) := by
  simpa [edgeAt, vertexAt, c.index_succ] using c.incidence (c.index i) v

lemma mod_of_lt_twice {m x : ℕ} (hx : x < 2 * m) :
    x % m = if x < m then x else x - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma vertexAt_eq_iff {a x y : ℕ} (ha : a < c.size)
    (hx : a ≤ x ∧ x < a + c.size) (hy : a ≤ y ∧ y < a + c.size) :
    c.vertexAt x = c.vertexAt y ↔ x = y := by
  constructor
  · intro h
    have hm : x % c.size = y % c.size := congrArg Fin.val (c.simple h)
    rw [mod_of_lt_twice (by omega), mod_of_lt_twice (by omega)] at hm
    split_ifs at hm <;> omega
  · exact congrArg c.vertexAt

def arc (start length : ℕ) (hstart : start < c.size) (hpos : 0 < length)
    (hlt : length < c.size) (hodd : length % 2 = 1) : OddPath inc where
  length := length
  positive := hpos
  odd := hodd
  vertex i := c.vertexAt (start + i)
  edge i := c.edgeAt (start + i)
  simple := by
    intro i hi j hj h
    change 0 ≤ i ∧ i ≤ length at hi
    change 0 ≤ j ∧ j ≤ length at hj
    have := (c.vertexAt_eq_iff hstart
      (x := start + i) (y := start + j) (by constructor <;> omega)
      (by constructor <;> omega)).mp h
    omega
  incidence := by
    intro i hi v
    simpa [Nat.add_assoc] using c.edgeAt_incidence (start + i) v

structure Corners where
  a₀ : ℕ
  a₁ : ℕ
  a₂ : ℕ
  a₃ : ℕ
  lt₀ : a₀ < a₁
  lt₁ : a₁ < a₂
  lt₂ : a₂ < a₃
  lt₃ : a₃ < c.size
  odd₀ : (a₁ - a₀) % 2 = 1
  odd₁ : (a₂ - a₁) % 2 = 1
  odd₂ : (a₃ - a₂) % 2 = 1
  odd₃ : (c.size + a₀ - a₃) % 2 = 1

namespace Corners

variable {c} (k : c.Corners)

def start : Fin 4 → ℕ := ![k.a₀, k.a₁, k.a₂, k.a₃]

def stop : Fin 4 → ℕ := ![k.a₁, k.a₂, k.a₃, c.size + k.a₀]

def length (i : Fin 4) : ℕ := k.stop i - k.start i

lemma bounds (i : Fin 4) :
    k.a₀ ≤ k.start i ∧ k.start i < c.size ∧
    k.start i < k.stop i ∧ k.stop i ≤ k.a₀ + c.size ∧
    k.stop i < k.start i + c.size := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i <;> simp [start, stop] <;> omega

lemma length_pos (i : Fin 4) : 0 < k.length i := by
  have := k.bounds i
  dsimp [length]
  omega

lemma length_lt (i : Fin 4) : k.length i < c.size := by
  have := k.bounds i
  dsimp [length]
  omega

lemma length_odd (i : Fin 4) : k.length i % 2 = 1 := by
  fin_cases i
  · exact k.odd₀
  · exact k.odd₁
  · exact k.odd₂
  · exact k.odd₃

def side (i : Fin 4) : OddPath inc :=
  c.arc (k.start i) (k.length i) (k.bounds i).2.1 (k.length_pos i)
    (k.length_lt i) (k.length_odd i)

lemma side_vertex (i : Fin 4) (j : ℕ) :
    (k.side i).vertex j = c.vertexAt (k.start i + j) := rfl

lemma side_length (i : Fin 4) : (k.side i).length = k.length i := rfl

lemma side_first (i : Fin 4) : (k.side i).vertex 0 = c.vertexAt (k.start i) := by
  simp [side_vertex]

lemma side_last (i : Fin 4) : (k.side i).vertex (k.side i).length =
    c.vertexAt (k.stop i) := by
  rw [side_vertex, side_length]
  congr 1
  dsimp [length]
  have := k.bounds i
  omega

lemma joins (i : Fin 4) : (k.side i).vertex (k.side i).length =
    (k.side (i + 1)).vertex 0 := by
  rw [side_last, side_first]
  fin_cases i <;> simp [start, stop]
  simpa only [Nat.add_comm] using c.vertexAt_periodic k.a₀

lemma starts_injective : Function.Injective k.start := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [start] <;> omega

lemma corners_injective : Function.Injective fun i => (k.side i).vertex 0 := by
  intro i j h
  simp only [side_first] at h
  have hi := k.bounds i
  have hj := k.bounds j
  have ha : k.a₀ < c.size := by have := k.lt₀; omega
  apply k.starts_injective
  exact (c.vertexAt_eq_iff ha ⟨hi.1, by omega⟩ ⟨hj.1, by omega⟩).mp h

variable [DecidableEq V]

lemma inside_iff (i : Fin 4) (v : V) :
    v ∈ (k.side i).inside ↔
      ∃ t, k.start i < t ∧ t < k.stop i ∧ c.vertexAt t = v := by
  simp only [OddPath.inside, Finset.mem_image, Finset.mem_Icc, side_length, side_vertex]
  constructor
  · rintro ⟨j, hj, h⟩
    refine ⟨k.start i + j, by omega, ?_, h⟩
    have := k.bounds i
    dsimp [length] at hj
    omega
  · rintro ⟨t, hlow, hhigh, h⟩
    refine ⟨t - k.start i, ?_, ?_⟩
    · dsimp [length]
      constructor <;> omega
    · have he : k.start i + (t - k.start i) = t := by omega
      simpa [he] using h

omit [DecidableEq V] in
lemma interior_ranges_disjoint (i j : Fin 4) (hij : i ≠ j) (t : ℕ)
    (hi : k.start i < t ∧ t < k.stop i) :
    ¬ (k.start j < t ∧ t < k.stop j) := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i <;> fin_cases j <;> simp_all [start, stop] <;> omega

lemma interiors_disjoint : Pairwise fun i j => Disjoint (k.side i).inside (k.side j).inside := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hv hw
  obtain ⟨x, hx₁, hx₂, hx⟩ := (k.inside_iff i v).mp hv
  obtain ⟨y, hy₁, hy₂, hy⟩ := (k.inside_iff j v).mp hw
  have hi := k.bounds i
  have hj := k.bounds j
  have ha : k.a₀ < c.size := by have := k.lt₀; omega
  have hxy := (c.vertexAt_eq_iff ha (x := x) (y := y)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).mp (hx.trans hy.symm)
  subst y
  exact k.interior_ranges_disjoint i j hij x ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩

omit [DecidableEq V] in
lemma interior_not_corner_index (i j : Fin 4) (t : ℕ)
    (ht : k.start i < t ∧ t < k.stop i) : t ≠ k.start j := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i <;> fin_cases j <;> simp_all [start, stop] <;> omega

lemma interior_ne_corner (i j : Fin 4) {v : V} (hv : v ∈ (k.side i).inside) :
    v ≠ (k.side j).vertex 0 := by
  intro heq
  obtain ⟨t, ht₁, ht₂, ht⟩ := (k.inside_iff i v).mp hv
  have hi := k.bounds i
  have hj := k.bounds j
  have ha : k.a₀ < c.size := by have := k.lt₀; omega
  have h := (c.vertexAt_eq_iff ha (x := t) (y := k.start j)
    ⟨by omega, by omega⟩ ⟨hj.1, by omega⟩).mp (ht.trans (by simpa [side_first] using heq))
  exact k.interior_not_corner_index i j t ⟨ht₁, ht₂⟩ h

lemma interior_ends_disjoint (i j : Fin 4) : Disjoint (k.side i).inside (k.side j).ends := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  simp only [OddPath.ends, Finset.mem_insert, Finset.mem_singleton, k.joins] at hw
  exact hw.elim (k.interior_ne_corner i j hv) (k.interior_ne_corner i (j+1) hv)

def cellPaths (chord : Fin 4 → E)
    (hchord : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length) : CellPaths inc where
  side := k.side
  joins := k.joins
  corners_injective := k.corners_injective
  interiors_disjoint := k.interiors_disjoint
  interior_ends_disjoint := k.interior_ends_disjoint
  chord := chord
  chord_incidence := hchord

end Corners

end IndexedCycle

end

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_mod (i : ℕ) : c.edgeAt (i % c.size) = c.edgeAt i := by
  exact congrArg c.edge (Fin.ext (Nat.mod_mod i c.size))

lemma consecutive_ne (i : ℕ) (hi : i < c.size) : c.edgeAt i ≠ c.edgeAt (i+1) := by
  intro he
  have hm : inc (c.edgeAt (i+1)) (c.vertexAt i) := he ▸
    (c.edgeAt_incidence i _).mpr (Or.inl rfl)
  rcases (c.edgeAt_incidence (i+1) _).mp hm with h | h
  · have := (c.vertexAt_eq_iff hi (x := i) (y := i+1)
      (by have := c.four_le; omega) (by have := c.four_le; omega)).mp h
    omega
  · have := (c.vertexAt_eq_iff hi (x := i) (y := i+1+1)
      (by have := c.four_le; omega) (by have := c.four_le; omega)).mp h
    omega

lemma edges_reachable (U : Finset E) (hU : ∀ i, c.edgeAt i ∈ U) (i : ℕ) :
    (overlayLineGraph inc U).Reachable (c.edgeAt 0) (c.edgeAt i) := by
  suffices hs : ∀ j, j < c.size →
      (overlayLineGraph inc U).Reachable (c.edgeAt 0) (c.edgeAt j) by
    simpa only [c.edgeAt_mod] using hs (i % c.size)
      (Nat.mod_lt i (by have := c.four_le; omega))
  intro j hj
  induction j with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
      apply (ih (by omega)).trans
      apply SimpleGraph.Adj.reachable
      refine ⟨c.consecutive_ne j (by omega), hU j, hU (j+1), ?_⟩
      exact ⟨c.vertexAt (j+1), (c.edgeAt_incidence j _).mpr (Or.inr rfl),
        (c.edgeAt_incidence (j+1) _).mpr (Or.inl rfl)⟩

section

variable [Fintype V] [DecidableEq E]

lemma adjacent_mem_complement {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (i : ℕ) (hi : i < c.size) :
    c.edgeAt (i+1) ∈ M ↔ c.edgeAt i ∉ M := by
  have hein := (c.edgeAt_incidence i (c.vertexAt (i+1))).mpr (Or.inr rfl)
  have hfin := (c.edgeAt_incidence (i+1) (c.vertexAt (i+1))).mpr (Or.inl rfl)
  constructor
  · intro hf he
    exact c.consecutive_ne i hi (hM.unique (Finset.mem_univ _) he hein hf hfin)
  · intro he
    have heN := (Finset.mem_union.mp (hU i)).resolve_left he
    rcases Finset.mem_union.mp (hU (i+1)) with hf | hf
    · exact hf
    · exact False.elim (c.consecutive_ne i hi (hN.unique (Finset.mem_univ _) heN hein hf hfin))

lemma cycle_edge_mem_complement {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (i : ℕ) :
    c.edgeAt i ∈ N ↔ c.edgeAt i ∉ M := by
  have hm : i % c.size < c.size := Nat.mod_lt i (by have := c.four_le; omega)
  have heq := c.edgeAt_mod i
  have h := c.adjacent_mem_complement hM hN hU (i % c.size) hm
  have hn := c.adjacent_mem_complement hN hM
    (fun j => by rw [Finset.union_comm]; exact hU j) (i % c.size) hm
  constructor
  · intro hiN hiM
    have hjM : c.edgeAt (i % c.size + 1) ∉ M := fun hj => (h.mp hj) (heq.symm ▸ hiM)
    have hjN : c.edgeAt (i % c.size + 1) ∉ N := fun hj => (hn.mp hj) (heq.symm ▸ hiN)
    exact (Finset.mem_union.mp (hU _)).elim hjM hjN
  · intro hiM
    exact (Finset.mem_union.mp (hU i)).resolve_left hiM

lemma cycle_edge_mem_parity {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (i : ℕ) :
    c.edgeAt i ∈ M ↔ if i % 2 = 0 then c.edgeAt 0 ∈ M else c.edgeAt 0 ∉ M := by
  have hb : ∀ j, j < c.size →
      (c.edgeAt j ∈ M ↔ if j % 2 = 0 then c.edgeAt 0 ∈ M else c.edgeAt 0 ∉ M) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        rw [c.adjacent_mem_complement hM hN hU j (by omega), ih (by omega)]
        split_ifs <;> first | omega | tauto
  have hh := hb (i % c.size) (Nat.mod_lt i (by have := c.four_le; omega))
  have hdiv : 2 ∣ c.size := Nat.dvd_of_mod_eq_zero c.even
  have hmod : (i % c.size) % 2 = i % 2 := Nat.mod_mod_of_dvd i hdiv
  simpa only [c.edgeAt_mod, hmod] using hh

end

namespace Corners

variable {c} (k : c.Corners)

lemma parity_start (i : Fin 4) :
    k.start i % 2 = if CellPaths.sideBit i then k.a₀ % 2 else 1 - k.a₀ % 2 := by
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have ho₀ := k.odd₀
  have ho₁ := k.odd₁
  have ho₂ := k.odd₂
  fin_cases i <;> simp [start, CellPaths.sideBit] <;> omega

variable [DecidableEq V] [DecidableEq E]

lemma cell_orientation_subset (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (S : Finset E) (a : ℕ) (ha : a < 2)
    (hS : ∀ t, t % 2 = a → c.edgeAt t ∈ S) :
    (k.cellPaths chord hc).orientation (decide (k.a₀ % 2 = a)) ⊆ S := by
  have hh : ∀ i, (k.cellPaths chord hc).orientationPieces (decide (k.a₀ % 2 = a)) i ⊆ S := by
    intro i e he
    simp only [CellPaths.orientationPieces, CellPaths.pieces] at he
    split_ifs at he with hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjl, hjr⟩ := Finset.mem_Ico.mp hb
      apply hS
      have hs := k.parity_start i
      have hp' : j % 2 = 0 := hp
      change CellPaths.sideBit i = decide (k.a₀ % 2 = a) at hi
      change (k.start i + j) % 2 = a
      rw [Nat.add_mod, hs, hp']
      cases hbit : CellPaths.sideBit i <;> simp_all
      omega
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hb, hp⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjl, hjr⟩ := Finset.mem_Ico.mp hb
      apply hS
      have hs := k.parity_start i
      have hp' : j % 2 = 1 := hp
      change CellPaths.sideBit i ≠ decide (k.a₀ % 2 = a) at hi
      change (k.start i + j) % 2 = a
      rw [Nat.add_mod, hs, hp']
      cases hbit : CellPaths.sideBit i <;> simp_all <;> omega
  intro e he
  change e ∈ CellPaths.assemble _ at he
  simp only [CellPaths.assemble, Finset.mem_union] at he
  rcases he with (he | he) | (he | he)
  · exact hh 0 he
  · exact hh 2 he
  · exact hh 1 he
  · exact hh 3 he

lemma cell_orientation_reachable (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (U : Finset E) (hU : ∀ i, c.edgeAt i ∈ U) (b : Bool) :
    ∀ e ∈ (k.cellPaths chord hc).orientation b,
      (overlayLineGraph inc U).Reachable (c.edgeAt 0) e := by
  have hh : ∀ i e, e ∈ (k.cellPaths chord hc).orientationPieces b i →
      (overlayLineGraph inc U).Reachable (c.edgeAt 0) e := by
    intro i e he
    simp only [CellPaths.orientationPieces, CellPaths.pieces] at he
    split_ifs at he <;>
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp he <;>
      exact c.edges_reachable U hU (k.start i + j)
  intro e he
  change e ∈ CellPaths.assemble _ at he
  simp only [CellPaths.assemble, Finset.mem_union] at he
  rcases he with (he | he) | (he | he)
  · exact hh 0 e he
  · exact hh 2 e he
  · exact hh 1 e he
  · exact hh 3 e he

end Corners

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
