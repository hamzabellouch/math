import OAI.Combinatorics.Hamiltonian.Traces

namespace OAI

/-! Ordinary square cells and connected finite lattice corridors. -/

namespace Barnette.SquareGrid

noncomputable section

def graph : SimpleGraph (ℤ × ℤ) where
  Adj a b := ((a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ a.2 = b.2) ∨
    ((a.2 + 1 = b.2 ∨ b.2 + 1 = a.2) ∧ a.1 = b.1)
  symm := ⟨by
    intro a b h
    rcases h with ⟨h, he⟩ | ⟨h, he⟩
    · exact Or.inl ⟨h.symm, he.symm⟩
    · exact Or.inr ⟨h.symm, he.symm⟩⟩
  loopless := ⟨by intro a h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega⟩

def cell (δ : ℝ) (z : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Icc (δ * z.1) (δ * ((z.1 : ℝ) + 1)) ×ˢ
    Set.Icc (δ * z.2) (δ * ((z.2 : ℝ) + 1))

def cells (δ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℤ × ℤ) :=
  {z | (cell δ z ∩ K).Nonempty}

theorem cell_closed (δ : ℝ) (z : ℤ × ℤ) : IsClosed (cell δ z) :=
  isClosed_Icc.prod isClosed_Icc

theorem cell_compact (δ : ℝ) (z : ℤ × ℤ) : IsCompact (cell δ z) :=
  isCompact_Icc.prod isCompact_Icc

theorem cell_cover {δ : ℝ} (hδ : 0 < δ) (p : ℝ × ℝ) : ∃ z, p ∈ cell δ z := by
  refine ⟨(⌊p.1 / δ⌋, ⌊p.2 / δ⌋), ?_⟩
  constructor
  · constructor
    · have h := (le_div_iff₀ hδ).mp (Int.floor_le (p.1 / δ))
      simpa only [mul_comm] using h
    · have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (p.1 / δ))
      exact le_of_lt (by simpa only [mul_comm] using h)
  · constructor
    · have h := (le_div_iff₀ hδ).mp (Int.floor_le (p.2 / δ))
      simpa only [mul_comm] using h
    · have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (p.2 / δ))
      exact le_of_lt (by simpa only [mul_comm] using h)

theorem subset_union_cells {δ : ℝ} (hδ : 0 < δ) (K : Set (ℝ × ℝ)) :
    K ⊆ ⋃ z : cells δ K, cell δ z.val := by
  intro p hp
  obtain ⟨z, hz⟩ := cell_cover hδ p
  exact Set.mem_iUnion.mpr ⟨⟨z, p, hz, hp⟩, hz⟩

private theorem int_bound_of_cell {δ R : ℝ} (hδ : 0 < δ) {a : ℤ} {x : ℝ}
    (hx : -R ≤ x ∧ x ≤ R) (ha : δ * a ≤ x ∧ x ≤ δ * ((a : ℝ) + 1)) :
    -(R / δ + 1) ≤ (a : ℝ) ∧ (a : ℝ) ≤ R / δ + 1 := by
  have hu : (a : ℝ) ≤ R / δ :=
    (le_div_iff₀ hδ).mpr (by nlinarith [ha.1, hx.2])
  have hl : -R / δ ≤ (a : ℝ) + 1 :=
    (div_le_iff₀ hδ).mpr (by nlinarith [ha.2, hx.1])
  rw [neg_div] at hl
  constructor <;> linarith

theorem cells_finite {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) : (cells δ K).Finite := by
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_int_ge (R / δ + 1)
  apply ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset
  rintro z ⟨p, hp, hpK⟩
  have hp₁ : -R ≤ p.1 ∧ p.1 ≤ R := abs_le.mp ((norm_fst_le p).trans (hR p hpK))
  have hp₂ : -R ≤ p.2 ∧ p.2 ≤ R := abs_le.mp ((norm_snd_le p).trans (hR p hpK))
  obtain ⟨hz₁, hz₁'⟩ := int_bound_of_cell hδ hp₁ hp.1
  obtain ⟨hz₂, hz₂'⟩ := int_bound_of_cell hδ hp₂ hp.2
  have hb₁ : (-(N : ℝ)) ≤ z.1 ∧ (z.1 : ℝ) ≤ N := by constructor <;> linarith
  have hb₂ : (-(N : ℝ)) ≤ z.2 ∧ (z.2 : ℝ) ≤ N := by constructor <;> linarith
  exact ⟨⟨by exact_mod_cast hb₁.1, by exact_mod_cast hb₁.2⟩,
    ⟨by exact_mod_cast hb₂.1, by exact_mod_cast hb₂.2⟩⟩

theorem dist_le_of_mem_cell {δ : ℝ} {z : ℤ × ℤ} {p q : ℝ × ℝ}
    (hp : p ∈ cell δ z) (hq : q ∈ cell δ z) : dist p q ≤ δ := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2, hq.1.1, hq.1.2, hq.2.1, hq.2.2]

theorem cell_subset_thickening {δ ε : ℝ} (hδε : δ < ε) {K : Set (ℝ × ℝ)}
    {z : ℤ × ℤ} (hz : z ∈ cells δ K) : cell δ z ⊆ Metric.thickening ε K := by
  obtain ⟨q, hq, hqK⟩ := hz
  intro p hp
  exact Metric.mem_thickening_iff.mpr ⟨q, hqK, (dist_le_of_mem_cell hp hq).trans_lt hδε⟩

theorem cells_disjoint {δ ε : ℝ} (hδε : δ < ε)
    {K L : Set (ℝ × ℝ)}
    (hKL : Disjoint (Metric.thickening ε K) (Metric.thickening ε L)) :
    Disjoint (cells δ K) (cells δ L) := by
  rw [Set.disjoint_left] at hKL ⊢
  intro z hz hz'
  have hzp := hz
  obtain ⟨p, hp, _⟩ := hzp
  exact hKL (cell_subset_thickening hδε hz hp) (cell_subset_thickening hδε hz' hp)

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

theorem finite_closed_cover_preconnected {ι α : Type*} [Finite ι] [TopologicalSpace α]
    (H : SimpleGraph ι) (K : Set α) (C : ι → Set α)
    (hK : IsPreconnected K) (hC : ∀ i, IsClosed (C i))
    (hcover : K ⊆ ⋃ i, C i) (hne : ∀ i, (K ∩ C i).Nonempty)
    (hjoin : ∀ p ∈ K, ∀ i j, p ∈ C i → p ∈ C j → H.Reachable i j) :
    H.Preconnected := by
  classical
  intro a b
  by_contra hab
  let U : Set α := ⋃ i : {i // H.Reachable a i}, C i.val
  let W : Set α := ⋃ i : {i // ¬H.Reachable a i}, C i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun i => hC i.val)
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun i => hC i.val)
  have hUW : K ⊆ U ∪ W := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hp)
    by_cases hai : H.Reachable a i
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
  have haU : (K ∩ U).Nonempty := by
    obtain ⟨p, hpK, hpa⟩ := hne a
    exact ⟨p, hpK, Set.mem_iUnion.mpr ⟨⟨a, .rfl⟩, hpa⟩⟩
  have hbW : (K ∩ W).Nonempty := by
    obtain ⟨p, hpK, hpb⟩ := hne b
    exact ⟨p, hpK, Set.mem_iUnion.mpr ⟨⟨b, hab⟩, hpb⟩⟩
  obtain ⟨p, hpK, hpU, hpW⟩ :=
    isPreconnected_closed_iff.mp hK U W hU hW hUW haU hbW
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hpW
  exact j.property (i.property.trans (hjoin p hpK i.val j.val hi hj))

private theorem coordinates_close {δ : ℝ} (hδ : 0 < δ) {a b : ℤ} {p : ℝ}
    (ha : δ * a ≤ p ∧ p ≤ δ * ((a : ℝ) + 1))
    (hb : δ * b ≤ p ∧ p ≤ δ * ((b : ℝ) + 1)) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  have hab : (a : ℝ) ≤ (b : ℝ) + 1 := (mul_le_mul_iff_right₀ hδ).mp (ha.1.trans hb.2)
  have hba : (b : ℝ) ≤ (a : ℝ) + 1 := (mul_le_mul_iff_right₀ hδ).mp (hb.1.trans ha.2)
  exact ⟨by exact_mod_cast hab, by exact_mod_cast hba⟩

theorem reachable_of_common_point {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} (hp : p ∈ K) (a b : cells δ K)
    (ha : p ∈ cell δ a.val) (hb : p ∈ cell δ b.val) :
    (graph.induce (cells δ K)).Reachable a b := by
  obtain ⟨hx, hx'⟩ := coordinates_close hδ ha.1 hb.1
  obtain ⟨hy, hy'⟩ := coordinates_close hδ ha.2 hb.2
  let c : cells δ K := ⟨(b.val.1, a.val.2), p, ⟨hb.1, ha.2⟩, hp⟩
  have hac : (graph.induce (cells δ K)).Reachable a c := by
    by_cases h : a.val.1 = b.val.1
    · have heq : a = c := Subtype.ext (Prod.ext h rfl)
      rw [← heq]
    · apply SimpleGraph.Adj.reachable
      change graph.Adj a.val c.val
      exact Or.inl ⟨by dsimp [c]; omega, rfl⟩
  have hcb : (graph.induce (cells δ K)).Reachable c b := by
    by_cases h : a.val.2 = b.val.2
    · have heq : c = b := Subtype.ext (Prod.ext rfl h)
      rw [heq]
    · apply SimpleGraph.Adj.reachable
      change graph.Adj c.val b.val
      exact Or.inr ⟨by dsimp [c]; omega, rfl⟩
  exact hac.trans hcb

theorem cells_connected {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : IsConnected K) :
    (graph.induce (cells δ K)).Connected := by
  classical
  let _ : Fintype (cells δ K) := (cells_finite hδ hK).fintype
  have hone : Nonempty (cells δ K) := by
    obtain ⟨p, hp⟩ := hc.nonempty
    obtain ⟨z, hz⟩ := cell_cover hδ p
    exact ⟨⟨z, p, hz, hp⟩⟩
  refine ⟨finite_closed_cover_preconnected _ K (fun z : cells δ K => cell δ z.val)
    hc.isPreconnected (fun z => cell_closed _ _) (subset_union_cells hδ K) ?_ ?_⟩
  · intro z
    obtain ⟨p, hp, hpK⟩ := z.property
    exact ⟨p, hpK, hp⟩
  · intro p hp a b ha hb
    exact reachable_of_common_point hδ hp a b ha hb

end
end Barnette.SquareGrid

end OAI
