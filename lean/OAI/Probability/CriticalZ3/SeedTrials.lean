import OAI.Probability.CriticalZ3.EntryLayers

namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical
namespace Box

theorem bits_mono (m : Model) {B C : Box} (h : ∀ x, B.Contains x → C.Contains x) :
    B.bits m ⊆ C.bits m := by
  intro e he
  cases m
  · exact (mem_bonds C e).mpr ⟨h _ ((mem_bonds B e).mp he).1,h _ ((mem_bonds B e).mp he).2⟩
  · exact (mem_vertices C e).mpr (h _ ((mem_vertices B e).mp he))

theorem disjoint_bits (m : Model) {B C : Box} (h : Disjoint B.vertices C.vertices) :
    Disjoint (B.bits m) (C.bits m) := by
  rw [Finset.disjoint_left] at h ⊢
  intro e he he'
  cases m
  · exact h ((mem_vertices B e.1).mpr ((mem_bonds B e).mp he).1)
      ((mem_vertices C e.1).mpr ((mem_bonds C e).mp he').1)
  · exact h he he'

@[simp] theorem center_mem_cube (c : Vertex) (r : ℕ) : (cube c r).Contains c := by
  rw [contains_cube]; intro i; simp

theorem cube_bits_card (m : Model) (c : Vertex) (r : ℕ) :
    ((cube c r).bits m).card = ((cube 0 r).bits m).card := by
  cases m
  · exact cube_bonds_card _ _
  · simp only [bits,card_cube]

noncomputable def relayCenter (C : Box) (r : ℕ) (y : Vertex) := C.seedCenter r (C.entry y)
noncomputable def seedBox (C : Box) (r : ℕ) (y : Vertex) := cube (C.relayCenter r y) r

noncomputable def successBits (C : Box) (r : ℕ) : (m : Model) → Vertex → Finset m.Bit
  | .bond,y => insert (C.entryBit .bond y) (C.seedBox r y).bonds
  | .site,y => (C.seedBox r y).vertices

noncomputable def seedCard (m : Model) (r : ℕ) : ℕ := ((cube 0 r).bits m).card
noncomputable def successCard (m : Model) (r : ℕ) : ℕ := seedCard m r + match m with
  | .bond => 1
  | .site => 0

theorem crossing_not_internal {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit .bond y ∉ C.bonds := by
  intro he
  obtain ⟨h0,h1⟩ := (mem_bonds C _).mp he
  have hi := neighborBond_incidence (entry_spec hy).2
  rcases hi with ⟨hx,_⟩ | ⟨_,hx⟩
  · exact hy.1 (hx ▸ h0)
  · exact hy.1 (hx ▸ h1)

theorem crossing_injective {C : Box} {y z : Vertex} (hy : C.Exterior y) (hz : C.Exterior z)
    (he : C.entryBit .bond y = C.entryBit .bond z) : y = z := by
  have hi := neighborBond_incidence (entry_spec hy).2
  have hj := neighborBond_incidence (entry_spec hz).2
  change Incidence (C.entryBit .bond y) y (C.entry y) at hi
  change Incidence (C.entryBit .bond z) z (C.entry z) at hj
  rw [←he] at hj
  rcases hi with ⟨hy0,hy1⟩ | ⟨hy1,hy0⟩ <;>
    rcases hj with ⟨hz0,hz1⟩ | ⟨hz1,hz0⟩
  · exact hy0.trans hz0.symm
  · exact False.elim (hy.1 ((hy0.trans hz1.symm).symm ▸ (entry_spec hz).1))
  · exact False.elim (hy.1 ((hy0.trans hz1.symm).symm ▸ (entry_spec hz).1))
  · exact hy0.trans hz0.symm

theorem seedBox_contained (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (y : Vertex) :
    ∀ x, (C.seedBox r y).Contains x → C.Contains x := C.seed_contained r hw (C.entry y)

theorem successBits_card (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    (C.successBits r m y).card = successCard m r := by
  cases m
  · have he : C.entryBit .bond y ∉ (C.seedBox r y).bonds := fun h =>
      C.crossing_not_internal hy (bits_mono .bond (C.seedBox_contained r hw y) h)
    rw [successBits,Finset.card_insert_of_notMem he]
    change ((cube (C.relayCenter r y) r).bits .bond).card+1 = _
    rw [cube_bits_card]; rfl
  · exact cube_bits_card .site (C.relayCenter r y) r

theorem successBits_disjoint (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y z : Vertex}
    (hy : C.Exterior y) (hz : C.Exterior z) (hsep : ∃ i, (4*r+2 : ℤ) < |y i-z i|) :
    Disjoint (C.successBits r m y) (C.successBits r m z) := by
  have hcent := C.separated_centers r hw (entry_spec hy).1 (entry_spec hz).1
    (entry_spec hy).2 (entry_spec hz).2 hsep
  have hseed := disjoint_bits m (disjoint_seeds hcent)
  have hyz : y ≠ z := by
    intro he
    obtain ⟨i,hi⟩ := hsep
    rw [he,sub_self,abs_zero] at hi
    omega
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he he'
    rcases Finset.mem_insert.mp he with he | he <;> rcases Finset.mem_insert.mp he' with he' | he'
    · exact hyz (C.crossing_injective hy hz (he.symm.trans he'))
    · subst e
      exact C.crossing_not_internal hy (bits_mono .bond (C.seedBox_contained r hw z) he')
    · subst e
      exact C.crossing_not_internal hz (bits_mono .bond (C.seedBox_contained r hw y) he)
    · exact Finset.disjoint_left.mp hseed he he'
  · exact hseed

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

theorem successBits_disjoint_outside (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    Disjoint (C.successBits r m y) (G.outsideBits m C) := by
  have hs := (G.outsideBits_disjoint_inside m C).symm.mono_left
    (Box.bits_mono m (C.seedBox_contained r hw y))
  cases m
  · rw [Box.successBits,Finset.disjoint_insert_left]
    exact ⟨G.entryBit_not_outside .bond hy,hs⟩
  · exact hs

theorem ContainsBox.mono {B C : Box} (hC : G.ContainsBox C)
    (h : ∀ x, B.Contains x → C.Contains x) : G.ContainsBox B :=
  ⟨(Box.bits_mono .site h).trans hC.1,(Box.bits_mono .bond h).trans hC.2⟩

/-- A successful exterior trial supplies a path for both bond and site percolation. -/
theorem success_reaches_center (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    {ω : m.Config} {o y : G.Node} (hy : y.1 ∈ G.entrants m C ω o)
    (hs : ∀ e ∈ C.successBits r m y.1, ω e = true) :
    ∃ v : G.Node, v.1 = C.relayCenter r y.1 ∧ G.Conn m ω o v := by
  obtain ⟨hey,hreach⟩ := (G.mem_entrants m C ω o y).mp hy
  have hCg : G.ContainsBox C := hC.mono G (fun _ => C.contains_expand 1)
  have hUg : G.ContainsBox (C.seedBox r y.1) := hCg.mono G (C.seedBox_contained r hw y.1)
  have hz := (Box.entry_spec hey).1
  let z : G.Node := ⟨C.entry y.1,G.containsBox_node hCg hz⟩
  let v : G.Node := ⟨C.relayCenter r y.1,
    G.containsBox_node hUg (Box.center_mem_cube _ _)⟩
  have heo : ∀ e ∈ (C.seedBox r y.1).bits m, ω e = true := by
    intro e he
    cases m
    · exact hs e (Finset.mem_insert_of_mem he)
    · exact hs e he
  have hyz : G.Adj m ω y z := by
    have hi := neighborBond_incidence (Box.entry_spec hey).2
    have heb := incidence_internal (Box.exterior_expand hey) (C.contains_expand 1 hz) hi
    cases m
    · exact ⟨C.entryBit .bond y.1,hC.2 heb,hi,hs _ (Finset.mem_insert_self _ _)⟩
    · exact ⟨⟨neighborBond y.1 z.1,hC.2 heb,hi⟩,(G.conn_open .site (G.outsideReach_conn .site hreach)).2,
        heo _ ((Box.mem_vertices _ _).mpr (C.seed_contains_entry r hw hz))⟩
  refine ⟨v,rfl,G.conn_trans m (G.outsideReach_conn m hreach) ?_⟩
  exact G.conn_trans m (G.conn_adj m hyz) (G.open_box_conn m hUg heo
    (C.seed_contains_entry r hw hz) (Box.center_mem_cube _ _))

end LatticeGraph
end CriticalZ3

end OAI
