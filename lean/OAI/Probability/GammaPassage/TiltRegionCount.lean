import OAI.Probability.GammaPassage.RareFastEvents

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset

theorem int_interval_card_real_le (l u : ℝ) (h : l ≤ u) :
    ((Finset.Icc ⌈l⌉ ⌊u⌋).card : ℝ) ≤ u-l+1 := by
  rw [Int.card_Icc]
  by_cases hh : 0 ≤ ⌊u⌋+1-⌈l⌉
  · have he : ((⌊u⌋+1-⌈l⌉).toNat : ℝ)=((⌊u⌋+1-⌈l⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hh
    rw [he]
    push_cast
    linarith [Int.floor_le u,Int.le_ceil l]
  · have hz : (⌊u⌋+1-⌈l⌉).toNat=0 := Int.toNat_eq_zero.mpr (le_of_not_ge hh)
    rw [hz]
    simp only [Nat.cast_zero]
    linarith

noncomputable def tiltColumn (b s : ℝ) (x : ℤ) : Finset Vertex :=
  {x} ×ˢ Finset.Icc ⌈b*x-8*s⌉ ⌊b*x+8*s⌋

theorem tiltColumn_card (b s : ℝ) (hs : 0 ≤ s) (x : ℤ) :
    ((tiltColumn b s x).card : ℝ) ≤ 16*s+2 := by
  have hh := int_interval_card_real_le (b*x-8*s) (b*x+8*s) (by linarith)
  simpa only [tiltColumn,Finset.card_product,Finset.card_singleton,one_mul] using
    hh.trans (by linarith)

theorem rareFast_tilt_vertices_card (b s : ℝ) (n : ℤ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ((rareFastVertices b 1 8 s n 0).card : ℝ) ≤ (3*(n : ℝ)+1)*(16*s+2) := by
  have hsub : rareFastVertices b 1 8 s n 0 ⊆
      (Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s) := by
    intro p hp
    have hh := (mem_rareFastVertices ..).mp hp
    have hx : -n ≤ p.1 ∧ p.1 ≤ 2*n := by
      constructor
      · have ht : -(n : ℝ) ≤ (p.1 : ℝ) := by simpa using hh.1
        exact_mod_cast ht
      · have := hh.2.1; norm_num only [sub_zero,one_add_one_eq_two] at this
        exact_mod_cast this
    have hy := abs_le.mp hh.2.2
    simp only [sub_zero,transverse] at hy
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,Finset.mem_Icc.mpr hx,?_⟩
    simp only [tiltColumn,Finset.mem_product,Finset.mem_singleton,Finset.mem_Icc,true_and]
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)
  have hcount : ((Finset.Icc (-n) (2*n)).card : ℝ)=3*(n : ℝ)+1 := by
    rw [Int.card_Icc]
    have he : ((2*n+1-(-n)).toNat : ℝ)=((2*n+1-(-n) : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ 2*n+1-(-n))
    rw [he]
    push_cast
    ring
  calc
    _ ≤ (((Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ (∑ x ∈ Finset.Icc (-n) (2*n), ((tiltColumn b s x).card : ℝ)) := by
      exact_mod_cast (Finset.card_biUnion_le :
        ((Finset.Icc (-n) (2*n)).biUnion (tiltColumn b s)).card ≤ _)
    _ ≤ ∑ _x ∈ Finset.Icc (-n) (2*n), (16*s+2) :=
      Finset.sum_le_sum (fun x _ => tiltColumn_card b s (by linarith) x)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,hcount]

/-- The internal-edge count is at most `144 * n * s`, for every lattice phase. -/
theorem rareFast_tilt_edges_card (b s : ℝ) (n : ℤ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ((internalEdges (rareFastVertices b 1 8 s n 0)).card : ℝ) ≤ 144*(n : ℝ)*s := by
  have hv := rareFast_tilt_vertices_card b s n hs hn
  have he : ((internalEdges (rareFastVertices b 1 8 s n 0)).card : ℝ) ≤
      2*((rareFastVertices b 1 8 s n 0).card : ℝ) := by
    exact_mod_cast internalEdges_card_le (rareFastVertices b 1 8 s n 0)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmul := mul_le_mul (show 3*(n : ℝ)+1 ≤ 4*n by linarith)
    (show 16*s+2 ≤ 18*s by linarith) (by linarith : 0 ≤ 16*s+2)
    (by linarith : 0 ≤ 4*(n : ℝ))
  nlinarith

end GammaFPP.CrossingBridge

end OAI
