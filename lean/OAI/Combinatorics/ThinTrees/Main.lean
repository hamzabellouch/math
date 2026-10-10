import OAI.Combinatorics.ThinTrees.Iteration

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

lemma connected_has_spanningTree {n m : ℕ} (G : MultiGraph n m)
    (hG : G.Connected univ) : ∃T : Finset (Fin m), G.SpanningTree T := by
  classical
  let A : Finset (Finset (Fin m)) := univ.filter G.Connected
  have hA : A.Nonempty := ⟨univ,by simp only [A,mem_filter,mem_univ,true_and]; exact hG⟩
  obtain ⟨T,hT,hmin⟩ := exists_min_image A Finset.card hA
  refine ⟨T,(mem_filter.mp hT).2,?_⟩
  intro e he hc
  have hh := hmin (T.erase e) (by simp only [A,mem_filter,mem_univ,true_and]; exact hc)
  exact (not_le_of_gt (card_erase_lt_of_mem he)) hh

end MultiGraph

theorem strongThinTree : MainStatement := by
  obtain ⟨C₀,hC₀,hpacking⟩ := MultiGraph.packing_thinness
  let C : ℝ := 3*max C₀ 1
  have hm : 1 ≤ max C₀ 1 := le_max_right _ _
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro k hk n m hn G hc
  by_cases hk2 : 2 ≤ k
  · let r := k/2
    have hr : 0 < r := Nat.div_pos hk2 (by norm_num)
    have hr' : 1 ≤ r := hr
    have hconn : G.EdgeConnected (2*r) := by
      intro S hS hS'
      exact (show 2*r ≤ k by dsimp [r]; omega).trans (hc S hS hS')
    have hpack := G.edgeConnected_treePackable hr (by omega) hconn
    obtain ⟨T,hT,hthin⟩ := hpacking r hr' n m G hn hpack
    refine ⟨T,hT,fun S hS hS' => (hthin S hS hS').trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
    have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    apply (div_le_div_iff₀ hrR hkR).mpr
    have hkr : (k:ℝ) ≤ 3*(r:ℝ) := by exact_mod_cast (show k ≤ 3*r by dsimp [r]; omega)
    have h1 := mul_le_mul_of_nonneg_left hkr hC₀.le
    have h2 := mul_le_mul_of_nonneg_right (le_max_left C₀ 1) hrR.le
    dsimp [C]
    nlinarith
  · have hk1 : k=1 := by omega
    subst k
    have hconn : G.Connected univ := by
      intro S hS hS'
      exact card_pos.mp (hc S hS hS')
    obtain ⟨T,hT⟩ := G.connected_has_spanningTree hconn
    refine ⟨T,hT,?_⟩
    intro S _ _
    have hh : ((G.cut T S).card:ℝ) ≤ (G.cut univ S).card := by
      exact_mod_cast G.cut_card_le_full T S
    have hCle : 1 ≤ C := by dsimp [C]; linarith
    simpa only [Nat.cast_one,div_one] using
      hh.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hCle)

end StrongThinTree

end

end

end OAI
