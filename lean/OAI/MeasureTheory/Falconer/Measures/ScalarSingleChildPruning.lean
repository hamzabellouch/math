import OAI.MeasureTheory.Falconer.Measures.ScalarPruningPreservation
import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupedPaths

namespace OAI

/-! Exact loss and new branching after keeping one child per terminal
 prefix. These are the operations used to trim a porous bunch. -/
namespace Falconer.Regularization

 theorem scalar_single_child_pruning_cost (L : Finset (CellPath 1)) {a b D m : ℕ}
    (hab : a ≤ b) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), K p ⊆ prefixChildren L a b p ∧ (K p).card = 1)
    (hD : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).card = D)
    (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m) :
    L.card = D*(scalarPruneLeaves L a b K).card := by
  classical
  have hKn : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hK p hp).2]; omega),(hK p hp).1⟩
  have hLcard : ∀ p ∈ L.image (List.take a), (prefixFiber L a p).card = D*m := by
    intro p hp
    rw [prefixFiber_card_sum hab]
    have he : ∀ c ∈ prefixChildren L a b p, (prefixFiber L b c).card = m :=
      fun c hc => hm c (prefixChildren_mem_image hc)
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,hD p hp]
  have hQcard : ∀ p ∈ L.image (List.take a),
      (prefixFiber (scalarPruneLeaves L a b K) a p).card = m := by
    intro p hp
    rw [scalarPruneLeaves_fiber_card L hab K p (hK p hp).1]
    have he : ∀ c ∈ K p, (prefixFiber L b c).card = m :=
      fun c hc => hm c (prefixChildren_mem_image ((hK p hp).1 hc))
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul,(hK p hp).2,one_mul]
  rw [prefixFiber_total_card L a,prefixFiber_total_card (scalarPruneLeaves L a b K) a,
    scalarPruneLeaves_upper_prefixes L le_rfl K hKn,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hLcard p hp,hQcard p hp]

 theorem scalar_single_child_group_card (L : Finset (CellPath 1)) {a c b : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take c), K p ⊆ prefixChildren L c b p ∧ (K p).card = 1)
    (p : CellPath 1) :
    (prefixChildren (scalarPruneLeaves L c b K) a b p).card = (prefixChildren L a c p).card := by
  classical
  have hKn : ∀ p ∈ L.image (List.take c), (K p).Nonempty ∧ K p ⊆ prefixChildren L c b p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hK p hp).2]; omega),(hK p hp).1⟩
  rw [prefixChildren_card_compose _ hac hcb,
    scalarPruneLeaves_upper_children L hac le_rfl K hKn]
  have he : ∀ q ∈ prefixChildren L a c p,
      (prefixChildren (scalarPruneLeaves L c b K) c b q).card = 1 := by
    intro q hq
    have hq' := prefixChildren_mem_image hq
    rw [scalarPruneLeaves_children L c b K q (hK q hq').1,(hK q hq').2]
  rw [Finset.sum_congr rfl he]
  simp

 theorem scalar_single_child_group_separated {N : ℕ} {L : Finset (CellPath 1)}
    (hL : L ⊆ cubePaths 1 N) {a c b : ℕ} (_hac : a ≤ c) (hcb : c ≤ b)
    (hb : b ≤ N) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take c), K p ⊆ prefixChildren L c b p ∧ (K p).card = 1)
    (g : ℝ) (p : CellPath 1)
    (hsep : ∀ u ∈ prefixChildren L a c p, ∀ v ∈ prefixChildren L a c p,
      u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v|) :
    ∀ u ∈ prefixChildren (scalarPruneLeaves L c b K) a b p,
      ∀ v ∈ prefixChildren (scalarPruneLeaves L c b K) a b p,
      u ≠ v → g-2*(1/2:ℝ)^c ≤ |scalarPathCenter u-scalarPathCenter v| := by
  classical
  intro u hu v hv huv
  have hQu := (Finset.mem_image.mp hu)
  obtain ⟨x,hx,hxu⟩ := hQu
  obtain ⟨y,hy,hyv⟩ := Finset.mem_image.mp hv
  have hxL := scalarPruneLeaves_subset L c b K (Finset.mem_filter.mp hx).1
  have hyL := scalarPruneLeaves_subset L c b K (Finset.mem_filter.mp hy).1
  have hux : u.take c = x.take c := by rw [← hxu,List.take_take,min_eq_left hcb]
  have hvy : v.take c = y.take c := by rw [← hyv,List.take_take,min_eq_left hcb]
  have hxK : u ∈ K (x.take c) := by
    rw [← hxu]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hyK : v ∈ K (y.take c) := by
    rw [← hyv]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
  have huvC : u.take c ≠ v.take c := by
    intro heq
    have hxy : x.take c = y.take c := hux.symm.trans (heq.trans hvy)
    rw [← hxy] at hyK
    have hc : (K (x.take c)).card ≤ 1 := by
      rw [(hK _ (Finset.mem_image_of_mem _ hxL)).2]
    exact huv (Finset.card_le_one.mp hc u hxK v hyK)
  have huc : u.take c ∈ prefixChildren L a c p := by
    rw [hux]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hxL,(Finset.mem_filter.mp hx).2⟩)
  have hvc : v.take c ∈ prefixChildren L a c p := by
    rw [hvy]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hyL,(Finset.mem_filter.mp hy).2⟩)
  have hse := hsep _ huc _ hvc huvC
  have huLen := scalar_prefix_children_length (a := a)
    ((scalarPruneLeaves_subset L c b K).trans hL) hb p u hu
  have hvLen := scalar_prefix_children_length (a := a)
    ((scalarPruneLeaves_subset L c b K).trans hL) hb p v hv
  have hdu : |scalarPathCenter u-scalarPathCenter (u.take c)| ≤ (1/2:ℝ)^c :=
    scalarPathCenter_same_parent huLen hcb (by simp only [List.take_take,min_self])
  have hdv : |scalarPathCenter v-scalarPathCenter (v.take c)| ≤ (1/2:ℝ)^c :=
    scalarPathCenter_same_parent hvLen hcb (by simp only [List.take_take,min_self])
  have ht : |scalarPathCenter (u.take c)-scalarPathCenter (v.take c)| ≤
      |scalarPathCenter u-scalarPathCenter (u.take c)|+|scalarPathCenter u-scalarPathCenter v|+
        |scalarPathCenter v-scalarPathCenter (v.take c)| := by
    calc
      _ ≤ |scalarPathCenter (u.take c)-scalarPathCenter u|+
        |scalarPathCenter u-scalarPathCenter (v.take c)| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter (u.take c)-scalarPathCenter u|+
        (|scalarPathCenter u-scalarPathCenter v|+|scalarPathCenter v-scalarPathCenter (v.take c)|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter (u.take c))]; ring
  linarith

end Falconer.Regularization

end OAI
