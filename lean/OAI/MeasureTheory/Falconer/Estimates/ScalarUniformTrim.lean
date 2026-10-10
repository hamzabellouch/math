import OAI.MeasureTheory.Falconer.Estimates.ScalarPathLevel

namespace OAI

/-! A complete bunch-trimming step on the original regularized paths:
 exact cardinal loss, retained branch count, separation, and common mass. -/
namespace Falconer.Regularization

 theorem scalar_trimmed_uniform_block {N : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (d k : ℕ → ℕ) (hd : Monotone d)
    {a c b m : ℕ} (hac : a ≤ c) (hcb : c ≤ b) (hb : d b ≤ N)
    (hcard : ∀ i < b, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    (hm : ∀ p ∈ L.image (List.take (d b)), (prefixFiber L (d b) p).card = m)
    (g : ℝ) (hsep : ∀ p ∈ L.image (List.take (d a)),
      ∀ u ∈ prefixChildren L (d a) (d c) p, ∀ v ∈ prefixChildren L (d a) (d c) p,
      u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v|) :
    ∃ F : CellPath 1 → Finset (CellPath 1),
      (∀ p ∈ L.image (List.take (d c)), F p ⊆ prefixChildren L (d c) (d b) p ∧ (F p).card = 1) ∧
      let Q := scalarPruneLeaves L (d c) (d b) F
      Q.Nonempty ∧ L.card = 2^(∑ i ∈ Finset.Ico c b, k i)*Q.card ∧
      ScalarPathLevel Q (d a) (d b) (2^(∑ i ∈ Finset.Ico a c, k i))
        (g-2*(1/2:ℝ)^(d c)) ∧
      (∀ p ∈ Q.image (List.take (d a)),
        (prefixFiber Q (d a) p).card = 2^(∑ i ∈ Finset.Ico a c, k i)*m) := by
  classical
  obtain ⟨F,hF⟩ := scalar_single_child_choice L (d c) (d b)
  have hFn : ∀ p ∈ L.image (List.take (d c)),
      (F p).Nonempty ∧ F p ⊆ prefixChildren L (d c) (d b) p := by
    intro p hp
    exact ⟨Finset.card_pos.mp (by rw [(hF p hp).2]; omega),(hF p hp).1⟩
  let Q := scalarPruneLeaves L (d c) (d b) F
  have hcCount : ∀ p ∈ L.image (List.take (d c)),
      (prefixChildren L (d c) (d b) p).card = 2^(∑ i ∈ Finset.Ico c b, k i) :=
    fun p hp => scalar_grouped_children_card L d k hd b hcard hcb le_rfl p hp
  have haCount : ∀ p ∈ L.image (List.take (d a)),
      (prefixChildren L (d a) (d c) p).card = 2^(∑ i ∈ Finset.Ico a c, k i) :=
    fun p hp => scalar_grouped_children_card L d k hd b hcard hac hcb p hp
  have hl : ScalarPathLevel L (d a) (d c) (2^(∑ i ∈ Finset.Ico a c, k i)) g :=
    ⟨hd hac,haCount,hsep⟩
  have hl' := hl.trim hL (hd hcb) hb F hF
  refine ⟨F,hF,scalarPruneLeaves_nonempty L hne F hFn,
    scalar_single_child_pruning_cost L (hd hcb) F hF hcCount hm,hl',?_⟩
  have hm' : ∀ p ∈ Q.image (List.take (d b)), (prefixFiber Q (d b) p).card = m := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [scalarPruneLeaves_fiber L (hd hcb) le_rfl F hq]
    exact hm _ (Finset.mem_image_of_mem _ (scalarPruneLeaves_subset L (d c) (d b) F hq))
  intro p hp
  rw [prefixFiber_card_sum (hd (hac.trans hcb))]
  have he : ∀ q ∈ prefixChildren Q (d a) (d b) p, (prefixFiber Q (d b) q).card = m :=
    fun q hq => hm' q (prefixChildren_mem_image hq)
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,Nat.nsmul_eq_mul]
  exact congrArg (fun t : ℕ => t*m) (hl'.card p hp)

end Falconer.Regularization

end OAI
