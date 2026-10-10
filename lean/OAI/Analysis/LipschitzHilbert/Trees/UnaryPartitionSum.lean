import OAI.Analysis.LipschitzHilbert.Trees.UnarySegmentation
import OAI.Analysis.LipschitzHilbert.Trees.PathDrops

namespace OAI

/-! Exact summation over the constructed unary segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace UnarySegmentPartition

variable {n : ℕ → ℝ} {start finish : ℕ}

theorem indices_disjoint (P : UnarySegmentPartition n start finish) :
    Set.PairwiseDisjoint (P.blocks : Set (ℕ × ℕ)) (fun b => Finset.Ico b.1 b.2) := by
  intro b hb c hc hbc
  apply Finset.disjoint_left.mpr
  intro j hjb hjc
  obtain ⟨hbj, hjb⟩ := Finset.mem_Ico.mp hjb
  obtain ⟨hcj, hjc⟩ := Finset.mem_Ico.mp hjc
  rcases P.ordered b hb c hc hbc with h | h <;> omega

theorem indices_union (P : UnarySegmentPartition n start finish) :
    P.blocks.biUnion (fun b => Finset.Ico b.1 b.2) = Finset.Ico start finish := by
  ext j
  constructor
  · intro hj
    obtain ⟨b, hb, hjb⟩ := Finset.mem_biUnion.mp hj
    have h := P.bounds b hb
    have hj' := Finset.mem_Ico.mp hjb
    exact Finset.mem_Ico.mpr ⟨h.1.trans hj'.1, hj'.2.trans_le h.2.2⟩
  · intro hj
    obtain ⟨b, hb, hjb, hbj⟩ := P.cover j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_Ico.mpr ⟨hjb, hbj⟩⟩

theorem sum_blocks {E : Type*} [AddCommMonoid E]
    (P : UnarySegmentPartition n start finish) (f : ℕ → E) :
    (∑ b ∈ P.blocks, ∑ j ∈ Finset.Ico b.1 b.2, f j) =
      ∑ j ∈ Finset.Ico start finish, f j := by
  rw [← Finset.sum_biUnion P.indices_disjoint, P.indices_union]

end UnarySegmentPartition

theorem sum_Ico_mass_drop (n : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, (n j - n (j + 1))) = n a - n b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    ring

/-- The discarded errors are charged to actual mass drops. Summation
over segments introduces no factor counting the number of tiny drops. -/
theorem unary_partition_weighted_drop_le (n : ℕ → ℝ) (hn : Antitone n)
    (start finish : ℕ) (P : UnarySegmentPartition n start finish) {μ Q : ℝ}
    (hμ : μ ≤ 1) (hnpos : ∀ j, start ≤ j → j ≤ finish → 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j ^ μ ≤ Q) :
    (∑ b ∈ P.blocks, n b.1 ^ (μ - 1) * (n b.1 - n b.2)) ≤
      Q * ∑ j ∈ Finset.Ico start finish, pathDrop n j := by
  calc
    _ ≤ ∑ b ∈ P.blocks, ∑ j ∈ Finset.Ico b.1 b.2, Q * pathDrop n j := by
      apply Finset.sum_le_sum
      intro b hb
      have hbnd := P.bounds b hb
      rw [← sum_Ico_mass_drop n hbnd.2.1.le, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjb := Finset.mem_Ico.mp hj
      have hjstart := hbnd.1.trans hjb.1
      have hjfinish : j ≤ finish := hjb.2.le.trans hbnd.2.2
      have hjpos := hnpos j hjstart hjfinish
      have hdrop : 0 ≤ n j - n (j + 1) := sub_nonneg.mpr (hn (Nat.le_succ _))
      have hp : n b.1 ^ (μ - 1) ≤ n j ^ (μ - 1) :=
        Real.rpow_le_rpow_of_nonpos hjpos (hn hjb.1) (by linarith)
      calc
        _ ≤ n j ^ (μ - 1) * (n j - n (j + 1)) :=
          mul_le_mul_of_nonneg_right hp hdrop
        _ = n j ^ μ * pathDrop n j := by rw [Real.rpow_sub_one hjpos.ne', pathDrop]; ring
        _ ≤ Q * pathDrop n j := mul_le_mul_of_nonneg_right
          (hQ j (Finset.mem_Ico.mpr ⟨hjstart, hjb.2.trans_le hbnd.2.2⟩))
          (pathDrop_nonnegative n j hjpos (hn (Nat.le_succ _)))
    _ = Q * ∑ j ∈ Finset.Ico start finish, pathDrop n j := by
      rw [P.sum_blocks, Finset.mul_sum]

end LipschitzHilbert

end

end OAI
