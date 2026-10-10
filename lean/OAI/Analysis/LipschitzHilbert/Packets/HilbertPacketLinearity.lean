import OAI.Analysis.LipschitzHilbert.Packets.HilbertPacketSums

namespace OAI

/-! Exact linearity of partial packet sums across a finite box decomposition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem partialBandSum_finset_sum {B : Type*} {N : ℕ} (s : Finset B)
    (f : B → Fin N → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    partialBandSum (fun j => ∑ b ∈ s, f b j) n x =
      ∑ b ∈ s, partialBandSum (f b) n x := by
  simp only [partialBandSum, sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [hj, ite_true]
  · simp only [hj, ite_false, Finset.sum_const_zero]

theorem hilbertPartialBandSum_finset_sum {B : Type*} {N : ℕ} {κ : Type*} [Fintype κ]
    (s : Finset B) (f : B → Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum (fun j k => ∑ b ∈ s, f b j k) n x =
      ∑ b ∈ s, hilbertPartialBandSum (f b) n x := by
  ext k
  change partialBandSum (fun j => ∑ b ∈ s, f b j k) n x = _
  rw [partialBandSum_finset_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

end LipschitzHilbert

end

end OAI
