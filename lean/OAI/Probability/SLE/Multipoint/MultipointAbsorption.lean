import OAI.Probability.SLE.Multipoint.MultipointYoung

namespace OAI

/-! Summation of the pairwise Young bounds. The active index set may
change at the individual activation and completion times. -/

noncomputable section
open scoped BigOperators

namespace SLEExactGauge.Multipoint

lemma offDiag_vertex_cost_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) (hA : ∀ i ∈ s, 0 ≤ A i) :
    (∑ ij ∈ s.offDiag, (A ij.1 + A ij.2)) ≤
      2 * (s.card : ℝ) * ∑ i ∈ s, A i := by
  calc
    _ ≤ ∑ ij ∈ s ×ˢ s, (A ij.1 + A ij.2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ij hij
        obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
        exact Finset.mem_product.mpr ⟨hi, hj⟩
      · intro ij hij _
        obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
        exact add_nonneg (hA _ hi) (hA _ hj)
    _ = _ := by
      rw [Finset.sum_product]
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring

/-- Negative one-point drift absorbs every pair contribution. We bound
the off-diagonal vertex count by the full square; this only changes the
order-dependent choice of epsilon. -/
theorem sum_drift_absorption {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (D A H : ι → ℝ) (cross weight : ι × ι → ℝ)
    (C k ε L : ℝ) (hε : 0 ≤ ε) (hA : ∀ i ∈ s, 0 ≤ A i)
    (hbudget : 2*ε*(s.card : ℝ) ≤ k)
    (hD : ∀ i ∈ s, D i ≤ C*H i-k*A i)
    (hcross : ∀ ij ∈ s.offDiag, cross ij ≤ ε*(A ij.1+A ij.2)+L*weight ij) :
    (∑ i ∈ s, D i) + (∑ ij ∈ s.offDiag, cross ij) ≤
      C*(∑ i ∈ s, H i) + L*(∑ ij ∈ s.offDiag, weight ij) := by
  have hsumD := Finset.sum_le_sum hD
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumD
  have hsumcross := Finset.sum_le_sum hcross
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumcross
  have hvertices := mul_le_mul_of_nonneg_left (offDiag_vertex_cost_le s A hA) hε
  rw [Finset.sum_add_distrib] at hvertices
  have hsumA : 0 ≤ ∑ i ∈ s, A i := Finset.sum_nonneg hA
  have htotal := mul_le_mul_of_nonneg_right hbudget hsumA
  nlinarith

lemma absorption_epsilon_pos {k : ℝ} (hk : 0 < k) (m : ℕ) :
    0 < k/(4*((m : ℝ)+1)) := by positivity

lemma absorption_epsilon_budget {k : ℝ} (hk : 0 ≤ k) (m : ℕ) :
    2*(k/(4*((m : ℝ)+1)))*(m : ℝ) ≤ k := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hden : 0 < 4*((m : ℝ)+1) := by positivity
  have he : 2*(k/(4*((m : ℝ)+1)))*(m : ℝ) =
      (2*k*(m : ℝ))/(4*((m : ℝ)+1)) := by ring
  rw [he]
  apply (div_le_iff₀ hden).mpr
  nlinarith

end SLEExactGauge.Multipoint

end

end OAI
