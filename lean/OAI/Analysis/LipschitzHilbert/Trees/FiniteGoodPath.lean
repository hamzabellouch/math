import OAI.Analysis.LipschitzHilbert.Trees.PathExpansion

namespace OAI

/-! Good-path domination from an exact finite top expansion and the
proved individual terminal-probability cap. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
variable {τ : Type*} [DecidableEq τ]

/-- The bad terminal tops carry at most half the original amount. -/
theorem finite_good_path_domination (S bad : Finset τ) (hbadS : bad ⊆ S)
    (w e Q : τ → ℝ) (V C : ℝ) (hV : 0 < V)
    (htotal : ∑ t ∈ S, e t*Q t = V)
    (hprob : ∀ t ∈ bad, e t*Q t/V ≤ C*w t)
    (he : ∀ t ∈ S, e t ≤ C*w t) (hQ : ∀ t ∈ S, 0 ≤ Q t)
    (hbad : C*(∑ t ∈ bad, w t) ≤ 1/2) :
    V ≤ 2*C*∑ t ∈ S\bad, w t*Q t := by
  classical
  have hbadAmount : (∑ t ∈ bad, e t*Q t) ≤ V/2 := by
    calc
      _ ≤ ∑ t ∈ bad, (C*w t)*V := Finset.sum_le_sum fun t ht =>
        (div_le_iff₀ hV).mp (hprob t ht)
      _ = (C*(∑ t ∈ bad, w t))*V := by rw [Finset.mul_sum,Finset.sum_mul]
      _ ≤ (1/2)*V := mul_le_mul_of_nonneg_right hbad hV.le
      _ = V/2 := by ring
  have hsplit := Finset.sum_sdiff hbadS (f := fun t => e t*Q t)
  rw [htotal] at hsplit
  have hgood : (∑ t ∈ S\bad, e t*Q t) ≤ C*∑ t ∈ S\bad, w t*Q t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have htS := (Finset.mem_sdiff.mp ht).1
    exact (mul_le_mul_of_nonneg_right (he t htS) (hQ t htS)).trans_eq (mul_assoc _ _ _)
  linarith

end LipschitzHilbert

end

end OAI
