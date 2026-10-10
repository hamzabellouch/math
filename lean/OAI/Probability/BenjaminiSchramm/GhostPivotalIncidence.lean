import OAI.Probability.BenjaminiSchramm.WeightedGhostIncidence
import OAI.Probability.BenjaminiSchramm.GhostPivotalWeight

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma oriented_pivotal_weight_le (S : Set V) (e : E) (w : V → ℝ≥0∞) :
    (∑' u : V, ∑' v : V,
      if G e = s(u,v) ∧ u ∈ S ∧ v ∉ S then w v else 0) ≤
      if e ∈ (criticalModel G).incidentEdges S then 2 * ∑ v ∈ (G e).toFinset, w v else 0 := by
  let B := (G e).toFinset
  by_cases he : e ∈ (criticalModel G).incidentEdges S
  · rw [ite_eq_left he]
    rw [tsum_eq_sum (s := B) (fun u hu => by
      apply ENNReal.tsum_eq_zero.mpr
      intro v
      apply ite_eq_right
      intro h
      exact hu (Sym2.mem_toFinset.mpr (by rw [h.1]; simp)))]
    have hrow (u : V) :
        (∑' v : V, if G e = s(u,v) ∧ u ∈ S ∧ v ∉ S then w v else 0) ≤ ∑ v ∈ B, w v := by
      rw [tsum_eq_sum (s := B) (fun v hv => by
        apply ite_eq_right
        intro h
        exact hv (Sym2.mem_toFinset.mpr (by rw [h.1]; simp)))]
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp
    calc
      _ ≤ ∑ _u ∈ B, ∑ v ∈ B, w v := Finset.sum_le_sum fun u _ => hrow u
      _ = (B.card : ℝ≥0∞) * ∑ v ∈ B, w v := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        exact_mod_cast (show B.card ≤ 2 by
          dsimp [B]
          rw [Sym2.card_toFinset]
          split_ifs <;> omega)
  · rw [ite_eq_right he]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro u
    apply ENNReal.tsum_eq_zero.mpr
    intro v
    apply ite_eq_right
    intro h
    exact he ⟨u,h.2.1,by change u ∈ G e; rw [h.1]; simp⟩

end Percolation.BenjaminiSchramm

end

end OAI
