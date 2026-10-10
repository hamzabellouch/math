import OAI.Analysis.Pureness.Completion.CompletedMainConstruction
import OAI.Analysis.Pureness.Completion.CompletedSourceLowerBound
import OAI.Analysis.Pureness.Divisibility.RankBudget

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_completed_source_budget (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (a : CornerCompletion A) (ha : 0 ≤ a) (ha0 : a ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (b : CornerCompletion A) (m s E : ℝ), 0 ≤ b ∧ 0 < m ∧ 0 ≤ E ∧
      1 / ((n : ℝ) + 1) < s ∧ s < 1 / (n : ℝ) ∧
      E < (s - 1 / ((n : ℝ) + 1)) * m ∧
      ∀ τ : TracialState A, ENNReal.ofReal m ≤ completedRootRank τ a ∧
        completedRootRank τ b ≤ ENNReal.ofReal s * completedRootRank τ a ∧
        ENNReal.ofReal s * completedRootRank τ a ≤ completedRootRank τ b + ENNReal.ofReal E := by
  obtain ⟨J,m,hm,_,hma⟩ := completedSourceU_uniform_lower_bound hsimple hT a ha ha0
  obtain ⟨s,hslo,hshi⟩ := exists_sandwich_coefficient n hn
  have hs : 0 < s := (by positivity : (0 : ℝ) < 1 / ((n : ℝ)+1)).trans hslo
  let e : ℝ := ((s - 1 / ((n : ℝ)+1))*m)/2
  have he : 0 < e := by dsimp [e]; positivity
  let η : ℕ → ℝ := fun j => e * (1/2 : ℝ)^(j+1)
  have hη (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have hg : HasSum (fun j : ℕ => (1/2 : ℝ)^j) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) using 1
    norm_num
  have hsum : HasSum η e := by
    have h := hg.mul_left (e/2)
    have hf : (fun j : ℕ => (e/2)*(1/2 : ℝ)^j) = η := by
      funext j; dsimp [η]; rw [pow_succ]; ring
    rw [hf, show e/2*2=e by ring] at h
    exact h
  obtain ⟨b,hb,hr⟩ := exists_completed_rank_budget hsimple hinf hT a ha s hs.le η hη hsum.summable
  refine ⟨b,m,s,e,hb,hm,he.le,hslo,hshi,?_,fun τ => ⟨hma τ,?_,?_⟩⟩
  · dsimp [e]; nlinarith [mul_pos (sub_pos.mpr hslo) hm]
  · exact (hr τ).1
  · simpa only [hsum.tsum_eq] using (hr τ).2
end CuntzPureness

end

end OAI
