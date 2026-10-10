import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Gluing.FreshTrial
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_allOpen (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (allOpen S)=∏ e∈hS.toFinset, bitMeasure (q e) {True} := by
  have he : allOpen S=⋂ e∈hS.toFinset, {ω : Set E | (e∈ω)=True} := by
    ext ω
    simp [allOpen,Set.subset_def]
  rw [he,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e True)
  · intro e _
    exact ⟨{True},MeasurableSet.singleton _,rfl⟩

lemma law_allOpen_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N) (hq : ∀ e∈S, (p : ℝ) ≤ q e) :
    (p : ℝ)^N ≤ (law q).real (allOpen S) := by
  rw [measureReal_def,law_allOpen q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (p : ℝ)^S.ncard := pow_le_pow_of_le_one p.2.1 p.2.2 hN
    _ = ∏ e∈hS.toFinset, (p : ℝ) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro edge hedge; exact p.2.1
      · intro e he
        change (p : ℝ) ≤ (bitMeasure (q e)).real {True}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,ite_true] using hq e (hS.mem_toFinset.mp he)
end BernoulliProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBalls_disjoint {v w : V} {n : ℕ} (h : w∉G.vertexBall v (n+n)) :
    Disjoint (G.vertexBall v n) (G.vertexBall w n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact h (G.vertexBall_add hz n (G.vertexBall_comm.mp hz'))

lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)

lemma inward_trials_disjoint (F : V → Set E) (m : ℕ)
    (hF : ∀ v, F v⊆G.inducedEdges (G.vertexBall v (2*m+1)))
    {v w : V} (h : w∉G.vertexBall v (4*m+2)) : Disjoint (F v) (F w) := by
  have h' : w∉G.vertexBall v ((2*m+1)+(2*m+1)) := by
    simpa only [show (2*m+1)+(2*m+1)=4*m+2 by omega] using h
  exact (G.inducedEdges_disjoint (G.vertexBalls_disjoint h')).mono (hF v) (hF w)

end BondGraph
end CriticalPercolation
end
end
end

end OAI
