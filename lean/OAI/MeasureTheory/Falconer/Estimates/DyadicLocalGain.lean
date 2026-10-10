import OAI.MeasureTheory.Falconer.Measures.LocalPruningGain
import OAI.MeasureTheory.Falconer.Geometry.OccupiedCellSeparation

namespace OAI

/-! # Applying local radial collision prunings on the actual occupied dyadic tree -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem dyadic_gain_of_local_prunings (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) (N J : ℕ) (depth : ℕ → ℕ)
    (hdepth : ∀ j ≤ J, depth j ≤ N) (hmono : ∀ j < J, depth j ≤ depth (j+1))
    (A P : Set (Space d)) (hA : μ Aᶜ = 0) {s : ℝ} (hs : 0 < s)
    (hsep : ∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hGcore : G ⊆ Q.occupiedTreeCore μ N ×ˢ P)
    (r : ℝ) (W : ℕ → ℝ) (θ : ℝ≥0∞) (F cost : ℕ → ℝ≥0∞)
    (hθ : 0 < θ) (hθtop : θ ≠ ∞)
    (hsmall : ∀ j < J, Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1)) ≤ s/2)
    (hwidth : ∀ j < J, 2*(Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1)))/(s/2)+2*r ≤ W j)
    (hlocal : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ∃ H : Set (Space d × Space d), MeasurableSet H ∧
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        ((G ∩ ((Q.descendant p).carrier ×ˢ univ)) \ H) ≤ cost j ∧
      ∀ z ∈ H, radialCollisionMass (ProbabilityTheory.cond μ (Q.descendant p).carrier)
        (W j) z ≤ F j) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ (∑ j ∈ Finset.range J, cost j)+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d, μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ r} ≤
        ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  have hpos : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      μ (Q.descendant p).carrier ≠ 0 := fun _ _ _ hp => (Finset.mem_filter.mp hp).2.ne'
  have hdisj : ∀ j ≤ J, (Q.occupiedPaths μ (depth j) : Set (List (Fin d → Bool))).PairwiseDisjoint
      (fun p => (Q.descendant p).carrier) := by
    intro j _ p hp q hq hpq
    exact Q.descendants_disjoint
      (((mem_cubePaths d (depth j) p).mp (Finset.mem_filter.mp hp).1).trans
        ((mem_cubePaths d (depth j) q).mp (Finset.mem_filter.mp hq).1).symm) hpq
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := radial_gain_of_local_prunings μ ν G hG
    (fun _ p => (Q.descendant p).carrier) (fun j => Q.occupiedPaths μ (depth j))
    (fun j p => p.take (depth j)) J
    (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))) W r (s/2) θ F cost
    (by positivity) hθ hθtop (fun _ _ p _ => (Q.descendant p).measurable) hpos hdisj
    (fun j hj _ hp => Q.occupied_parent hQ μ (hmono j hj) hp)
    (fun _ _ _ hp _ hy _ hz => Q.occupied_diameter_bound hQ μ hp hy hz)
    (fun x hx j hj p hp y hy => occupied_cell_separation Q hQ μ A P hA hsep
      (hsmall j hj) hp x (by obtain ⟨z,hz⟩ := hx; exact (hGcore hz).2) y hy)
    hwidth hlocal
    (fun z x hz => Q.occupiedTreeCore_cover μ (hdepth J le_rfl) (hGcore hz).1)
  refine ⟨G',hG',hsub,?_,?_⟩
  · simpa only [measure_univ,mul_one] using hdel
  · intro x u
    simpa only [measure_univ,mul_one] using hbound x u

end Falconer

end OAI
