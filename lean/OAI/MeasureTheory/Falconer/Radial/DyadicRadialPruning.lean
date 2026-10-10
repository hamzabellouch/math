import OAI.MeasureTheory.Falconer.Radial.OccupiedRadialTree
import OAI.MeasureTheory.Falconer.Radial.FiniteRadialPruning

namespace OAI

/-! # Radial pruning on actual occupied dyadic descendants -/

namespace Falconer
open Set Metric MeasureTheory NormedSpace
open scoped ENNReal BigOperators
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem dyadic_radial_pruning (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : DyadicCube d) (hQ : 0 < Q.side) (hroot : μ Q.carrierᶜ = 0)
    (N J : ℕ) (hJ : 0 < J) (depth : ℕ → ℕ)
    (hdepth : ∀ j ≤ J, depth j ≤ N) (hmono : ∀ j < J, depth j ≤ depth (j+1))
    (r W : ℕ → ℝ) (Bs Bp capRadius : ℝ) (F K t : ℕ → ℝ≥0∞)
    (P : Set (Space d)) (hP : MeasurableSet P) (hPfull : ν Pᶜ = 0)
    (hPb : ∀ x ∈ P, ‖x‖ ≤ Bp) (hQb : ∀ z ∈ Q.carrier, ‖z‖ ≤ Bs)
    (hfar : ∀ j < J, Real.sqrt d*(Q.side/(2:ℝ)^depth j) < r j)
    (hwidth : ∀ j < J,
      Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))+2*(Bs+Bp)*capRadius ≤ W j)
    (hball : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ν (ball (Q.descendant p).center (r j)) ≤ K j)
    (htrouble : ∀ j < J, ∀ p ∈ Q.occupiedPaths μ (depth j),
      ((ProbabilityTheory.cond μ (Q.descendant p).carrier).prod ν)
        (troublesomePair (ProbabilityTheory.cond μ (Q.descendant p).carrier)
          (Q.descendant p).center (r j) (Real.sqrt d*(Q.side/(2:ℝ)^depth j))
          Bs (W j) (F j)) ≤ t j)
    (θ : ℝ≥0∞) (hθ : 0 < θ) (hθtop : θ ≠ ∞) :
    ∃ G : Set (Space d × Space d), MeasurableSet G ∧
      (ν.prod μ) Gᶜ ≤ (∑ j ∈ Finset.range J, (K j+t j))+(J+1:ℝ≥0∞)*θ ∧
      ∀ x u : Space d,
        μ {z | (x,z) ∈ G ∧ ‖normalize (z-x)-u‖ ≤ capRadius} ≤
          ∏ j ∈ Finset.range J, θ⁻¹*F j := by
  apply finite_radial_pruning μ ν J hJ
    (fun j => Q.occupiedPaths μ (depth j)) (fun _ p => (Q.descendant p).carrier)
    (fun j p => p.take (depth j)) (fun _ p => (Q.descendant p).center)
    r (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth j)) W
    (fun j => Real.sqrt d*(Q.side/(2:ℝ)^depth (j+1))) Bs Bp capRadius F K t
    P (Q.occupiedTreeCore μ N) hP (Q.occupiedTreeCore_measurable μ N)
    hPfull (Q.occupiedTreeCore_full μ N hroot) hPb
    (fun z hz => hQb z hz.1)
    (fun _ _ p _ => (Q.descendant p).measurable)
    (fun _ _ _ hp => (Finset.mem_filter.mp hp).2.ne')
    (fun j _ p hp q hq hpq => Q.descendants_disjoint
      (((mem_cubePaths d (depth j) p).mp (Finset.mem_filter.mp hp).1).trans
        ((mem_cubePaths d (depth j) q).mp (Finset.mem_filter.mp hq).1).symm) hpq)
    (fun j hj z hz => Q.occupiedTreeCore_cover μ (hdepth j hj) hz)
    (fun j _ p hp z hz => ⟨Q.occupied_center_bound hQ μ hp hz,
      hQb z (Q.descendant_subset p hz)⟩)
    hfar
    (fun j hj _ hp => Q.occupied_parent hQ μ (hmono j hj) hp)
    (fun _ _ _ hp _ hy _ hz => Q.occupied_diameter_bound hQ μ hp hy hz)
    hwidth hball htrouble θ hθ hθtop

end Falconer

end OAI
