import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationarySlope
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableInvariantRepresentative
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HilbertOrbitAverage

namespace OAI

/-! # Fixed L2 vectors and orbit averaging for a countable action

This connects the Hilbert-space averaging theorem to measurable functions on
the original probability space. Fixed vectors receive exactly invariant
measurable representatives, rather than just invariant equivalence classes.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set

variable {G X : Type*} [Group G] [Countable G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (μ : Measure X) [SMulInvariantMeasure G X μ]

/-- Simultaneous measurable representative of a fixed vector. -/
theorem fixedL2_invariantRepresentative (v : Lp ℝ 2 μ)
    (hfix : ∀ g : G, stationaryPullback μ g v = v) :
    ∃ F : X → ℝ, Measurable F ∧ F =ᵐ[μ] v ∧ ∀ (g : G) x, F (g • x) = F x := by
  apply aemeasurable_invariantRepresentative μ v (Lp.aestronglyMeasurable v).aemeasurable
  intro g
  have hp : Lp.compMeasurePreserving (fun x : X => g • x)
      (measurePreserving_smul g μ) v = v := by
    simpa only [stationaryPullback, inv_inv] using hfix g⁻¹
  have he := Lp.coeFn_compMeasurePreserving v (measurePreserving_smul g μ)
  rw [hp] at he
  exact he.symm

attribute [local instance] stationaryL2Action

/-- Convex orbit averaging produces an exactly invariant measurable limit. -/
theorem exists_L2_orbitAverage (v : Lp ℝ 2 μ) :
    ∃ (w : Lp ℝ 2 μ) (F : X → ℝ),
      w ∈ closure (convexHull ℝ (range (fun g : G => stationaryPullback μ g v))) ∧
      Measurable F ∧ F =ᵐ[μ] w ∧ ∀ (g : G) x, F (g • x) = F x := by
  obtain ⟨w, hw, hfix⟩ := exists_fixed_in_convex_orbit (G := G) v
  obtain ⟨F, hF, he, hFi⟩ := fixedL2_invariantRepresentative μ w hfix
  exact ⟨w, F, hw, hF, he, hFi⟩

end PolycyclicRecognition

end

end OAI
