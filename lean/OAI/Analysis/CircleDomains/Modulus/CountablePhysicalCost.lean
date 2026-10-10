import OAI.Analysis.CircleDomains.Modulus.CountablePhysicalLength
import OAI.Analysis.CircleDomains.Probability.CollarTimeMeasures
import OAI.Analysis.CircleDomains.Probability.PhysicalPieceTimeMeasure

namespace OAI

/-! Exact physical time and weighted occupation measures for collar
concatenations. Parameter multiplicity is preserved. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalTimeLength_collarPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η : FinitePhysicalPath e y₀) (γ : ℕ → FinitePhysicalPath e y₀)
    (hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s) :
    physicalTimeLength e y₀ η = Measure.sum (fun n =>
      (physicalTimeLength e y₀ (γ n)).map (affinePathTime (collarTime (n + 1)) (collarTime n))) := by
  rw [← sum_collar_restrict (physicalTimeLength e y₀ η)]
  congr 1
  funext n
  exact physicalTimeLength_piece e hU y₀ η (γ n)
    (collarTime_strictAnti (Nat.lt_succ_self n)) (hmatch n)

theorem physicalDomainLength_collarPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η : FinitePhysicalPath e y₀) (γ : ℕ → FinitePhysicalPath e y₀)
    (hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s) :
    physicalDomainLength e y₀ η.val = ∑' n, physicalDomainLength e y₀ (γ n).val := by
  rw [← physicalTimeLength_univ e y₀ η, physicalTimeLength_collarPieces e hU y₀ η γ hmatch,
    Measure.sum_apply _ MeasurableSet.univ]
  apply tsum_congr
  intro n
  rw [Measure.map_apply (affinePathTime _ _).continuous.measurable MeasurableSet.univ,
    preimage_univ, physicalTimeLength_univ]

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem physicalCost_collarPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η : FinitePhysicalPath e y₀) (γ : ℕ → FinitePhysicalPath e y₀)
    (hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) = (γ n).val s)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ η) =
      ∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ (γ n) := by
  rw [physicalOccupation_integral e hU y₀ η g hg,
    physicalTimeLength_collarPieces e hU y₀ η γ hmatch, lintegral_sum_measure]
  apply tsum_congr
  intro n
  have hmeas : Measurable (fun t : PathTime => g (physicalValue e y₀ (η.val t))) :=
    hg.comp ((measurable_physicalValue e hU y₀).comp η.val.continuous.measurable)
  rw [lintegral_map hmeas
    (affinePathTime _ _).continuous.measurable, physicalOccupation_integral e hU y₀ (γ n) g hg]
  apply lintegral_congr
  intro t
  simp only [hmatch]

end CircleDomainRigidity

end

end OAI
