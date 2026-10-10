import OAI.Analysis.CircleDomains.Selection.PhysicalSubpaths
import OAI.Analysis.CircleDomains.Selection.DyadicTimes
import OAI.Analysis.CircleDomains.Probability.RectifiableOccupationCode

namespace OAI

/-! Borel dyadic physical length and finite-stage occupation data.
Every length here uses the physical metric after inverting the quotient. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

def physicalDyadicPath (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (γ : C(PathTime, X)) : C(PathTime, Y) :=
  totalPhysicalSubpath e (dyadicLeft_le_right n i) y₀ γ

def physicalDyadicLength (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n))
    (γ : C(PathTime, X)) : ℝ≥0∞ :=
  eVariationOn (physicalDyadicPath e y₀ n i γ) univ

def physicalStageLength (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (γ : C(PathTime, X)) : ℝ≥0∞ :=
  ∑ i : Fin (2 ^ n), physicalDyadicLength e y₀ n i γ

def physicalDomainLength (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) : ℝ≥0∞ :=
  ⨆ n : ℕ, physicalStageLength e y₀ n γ

theorem physicalDyadicLength_le_domain (e : G ≃ₜ U) (y₀ : Y)
    (γ : C(PathTime, X)) (n : ℕ) (i : Fin (2 ^ n)) :
    physicalDyadicLength e y₀ n i γ ≤ physicalDomainLength e y₀ γ :=
  (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans
    (le_iSup (fun n => physicalStageLength e y₀ n γ) n)

theorem physicalDyadicPath_rectifiable (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞)
    (n : ℕ) (i : Fin (2 ^ n)) : BoundedVariationOn (physicalDyadicPath e y₀ n i γ) univ :=
  ne_of_lt ((physicalDyadicLength_le_domain e y₀ γ n i).trans_lt hγ)

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_physicalDyadicLength (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (n : ℕ) (i : Fin (2 ^ n)) : Measurable (physicalDyadicLength e y₀ n i) :=
  (measurable_pathVariation univ).comp
    (measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀)

theorem measurable_physicalDomainLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    Measurable (physicalDomainLength e y₀) := by
  apply Measurable.iSup
  intro n
  exact Finset.measurable_sum _ fun i _ => measurable_physicalDyadicLength e hU y₀ n i

theorem measurableSet_finitePhysicalDomainLength (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) :
    MeasurableSet {γ : C(PathTime, X) | physicalDomainLength e y₀ γ < ∞} :=
  measurableSet_lt (measurable_physicalDomainLength e hU y₀) measurable_const

variable [MeasurableSpace Y] [BorelSpace Y]

def physicalStageOccupation (e : G ≃ₜ U) (y₀ : Y) (n : ℕ) (γ : C(PathTime, X)) : Measure Y :=
  ∑ i : Fin (2 ^ n), rectifiableOccupationCode (physicalDyadicPath e y₀ n i γ)

omit [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)] in
theorem physicalStageOccupation_univ (e : G ≃ₜ U) (y₀ : Y)
    {γ : C(PathTime, X)} (hγ : physicalDomainLength e y₀ γ < ∞) (n : ℕ) :
    physicalStageOccupation e y₀ n γ univ = physicalStageLength e y₀ n γ := by
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply,
    rectifiableOccupationCode_univ (physicalDyadicPath_rectifiable e y₀ hγ n _)]
  rfl

theorem measurable_physicalStageOccupation (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (n : ℕ) :
    Measurable (physicalStageOccupation e y₀ n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [physicalStageOccupation, Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro i _
  exact (Measure.measurable_coe hs).comp (measurable_rectifiableOccupationCode.comp
    (measurable_totalPhysicalSubpath e hU (dyadicLeft_le_right n i) y₀))

end CircleDomainRigidity

end

end OAI
