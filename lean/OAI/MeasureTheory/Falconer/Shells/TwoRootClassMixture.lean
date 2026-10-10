import OAI.MeasureTheory.Falconer.Shells.TwoRootCandidates
import OAI.MeasureTheory.Falconer.Estimates.ActualClassMass
import OAI.MeasureTheory.Falconer.Estimates.OuterRootEquation21

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def twoRootClassCoefficient (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (N B₀ B₁ : ℕ) (a : List ℕ × List ℕ) : ℝ≥0 :=
  actualClassMass Q₀ μ N B₀ a.1 * actualClassMass Q₁ ν N B₁ a.2

noncomputable def twoRootClassMeasure (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) : Measure ℝ :=
  (RootShellData.ofOuter Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
    (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2)
    N lam lam sig kap (outerEntry (m₀ a.1) (m₁ a.2) N β) Q₀ Q₁).measure

theorem twoRootClassMeasure_mask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) :
    twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a =
      (((actualClassMeasure Q₀ μ N B₀ a.1).prod (actualClassMeasure Q₁ ν N B₁ a.2)).withDensity
        (fun z => distanceWeight z * twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
          (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β z)).map
            (fun z => dist z.1 z.2) := by
  unfold twoRootClassMeasure
  rw [RootShellData.ofOuter_measure]
  congr 2
  funext z
  simp only [twoRootPairMask,distanceWeight,outerEndpointMask_radial_swap]
  simp only [neg_div]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist z.1 z.2) _)

theorem twoRootClassCoefficient_sum_le_one (Q₀ Q₁ : DyadicSquare)
    (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N B₀ B₁ : ℕ) (lam : ℝ) :
    (∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
      (twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a : ℝ)) ≤ 1 := by
  have h₀ := actualClassMass_sum_le_one Q₀ hQ₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  have h₁ := actualClassMass_sum_le_one Q₁ hQ₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  simp only [retainedRootPairs,twoRootClassCoefficient,NNReal.coe_mul]
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact (mul_le_mul h₀ h₁ (Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)) zero_le_one).trans_eq (mul_one 1)

theorem twoRootClassCoefficient_prod (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N B₀ B₁ : ℕ) (a : List ℕ × List ℕ) :
    twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
      (actualClassMeasure Q₀ μ N B₀ a.1).prod (actualClassMeasure Q₁ ν N B₁ a.2) =
        (μ.prod ν).restrict (actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2) := by
  rw [← Measure.prod_restrict,← actualClassMass_smul_measure Q₀ μ N B₀ a.1,
    ← actualClassMass_smul_measure Q₁ ν N B₁ a.2,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rfl

theorem twoRootClassCoefficient_measure (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (a : List ℕ × List ℕ) :
    twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
      twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a =
        ((μ.prod ν).withDensity (fun z => distanceWeight z *
          twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a z)).map
            (fun z => dist z.1 z.2) := by
  rw [twoRootClassMeasure_mask,
    ← Measure.map_smul _ (continuous_fst.dist continuous_snd).measurable.aemeasurable]
  congr 1
  rw [ENNReal.smul_def,← withDensity_smul_measure,← ENNReal.smul_def,twoRootClassCoefficient_prod]
  rw [← withDensity_indicator ((measurableSet_actualClassDomain ..).prod (measurableSet_actualClassDomain ..))]
  congr 1
  funext z
  classical
  unfold twoRootRetainedMask
  by_cases h : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,mul_zero]

theorem restoredTwoRootCandidate_eq_sum (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
    restoredTwoRootCandidate Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β =
      ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
        twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
          twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a := by
  simp_rw [twoRootClassCoefficient_measure]
  unfold restoredTwoRootCandidate restoredTwoRootMask
  simp_rw [Finset.mul_sum]
  rw [← Measure.map_finset_sum (by fun_prop)]
  congr 1
  ext S hS
  simp only [withDensity_apply _ hS,Measure.finsetSum_apply]
  exact lintegral_finsetSum _ (fun a _ =>
    (show Measurable distanceWeight by unfold distanceWeight; fun_prop).mul
      (measurable_twoRootRetainedMask ..))

theorem restoredTwoRootCandidate_empty (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (h : retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam = ∅) :
    restoredTwoRootCandidate Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β = 0 := by
  simp [restoredTwoRootCandidate,restoredTwoRootMask,h]

end PlanarFalconer

end OAI
