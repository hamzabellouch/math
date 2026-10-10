import OAI.Analysis.CircleDomains.Probability.AffinePhysicalOccupation
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost

namespace OAI

/-! Disjoint restricted original fragments never exceed the original cost.
The physical arclength measure has no atoms and the collar cut tolls vanish. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace C(PathTime, X)] in
theorem timeToll_Icc_eq_Ioo (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    {a b : PathTime} (ha : m (γ a) = 0) (hb : m (γ b) = 0) :
    timeToll γ (Icc a b) m = timeToll γ (Ioo a b) m := by
  apply timeToll_eq_of_zero_difference γ m Ioo_subset_Icc_self
  intro t ht
  by_cases hta : t = a
  · simpa only [hta] using ha
  by_cases htb : t = b
  · simpa only [htb] using hb
  exact (ht.2 ⟨lt_of_le_of_ne ht.1.1 (Ne.symm hta), lt_of_le_of_ne ht.1.2 htb⟩).elim

theorem physicalTollCost_affine (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) {a b : PathTime} (hab : a < b)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (ha : m (γ.val a) = 0) (hb : m (γ.val b) = 0) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) =
      (∫⁻t in Ioo a b, g (physicalValue d.domainEquiv d.basePoint (γ.val t))
        ∂physicalTimeLength d.domainEquiv d.basePoint γ) + timeToll γ.val (Ioo a b) m := by
  unfold physicalTollCost
  rw [physicalCost_affine d.domainEquiv hU d.basePoint γ hab g hg]
  have hphys : (∫⁻t in Icc a b, g (physicalValue d.domainEquiv d.basePoint (γ.val t))
        ∂physicalTimeLength d.domainEquiv d.basePoint γ) =
      ∫⁻t in Ioo a b, g (physicalValue d.domainEquiv d.basePoint (γ.val t))
        ∂physicalTimeLength d.domainEquiv d.basePoint γ :=
    setLIntegral_congr (Ioo_ae_eq_Icc.symm)
  rw [hphys]
  change _ + boundaryToll (affineRestrictedPath a b γ.val) m = _
  rw [boundaryToll_affine γ.val m hab, timeToll_Icc_eq_Ioo γ.val m ha hb]

theorem sum_restricted_physicalTollCost_le {ι : Type*} [Countable ι]
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (a b : ι → PathTime)
    (hab : ∀i, a i < b i) (hdis : Pairwise (Disjoint on fun i => Ioo (a i) (b i)))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (ha : ∀i, m (γ.val (a i)) = 0) (hb : ∀i, m (γ.val (b i)) = 0) :
    (∑'i, physicalTollCost d g m
      (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hab i))) ≤
      physicalTollCost d g m γ := by
  simp_rw [physicalTollCost_affine d hU γ (hab _) g hg m (ha _) (hb _)]
  rw [ENNReal.tsum_add,
    ← lintegral_iUnion (fun _ => measurableSet_Ioo) hdis,
    ← timeToll_iUnion γ.val m _ hdis]
  unfold physicalTollCost
  rw [physicalOccupation_integral d.domainEquiv hU d.basePoint γ g hg,
    boundaryToll_eq_timeToll]
  apply add_le_add
  · simpa only [Measure.restrict_univ] using
      (lintegral_mono_set (μ := physicalTimeLength d.domainEquiv d.basePoint γ)
        (f := fun t => g (physicalValue d.domainEquiv d.basePoint (γ.val t))) (subset_univ _))
  · exact timeToll_mono γ.val m (subset_univ _)

end CircleDomainRigidity

end

end OAI
