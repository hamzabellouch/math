import OAI.MeasureTheory.Falconer.Recursion.RetainedPairMasks

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable def actualClassMass (Q : DyadicSquare) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) : ℝ≥0 :=
  (μ (actualClassDomain Q μ N B T)).toNNReal

theorem coe_actualClassMass (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) :
    (actualClassMass Q μ N B T : ENNReal) = μ (actualClassDomain Q μ N B T) :=
  ENNReal.coe_toNNReal (measure_ne_top μ _)

instance actualClassMeasure_instFinite (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) : IsFiniteMeasure (actualClassMeasure Q μ N B T) := by
  constructor
  change (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T) univ < ∞
  rw [normalizedClass_apply,univ_inter]
  change (μ (actualClassDomain Q μ N B T))⁻¹ * μ (actualClassDomain Q μ N B T) < ∞
  by_cases h : μ (actualClassDomain Q μ N B T) = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel h (measure_ne_top μ _)]
    exact ENNReal.one_lt_top

theorem actualClassMass_smul_measure (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) :
    actualClassMass Q μ N B T • actualClassMeasure Q μ N B T =
      μ.restrict (actualClassDomain Q μ N B T) := by
  rw [ENNReal.smul_def,coe_actualClassMass]
  simp only [actualClassMeasure,normalizedClass,classMeasure,Measure.restrict_apply_univ]
  change μ (actualClassDomain Q μ N B T) •
    ((μ (actualClassDomain Q μ N B T))⁻¹ • μ.restrict (actualClassDomain Q μ N B T)) = _
  by_cases h : μ (actualClassDomain Q μ N B T) = 0
  · rw [h,zero_smul,Measure.restrict_eq_zero.mpr h]
  · rw [smul_smul,ENNReal.mul_inv_cancel h (measure_ne_top μ _),one_smul]

theorem actualClassMeasure_probability (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (lam : ℝ) {T : List ℕ}
    (hT : T ∈ retainedClassLabels Q μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))) :
    IsProbabilityMeasure (actualClassMeasure Q μ N B T) := by
  apply normalizedClass_probability
  have h := retainedClass_mass_lower Q μ hT
  exact ne_of_gt ((ENNReal.ofReal_pos.mpr (by positivity)).trans_le h)

theorem actualClassMass_sum_le_one (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (N B : ℕ) (t : ENNReal) :
    (∑ T ∈ retainedClassLabels Q μ N B t, (actualClassMass Q μ N B T : ℝ)) ≤ 1 := by
  have h := retainedClass_mass_sum_le_one Q hQ μ N B t
  simp only [classMeasure,Measure.restrict_apply_univ] at h
  change (∑ T ∈ retainedClassLabels Q μ N B t, μ (actualClassDomain Q μ N B T)) ≤ 1 at h
  simp_rw [← coe_actualClassMass Q μ N B] at h
  exact_mod_cast h

end PlanarFalconer

end OAI
