import OAI.MeasureTheory.Falconer.Shells.FrequencyShell

namespace OAI

/-! # Covering the actual radial interval by its dyadic frequency annuli -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def radialIntervalMeasure (ν : Measure (Sphere d)) (H : ℝ) : Measure (Space d) :=
  Measure.map radialFrequencyMap ((volume.restrict (Icc (-H) H)).prod ν)

instance radialIntervalMeasure_finite (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (H : ℝ) :
    IsFiniteMeasure (radialIntervalMeasure ν H) := by
  unfold radialIntervalMeasure
  infer_instance

theorem radial_interval_cover_step (n : ℕ) :
    Icc (-((2:ℝ)^(n+1))) ((2:ℝ)^(n+1)) ⊆
      Icc (-((2:ℝ)^n)) ((2:ℝ)^n) ∪ radialFrequencyAnnulus ((2:ℝ)^n) := by
  intro t ht
  have hh : |t| ≤ (2:ℝ)^(n+1) := abs_le.mpr ht
  by_cases hs : |t| ≤ (2:ℝ)^n
  · exact Or.inl (abs_le.mp hs)
  · right
    refine ⟨(le_of_not_ge hs),?_⟩
    simpa only [pow_succ,mul_comm] using hh

theorem radial_interval_measure_step (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (n : ℕ) :
    radialIntervalMeasure ν ((2:ℝ)^(n+1)) ≤
      radialIntervalMeasure ν ((2:ℝ)^n)+radialFrequencyMeasure ν ((2:ℝ)^n) := by
  have hvol : volume.restrict (Icc (-((2:ℝ)^(n+1))) ((2:ℝ)^(n+1))) ≤
      volume.restrict (Icc (-((2:ℝ)^n)) ((2:ℝ)^n))+
        volume.restrict (radialFrequencyAnnulus ((2:ℝ)^n)) :=
    (Measure.restrict_mono (radial_interval_cover_step n) le_rfl).trans (Measure.restrict_union_le _ _)
  have hm : Measurable (@radialFrequencyMap d) := by unfold radialFrequencyMap; fun_prop
  have h := Measure.map_mono (Measure.prod_mono hvol (le_refl ν)) hm
  simpa only [radialIntervalMeasure,radialFrequencyMeasure,Measure.add_prod,
    Measure.map_add _ _ hm] using h

theorem radial_interval_dyadic_cover (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (n : ℕ) :
    radialIntervalMeasure ν ((2:ℝ)^n) ≤ radialIntervalMeasure ν 1+
      ∑ j ∈ Finset.range n, radialFrequencyMeasure ν ((2:ℝ)^j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ radialIntervalMeasure ν ((2:ℝ)^n)+radialFrequencyMeasure ν ((2:ℝ)^n) :=
        radial_interval_measure_step ν n
      _ ≤ (radialIntervalMeasure ν 1+∑ j ∈ Finset.range n, radialFrequencyMeasure ν ((2:ℝ)^j))+
          radialFrequencyMeasure ν ((2:ℝ)^n) := add_le_add ih le_rfl
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

end Falconer

end OAI
