import OAI.MeasureTheory.Falconer.Measures.SimultaneousProjectedFrostman
import OAI.MeasureTheory.Falconer.Slicing.SliceNormalization

namespace OAI

/-! # Normalize the common compact restriction while preserving every projection -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem normalized_projected_frostman (μ : ProbabilityMeasure (Space d))
    (n : ι → ℕ) (P : ∀ i, Space d →L[ℝ] Space (n i))
    {u : ℝ} (hu : 0 < u)
    (henergy : ∀ i, PlanarFalconer.rieszEnergyOn ((μ : Measure (Space d)).map (P i)) u < ∞) :
    ∃ ν : ProbabilityMeasure (Space d),
      IsCompact (ν : Measure (Space d)).support ∧
      (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ i,
        FrostmanBallBound ((ν : Measure (Space d)).map (P i)) u C := by
  obtain ⟨K,hK,hKm,C,hC,hfrost⟩ := simultaneous_projected_frostman μ n P hu henergy
  let ρ := (μ : Measure (Space d)).restrict K
  have hρ : ρ univ ≠ 0 := by simpa [ρ] using hKm.ne'
  let ν := normalizedSliceLaw ρ hρ
  have hmass : 0 < (ρ univ).toReal := ENNReal.toReal_pos hρ (measure_ne_top ρ univ)
  have heq : (ν : Measure (Space d)) = ENNReal.ofReal (((ρ univ).toReal)⁻¹) • ρ := by
    rw [ENNReal.ofReal_inv_of_pos hmass,ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
    rfl
  refine ⟨ν,?_,?_,((ρ univ).toReal)⁻¹*C,mul_pos (inv_pos.mpr hmass) hC,?_⟩
  · apply hK.of_isClosed_subset Measure.isClosed_support
    apply (ν : Measure (Space d)).support_subset_of_isClosed hK.isClosed
    change (ν : Measure (Space d)) Kᶜ = 0
    simp only [heq,Measure.smul_apply,ρ,Measure.restrict_apply hK.measurableSet.compl,
      compl_inter_self,measure_empty,smul_zero]
  · rw [heq]
    exact Measure.smul_absolutelyContinuous.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · intro i x r hr
    rw [heq,Measure.map_smul _ (P i).continuous.measurable.aemeasurable,
      Measure.smul_apply,smul_eq_mul]
    calc
      _ ≤ ENNReal.ofReal (((ρ univ).toReal)⁻¹) * ENNReal.ofReal (C*r^u) :=
        mul_le_mul_right (hfrost i x r hr) _
      _ = ENNReal.ofReal ((((ρ univ).toReal)⁻¹*C)*r^u) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Falconer

end OAI
