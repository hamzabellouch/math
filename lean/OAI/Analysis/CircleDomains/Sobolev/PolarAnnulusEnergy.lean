import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Polar integration on a bounded annulus, with the actual radial weight. -/
open Set Filter Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem lintegral_polar_annulus (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, g z) =
      ∫⁻ r in Ioo a b, ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * g (Complex.polarCoord.symm (r, θ)) := by
  let A := {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}
  let S := Ioo a b
  let T := Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * g (Complex.polarCoord.symm p)
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hP : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hf : Measurable f := by
    apply Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
    apply hg.comp
    change Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hpolar := Complex.lintegral_comp_polarCoord_symm (A.indicator g)
  rw [lintegral_indicator hA] at hpolar
  calc
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * (A.indicator g) (Complex.polarCoord.symm p) := hpolar.symm
    _ = ∫⁻ p, (S ×ˢ T).indicator f p := by
      rw [← lintegral_indicator hP]
      apply lintegral_congr
      intro p
      by_cases hp : p ∈ polarCoord.target
      · have hp0 : 0 < p.1 := hp.1
        have hmem : Complex.polarCoord.symm p ∈ A ↔ p.1 ∈ S := by
          simp only [A, S, mem_ofPred_eq, mem_Ioo, Complex.norm_polarCoord_symm,
            abs_of_pos hp0]
        by_cases hS : p.1 ∈ S
        · have hST : p ∈ S ×ˢ T := ⟨hS, hp.2⟩
          rw [indicator_of_mem hp, indicator_of_mem hST, indicator_of_mem (hmem.mpr hS)]
        · have hST : p ∉ S ×ˢ T := fun h => hS h.1
          rw [indicator_of_mem hp, indicator_of_notMem hST,
            indicator_of_notMem (fun h => hS (hmem.mp h)), mul_zero]
      · have hST : p ∉ S ×ˢ T := by
          rintro ⟨hS, hT⟩
          exact hp ⟨lt_of_le_of_lt ha hS.1, hT⟩
        rw [indicator_of_notMem hp, indicator_of_notMem hST]
    _ = ∫⁻ p in S ×ˢ T, f p := lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo) f
    _ = _ := setLIntegral_prod f hf.aemeasurable

end CircleDomainRigidity

end

end OAI
