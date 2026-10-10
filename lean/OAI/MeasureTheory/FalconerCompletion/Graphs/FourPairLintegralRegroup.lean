import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.ClassConditional

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set MeasureTheory
open scoped ENNReal
variable {V : Type*} [MeasurableSpace V]

theorem four_pair_lintegral_regroupND (μ ν : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : (V × V) × (V × V) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂(μ.prod ν).prod (μ.prod ν)) =
      ∫⁻ xx, ∫⁻ yy, F ((xx.1,yy.1),(xx.2,yy.2)) ∂ν.prod ν ∂μ.prod μ := by
  calc
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ x', ∫⁻ y', F ((x,y),(x',y')) ∂ν ∂μ ∂ν ∂μ := by
      rw [lintegral_prod _ hF.aemeasurable,
        lintegral_prod _ hF.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      exact lintegral_prod _ ((hF.comp (by fun_prop)).aemeasurable)
    _ = ∫⁻ x, ∫⁻ x', ∫⁻ y, ∫⁻ y', F ((x,y),(x',y')) ∂ν ∂ν ∂μ ∂μ := by
      apply lintegral_congr
      intro x
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (V × V) × V => F ((x,z.1.1),(z.1.2,z.2))) :=
        hF.comp (by fun_prop)
      exact hm.lintegral_prod_right'.aemeasurable
    _ = _ := by
      have hm : Measurable (fun z : (V × V) × (V × V) =>
          F ((z.1.1,z.2.1),(z.1.2,z.2.2))) := hF.comp (by fun_prop)
      rw [lintegral_prod _ hm.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro x'
      exact (lintegral_prod (fun yy : V × V => F ((x,yy.1),(x',yy.2)))
        ((hF.comp (by fun_prop)).aemeasurable)).symm

theorem pair_collision_fiber_boundND (μ ν : Measure V)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set ((V × V) × (V × V))) (hS : MeasurableSet S)
    (K : ℝ≥0∞)
    (hbound : ∀ᵐ xx ∂μ.prod μ,
      (ν.prod ν) {yy | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} ≤ K) :
    ((μ.prod ν).prod (μ.prod ν)) S ≤ (μ univ)^2*K := by
  have hm : Measurable (S.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hS
  have he := four_pair_lintegral_regroupND μ ν _ hm
  rw [lintegral_indicator hS,lintegral_const] at he
  simp only [one_mul,Measure.restrict_apply_univ] at he
  have hinner (xx : V × V) :
      (∫⁻ yy, S.indicator (fun _ => (1:ℝ≥0∞)) ((xx.1,yy.1),(xx.2,yy.2)) ∂ν.prod ν) =
      (ν.prod ν) {yy | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} := by
    change (∫⁻ yy, {yy : V × V | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S}.indicator
      (fun _ => (1:ℝ≥0∞)) yy ∂ν.prod ν) = _
    have hmeas : MeasurableSet {yy : V × V | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} :=
      hS.preimage (show Measurable (fun yy : V × V => ((xx.1,yy.1),(xx.2,yy.2))) by fun_prop)
    rw [lintegral_indicator hmeas]
    simp
  simp_rw [hinner] at he
  rw [he]
  calc
    _ ≤ ∫⁻ _xx, K ∂μ.prod μ := lintegral_mono_ae hbound
    _ = _ := by
      rw [lintegral_const,← univ_prod_univ,Measure.prod_prod]
      simp only [pow_two,mul_comm]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
