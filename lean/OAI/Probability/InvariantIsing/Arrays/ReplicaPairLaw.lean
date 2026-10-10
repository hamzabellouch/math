import OAI.Probability.InvariantIsing.Spectral.SpectralGGGeometry
import OAI.Probability.IsingPerceptron.OrderedQuantile

namespace OAI

/-! The exact two-link marginal of a scalar GG array. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators ENNReal

namespace InvariantIsing

def scalarOverlapLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Ω → RealArray) : Measure ℝ := μ.map (fun x => B x 0 1)

theorem gg_two_link_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → RealArray) (hB : Measurable B)
    (hgg : HasEntryGhirlandaGuerra B μ)
    (hs : ∀ᵐ x ∂μ, ∀ i j, B x i j = B x j i) (i : Fin 2) :
    (2 : ℝ≥0∞) • μ.map (fun x => (B x 0 1, B x i 2)) =
      (scalarOverlapLaw μ B).prod (scalarOverlapLaw μ B) +
        μ.map (fun x => (B x 0 1, B x 0 1)) := by
  classical
  have hm (j k : ℕ) : Measurable (fun x => B x j k) := by fun_prop
  let ζ := scalarOverlapLaw μ B
  let : IsProbabilityMeasure ζ :=
    (Measure.isProbabilityMeasure_map_iff (hm 0 1).aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (μ.map (fun x => (B x 0 1, B x i 2))) :=
    (Measure.isProbabilityMeasure_map_iff ((hm 0 1).prodMk (hm i 2)).aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (μ.map (fun x => (B x 0 1, B x 0 1))) :=
    (Measure.isProbabilityMeasure_map_iff ((hm 0 1).prodMk (hm 0 1)).aemeasurable).mpr inferInstance
  let : IsFiniteMeasure ((2 : ℝ≥0∞) • μ.map (fun x => (B x 0 1, B x i 2))) :=
    (μ.map (fun x => (B x 0 1, B x i 2))).smul_finite (by norm_num)
  apply measure_pair_eq_of_lower_rectangles _ (by norm_num)
  intro a b
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  have hsum : (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase i,
      μ.real ({x | B x 0 1 ≤ a} ∩ {x | B x i j ≤ b})) =
      μ.real ({x | B x 0 1 ≤ a} ∩ {x | B x 0 1 ≤ b}) := by
    fin_cases i
    · change (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 0,
        μ.real ({x | B x 0 1 ≤ a} ∩ {x | B x 0 j ≤ b})) = _
      rw [show (Finset.univ : Finset (Fin 2)).erase 0 = {1} by decide]
      simp only [Finset.sum_singleton, Fin.val_one]
    · change (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase 1,
        μ.real ({x | B x 0 1 ≤ a} ∩ {x | B x 1 j ≤ b})) = _
      rw [show (Finset.univ : Finset (Fin 2)).erase 1 = {0} by decide]
      simp only [Finset.sum_singleton, Fin.val_zero]
      apply measureReal_congr
      filter_upwards [hs] with x hx
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hx 1 0]
  have he := hgg 2 (by omega) i {v : Fin 2 → Fin 2 → ℝ | v 0 1 ≤ a}
    (measurableSet_le (by fun_prop) measurable_const) (Iic b) measurableSet_Iic
  change μ.real ({x | B x 0 1 ≤ a} ∩ {x | B x i 2 ≤ b}) =
    μ.real {x | B x 0 1 ≤ a} * μ.real {x | B x 0 1 ≤ b} / 2 +
      (∑ j ∈ (Finset.univ : Finset (Fin 2)).erase i,
        μ.real ({x | B x 0 1 ≤ a} ∩ {x | B x i j ≤ b})) / 2 at he
  rw [hsum] at he
  have hmap (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) :
      (μ.map (fun x => (F x, G x))).real (Iic a ×ˢ Iic b) =
        μ.real ({x | F x ≤ a} ∩ {x | G x ≤ b}) := by
    rw [map_measureReal_apply (hF.prodMk hG) (measurableSet_Iic.prod measurableSet_Iic)]
    rfl
  have hz (r : ℝ) : ζ.real (Iic r) = μ.real {x | B x 0 1 ≤ r} :=
    map_measureReal_apply (hm 0 1) measurableSet_Iic
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, Measure.add_apply]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  change 2 * (μ.map (fun x => (B x 0 1, B x i 2))).real (Iic a ×ˢ Iic b) =
    (ζ.prod ζ).real (Iic a ×ˢ Iic b) +
      (μ.map (fun x => (B x 0 1, B x 0 1))).real (Iic a ×ˢ Iic b)
  rw [hmap _ _ (hm 0 1) (hm i 2), measureReal_prod_prod, hz a, hz b,
    hmap _ _ (hm 0 1) (hm 0 1)]
  linarith

theorem gg_two_link_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → RealArray) (hB : Measurable B)
    (hgg : HasEntryGhirlandaGuerra B μ)
    (hs : ∀ᵐ x ∂μ, ∀ i j, B x i j = B x j i) (i : Fin 2)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) {C : ℝ} (hbound : ∀ p, |F p| ≤ C) :
    2 * (∫ x, F (B x 0 1, B x i 2) ∂μ) =
      (∫ x, ∫ y, F (x,y) ∂scalarOverlapLaw μ B ∂scalarOverlapLaw μ B) +
        ∫ x, F (x,x) ∂scalarOverlapLaw μ B := by
  have hm (j k : ℕ) : Measurable (fun x => B x j k) := by fun_prop
  let ζ := scalarOverlapLaw μ B
  let : IsProbabilityMeasure ζ :=
    (Measure.isProbabilityMeasure_map_iff (hm 0 1).aemeasurable).mpr inferInstance
  have hp : Integrable F (ζ.prod ζ) := integrable_of_measurable_abs_le hF hbound
  have hd : Integrable F (μ.map (fun x => (B x 0 1, B x 0 1))) :=
    integrable_of_measurable_abs_le hF hbound
  have he := congrArg (fun ρ : Measure (ℝ × ℝ) => ∫ p, F p ∂ρ)
    (gg_two_link_law μ B hB hgg hs i)
  rw [integral_smul_measure, integral_add_measure hp hd, ENNReal.toReal_ofNat, smul_eq_mul] at he
  rw [integral_map_of_stronglyMeasurable ((hm 0 1).prodMk (hm i 2)) hF.stronglyMeasurable,
    integral_map_of_stronglyMeasurable ((hm 0 1).prodMk (hm 0 1)) hF.stronglyMeasurable] at he
  calc
    _ = (∫ p, F p ∂ζ.prod ζ) + ∫ x, F (B x 0 1, B x 0 1) ∂μ := he
    _ = _ := by
      congr 1
      · exact integral_prod _ hp
      · exact (integral_map_of_stronglyMeasurable (hm 0 1)
          (hF.comp (measurable_id.prodMk measurable_id)).stronglyMeasurable).symm

end InvariantIsing

end

end OAI
