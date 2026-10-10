import OAI.Analysis.IrrationalRotation.Product.ProductMultiplierFunctionalCalculus
import OAI.Analysis.IrrationalRotation.Product.ProductLogIntegral

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

def weightValue (θ c : ℕ → ℝ) (x : Base) : Set.Icc (0 : ℝ) 1 :=
  ⟨weight θ c x, weight_mem_Icc θ c x⟩

theorem measurable_weightValue (θ c : ℕ → ℝ) : Measurable (weightValue θ c) :=
  (measurable_weight θ c).subtype_mk

def intervalCoordinate : C(Set.Icc (0 : ℝ) 1, ℂ) :=
  ⟨fun t => (t.val : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

def weightMultiplier (θ c : ℕ → ℝ) : Hilbert →L[ℂ] Hilbert :=
  multiplier θ (fun x => (weight θ c x : ℂ)) 1 (by norm_num)
    (measurable_weight θ c).complex_ofReal (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_mem_Icc θ c x).1] using (weight_mem_Icc θ c x).2)

@[simp] theorem weightedOperator_eq_shift_mul_weightMultiplier (θ c : ℕ → ℝ) :
    weightedOperator θ c = shiftOperator * weightMultiplier θ c := rfl

theorem weightValue_representation_coordinate (θ c : ℕ → ℝ) :
    continuousValueRepresentation θ (weightValue θ c) (measurable_weightValue θ c)
      intervalCoordinate = weightMultiplier θ c := by
  apply multiplier_operator_ext
  intro ξ
  have hleft := continuousValueMultiplier_coordinates_ae θ (weightValue θ c)
    (measurable_weightValue θ c) intervalCoordinate ξ
  have hright : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      weightMultiplier θ c ξ x k =
        (weight θ c (rotationIterate θ k x) : ℂ) * ξ x k :=
    multiplier_coordinates_ae θ _ _ _ _ _ ξ
  filter_upwards [hleft, hright] with x hl hr
  intro k
  exact (hl k).trans (hr k).symm

theorem weightMultiplier_vectorDeterminant_formula (θ c : ℕ → ℝ) :
    vectorFugledeKadisonDeterminant traceVector (weightMultiplier θ c) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (weight θ c x ^ 2 + ε.val) ∂baseMeasure) / 2)) := by
  rw [← weightValue_representation_coordinate θ c]
  rw [vectorFugledeKadisonDeterminant_composed_representation baseMeasure
    (weightValue θ c)
    (continuousValueRepresentation θ (weightValue θ c) (measurable_weightValue θ c))
    traceVector (vectorTrace_continuousValueRepresentation θ (weightValue θ c)
      (measurable_weightValue θ c)) intervalCoordinate]
  have hn : ∀ x, ‖intervalCoordinate (weightValue θ c x)‖ = weight θ c x := by
    intro x
    simp only [intervalCoordinate, ContinuousMap.coe_mk, weightValue,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_mem_Icc θ c x).1]
  simp_rw [hn]

theorem weightMultiplier_vectorDeterminant_zero (θ c : ℕ → ℝ)
    (hpos : ∀ᵐ x ∂baseMeasure, 0 < weight θ c x)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightMultiplier θ c) = 0 := by
  rw [weightMultiplier_vectorDeterminant_formula]
  exact ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    (measurable_weight θ c) (weight_mem_Icc θ c) hpos hinf

theorem shiftOperator_mem_unitary :
    shiftOperator ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem weightedOperator_vectorDeterminant_zero_of_ae_pos (θ c : ℕ → ℝ)
    (hpos : ∀ᵐ x ∂baseMeasure, 0 < weight θ c x)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 := by
  let u : unitary (Hilbert →L[ℂ] Hilbert) := ⟨shiftOperator, shiftOperator_mem_unitary⟩
  change vectorFugledeKadisonDeterminant traceVector
    ((u : Hilbert →L[ℂ] Hilbert) * weightMultiplier θ c) = 0
  rw [vectorFugledeKadisonDeterminant_unitary_mul]
  exact weightMultiplier_vectorDeterminant_zero θ c hpos hinf

theorem weightedOperator_vectorDeterminant_zero (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 :=
  weightedOperator_vectorDeterminant_zero_of_ae_pos θ c
    (ae_weight_pos θ c hθ0 hc hθ) hinf

theorem weightedOperator_vectorDeterminant_zero_of_cost_divergence (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (hcost : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 :=
  weightedOperator_vectorDeterminant_zero θ c (fun i => (hθ01 i).1) hc hθ
    ((hasNegInfiniteLogIntegral_iff_tsum θ c hθ01 hc).mpr hcost)

end Invariant233.ProductModel

end

end OAI
