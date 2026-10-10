import OAI.InformationTheory.Entanglement.TraceStateBounds

namespace OAI

noncomputable section
open scoped InnerProductSpace MeasureTheory
open MeasureTheory ContinuousLinearMap
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι X : Type*} [MeasurableSpace X]
variable (b : HilbertBasis ι ℂ H) (μ : Measure X) [IsFiniteMeasure μ]
variable (ρ : X→DensityOperator b)
variable (hρ : ∀ x y : H, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
include hρ
lemma density_coefficient_integrable (x y : H) :
    Integrable (fun z => inner ℂ x ((ρ z).val.val y)) μ := by
  apply (integrable_const (‖x‖*‖y‖)).mono' (hρ x y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => density_coefficient_bound b (ρ z) x y)
def densityIntegralLeft (y : H) : H→L[ℝ]ℂ :=
  ({ toFun x := ∫ z, inner ℂ x ((ρ z).val.val y) ∂μ
     map_add' x x' := by
       simp only [inner_add_left]
       exact integral_add (density_coefficient_integrable b μ ρ hρ x y)
         (density_coefficient_integrable b μ ρ hρ x' y)
     map_smul' r x := by
       change (∫ z, inner ℂ (r • x) ((ρ z).val.val y) ∂μ)=r • _
       calc
         _ = ∫ z, r • inner ℂ x ((ρ z).val.val y) ∂μ := by
           apply integral_congr_ae
           filter_upwards with z
           rw [← Complex.coe_smul r x]
           exact inner_smul_real_left (𝕜 := ℂ) x ((ρ z).val.val y) r
         _ = _ := integral_smul r _ } : H→ₗ[ℝ]ℂ).mkContinuous
    (‖y‖*μ.real Set.univ) (fun x => by
      change ‖∫ z, inner ℂ x ((ρ z).val.val y) ∂μ‖ ≤ (‖y‖*μ.real Set.univ)*‖x‖
      have hh := norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (fun z => density_coefficient_bound b (ρ z) x y))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
def densityIntegralRight (x : H) : H→L[ℝ]ℂ :=
  ({ toFun y := ∫ z, inner ℂ x ((ρ z).val.val y) ∂μ
     map_add' y y' := by
       simp only [map_add,inner_add_right]
       exact integral_add (density_coefficient_integrable b μ ρ hρ x y)
         (density_coefficient_integrable b μ ρ hρ x y')
     map_smul' r y := by
       change (∫ z, inner ℂ x ((ρ z).val.val (r • y)) ∂μ)=r • _
       calc
         _ = ∫ z, r • inner ℂ x ((ρ z).val.val y) ∂μ := by
           apply integral_congr_ae
           filter_upwards with z
           rw [← Complex.coe_smul r y,map_smul]
           exact inner_smul_real_right (𝕜 := ℂ) x ((ρ z).val.val y) r
         _ = _ := integral_smul r _ } : H→ₗ[ℝ]ℂ).mkContinuous
    (‖x‖*μ.real Set.univ) (fun y => by
      change ‖∫ z, inner ℂ x ((ρ z).val.val y) ∂μ‖ ≤ (‖x‖*μ.real Set.univ)*‖y‖
      have hh := norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall (fun z => density_coefficient_bound b (ρ z) x y))
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)
lemma densityIntegral_left_continuous (y : H) :
    Continuous (fun x => ∫ z, inner ℂ x ((ρ z).val.val y) ∂μ) :=
  (densityIntegralLeft b μ ρ hρ y).continuous
lemma densityIntegral_right_continuous (x : H) :
    Continuous (fun y => ∫ z, inner ℂ x ((ρ z).val.val y) ∂μ) :=
  (densityIntegralRight b μ ρ hρ x).continuous

end SecretKey

end

end OAI
