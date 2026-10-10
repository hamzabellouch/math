import Mathlib
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative
import OAI.Analysis.IrrationalRotation.Product.ProductSupport

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductNorm

theorem floor_add_eq_indicator (x θ : ℝ) (hx : x ∈ Ico (0 : ℝ) 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (⌊x + θ⌋ : ℝ) = (Ico (1 - θ) 1).indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : 1 - θ ≤ x
  · have hmem : x ∈ Ico (1 - θ) 1 := ⟨h, hx.2⟩
    rw [Set.indicator_of_mem hmem]
    have hf : ⌊x + θ⌋ = (1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith [hx.1, hx.2]
    simp [hf]
  · have hmem : x ∉ Ico (1 - θ) 1 := fun hx' => h hx'.1
    rw [Set.indicator_of_notMem hmem]
    have hf : ⌊x + θ⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith [hx.1, hx.2]
    simp [hf]

theorem lintegral_floor_add (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (∫⁻ x : ℝ in Ico (0 : ℝ) 1, ENNReal.ofReal (⌊x + θ⌋ : ℝ)) =
      ENNReal.ofReal θ := by
  have heq : (fun x : ℝ => ENNReal.ofReal (⌊x + θ⌋ : ℝ)) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)]
      (Ico (1 - θ) 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [floor_add_eq_indicator x θ hx hθ0 hθ1]
    by_cases hm : x ∈ Ico (1 - θ) 1 <;> simp [hm]
  rw [lintegral_congr_ae heq, lintegral_indicator measurableSet_Ico]
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
  rw [Measure.restrict_apply measurableSet_Ico]
  have hsubset : Ico (1 - θ) 1 ⊆ Ico (0 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  rw [inter_eq_left.mpr hsubset, Real.volume_Ico]
  congr 1
  ring

theorem lintegral_tsum_floor_cost {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Ico (0 : ℝ) 1)))
    (c θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) :
    (∫⁻ x, ∑' i, ENNReal.ofReal (c i) * ENNReal.ofReal (⌊u i x + θ i⌋ : ℝ) ∂μ) =
      ∑' i, ENNReal.ofReal (c i) * ENNReal.ofReal (θ i) := by
  have hm (i : ι) : Measurable (fun x : ℝ => ENNReal.ofReal (⌊x + θ i⌋ : ℝ)) := by
    fun_prop
  have hm' (i : ι) : Measurable (fun x : Ω =>
      ENNReal.ofReal (c i) * ENNReal.ofReal (⌊u i x + θ i⌋ : ℝ)) :=
    measurable_const.mul ((hm i).comp (hu i).measurable)
  rw [lintegral_tsum (fun i => (hm' i).aemeasurable)]
  apply tsum_congr
  intro i
  calc
    _ = ENNReal.ofReal (c i) * (∫⁻ x, ENNReal.ofReal (⌊u i x + θ i⌋ : ℝ) ∂μ) :=
      lintegral_const_mul (ENNReal.ofReal (c i))
        (show Measurable (fun x => ENNReal.ofReal (⌊u i x + θ i⌋ : ℝ)) from
          (hm i).comp (hu i).measurable)
    _ = ENNReal.ofReal (c i) * (∫⁻ x : ℝ in Ico (0 : ℝ) 1,
        ENNReal.ofReal (⌊x + θ i⌋ : ℝ)) := by
      congr 1
      exact (hu i).lintegral_comp (hm i)
    _ = _ := by rw [lintegral_floor_add (θ i) (hθ0 i) (hθ1 i)]

theorem lintegral_product_floor_cost {ι : Type*} [Countable ι]
    (c θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) :
    (∫⁻ x : ι → UnitAddCircle,
      ∑' i, ENNReal.ofReal (c i) * ENNReal.ofReal
        (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + θ i⌋ : ℝ)
      ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))) =
      ∑' i, ENNReal.ofReal (c i) * ENNReal.ofReal (θ i) := by
  exact lintegral_tsum_floor_cost _ _
    (fun i => CocycleSupport.measurePreserving_productRepresentative i) c θ hθ0 hθ1

theorem lintegral_neg_log_product_weight {ι : Type*} [Countable ι]
    (c θ : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∀ i, θ i ≤ 1) (hθ : Summable θ) :
    (∫⁻ x : ι → UnitAddCircle, ENNReal.ofReal
      (-Real.log (Real.exp (-(∑' i, c i *
        (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + θ i⌋ : ℝ)))))
      ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))) =
      ∑' i, ENNReal.ofReal (c i) * ENNReal.ofReal (θ i) := by
  rw [← lintegral_product_floor_cost c θ hθ0 hθ1]
  apply lintegral_congr_ae
  filter_upwards [CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ]
    with x hx
  have hfinite : (Function.support (fun i => c i *
      (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + θ i⌋ : ℝ))).Finite := by
    have hf := hx (1 : ℤ)
    simp only [Int.cast_one, one_mul] at hf
    apply hf.subset
    intro i hi
    simp only [Function.mem_support] at hi ⊢
    intro hz
    apply hi
    simp [hz]
  have hsum : Summable (fun i => c i *
      (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + θ i⌋ : ℝ)) :=
    summable_of_hasFiniteSupport hfinite
  have hcost (i : ι) : 0 ≤ c i *
      (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + θ i⌋ : ℝ) := by
    apply mul_nonneg (hc i)
    have hu : 0 ≤ ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) :=
      (AddCircle.equivIco (1 : ℝ) 0 (x i)).property.1
    exact_mod_cast Int.floor_nonneg.mpr (add_nonneg hu (hθ0 i))
  simp only [Real.log_exp, neg_neg]
  rw [ENNReal.ofReal_tsum_of_nonneg hcost hsum]
  exact tsum_congr fun i => ENNReal.ofReal_mul (hc i)

end Invariant233.ProductNorm

end OAI
