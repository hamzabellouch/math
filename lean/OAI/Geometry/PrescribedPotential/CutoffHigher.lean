import Mathlib
import OAI.Geometry.PrescribedPotential.IntegerBounds
import OAI.Geometry.PrescribedPotential.PatchDifferential

namespace OAI

/-! Cutoff Higher. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical BoundedContinuousFunction

namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzCoord_product_zero (κ f : 𝓢(E, ℂ)) :
    schwartzCoord 0 (SchwartzMap.smulLeftCLM ℂ κ f) =
      multiply κ.toBoundedContinuousFunction (schwartzCoord 0 f) := by
  apply l2_injective
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [schwartzCoord_distribution, schwartz_temperate_product_distribution κ.hasTemperateGrowth,
    besselPotential_zero, ContinuousLinearMap.id_apply,
    multiply_distribution _ κ.hasTemperateGrowth, schwartzCoord_distribution,
    besselPotential_zero, ContinuousLinearMap.id_apply]
  rfl

lemma coreBound_coefficient_zero (c : E →ᵇ ℂ)
    (hc : (c : E → ℂ).HasTemperateGrowth) :
    CoreBound 0 0 (SchwartzMap.smulLeftCLM ℂ c) := by
  refine ⟨‖c‖, norm_nonneg _, fun f => ?_⟩
  have he : schwartzCoord 0 (SchwartzMap.smulLeftCLM ℂ c f) =
      multiply c (schwartzCoord 0 f) := by
    apply l2_injective
    simp only [Lp.toTemperedDistributionCLM_apply]
    rw [schwartzCoord_distribution, schwartz_temperate_product_distribution hc,
      besselPotential_zero, ContinuousLinearMap.id_apply,
      multiply_distribution c hc, schwartzCoord_distribution,
      besselPotential_zero, ContinuousLinearMap.id_apply]
  rw [he]
  exact multiply_norm_le _ _

lemma coreBound_product_zero (κ : 𝓢(E, ℂ)) :
    CoreBound 0 0 (SchwartzMap.smulLeftCLM ℂ κ) := by
  refine ⟨‖κ.toBoundedContinuousFunction‖, norm_nonneg _, fun f => ?_⟩
  rw [schwartzCoord_product_zero]
  exact multiply_norm_le _ _

lemma coreBound_product_word (ws : List E) (κ : 𝓢(E, ℂ)) {s : ℝ}
    (hws : (ws.length : ℝ) ≤ s) :
    CoreBound s 0 (fun f => schwartzWord ws (SchwartzMap.smulLeftCLM ℂ κ f)) := by
  induction ws generalizing κ s with
  | nil => exact (coreBound_product_zero κ).comp (CoreBound.id (by simpa using hws))
  | cons w ws ih =>
    have hw : (ws.length : ℝ) + 1 ≤ s := by
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hws
    have hfirst := ih (∂_{w} κ) (s := s) (by linarith)
    have hrest := (ih κ (s := s - 1) (by linarith)).comp
      (coreBound_deriv w (s := s) (t := s - 1) le_rfl)
    convert hfirst.add hrest using 1
    funext f
    change ∂_{w} (schwartzWord ws (SchwartzMap.smulLeftCLM ℂ κ f)) = _
    rw [← GlobalElliptic.word_deriv_comm, schwartz_deriv_product, map_add]
    rfl

lemma coreBound_product_integer (κ : 𝓢(E, ℂ)) (k : ℕ) :
    CoreBound (k : ℝ) (k : ℝ) (SchwartzMap.smulLeftCLM ℂ κ) := by
  have hh := coreBound_of_words_integer k (s := (k : ℝ)) (t := 0)
    (SchwartzMap.smulLeftCLM ℂ κ)
    (fun ws hw => coreBound_product_word ws κ (by exact_mod_cast hw))
  simpa only [zero_add] using hh

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_second_product (v w : E) (κ f : 𝓢(E, ℂ)) :
    ∂_{v} (∂_{w} (SchwartzMap.smulLeftCLM ℂ κ f)) =
      SchwartzMap.smulLeftCLM ℂ κ (∂_{v} (∂_{w} f)) +
        (SchwartzMap.smulLeftCLM ℂ (∂_{v} κ : 𝓢(E, ℂ)) (∂_{w} f) +
          SchwartzMap.smulLeftCLM ℂ (∂_{w} κ : 𝓢(E, ℂ)) (∂_{v} f) +
            SchwartzMap.smulLeftCLM ℂ (∂_{v} (∂_{w} κ) : 𝓢(E, ℂ)) f) := by
  rw [schwartz_deriv_product, lineDerivOp_add, schwartz_deriv_product, schwartz_deriv_product]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_product_assoc {c : E → ℂ} (hc : c.HasTemperateGrowth) (κ f : 𝓢(E, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ c (SchwartzMap.smulLeftCLM ℂ κ f) =
      SchwartzMap.smulLeftCLM ℂ (SchwartzMap.smulLeftCLM ℂ c κ : 𝓢(E, ℂ)) f := by
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hc,
    SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.smulLeftCLM ℂ c κ).hasTemperateGrowth,
    smul_eq_mul, mul_assoc]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_product_comm {c : E → ℂ} (hc : c.HasTemperateGrowth) (κ f : 𝓢(E, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ c (SchwartzMap.smulLeftCLM ℂ κ f) =
      SchwartzMap.smulLeftCLM ℂ κ (SchwartzMap.smulLeftCLM ℂ c f) := by
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hc,
    SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth, smul_eq_mul]
  ring
end SobolevChart

namespace MetricLocalization
open EllipticKernel SobolevChart
variable {n : ℕ}

lemma schwartzDifferential_bound
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ i j, (c i j : EC n → ℂ).HasTemperateGrowth) :
    CoreBound 2 0 (schwartzDifferential c) := by
  change CoreBound 2 0 (fun f => schwartzDifferential c f)
  simp only [schwartzDifferential, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]
  apply CoreBound.sum Finset.univ
  intro i _
  apply CoreBound.sum Finset.univ
  intro j _
  exact (coreBound_coefficient_zero (c i j) (hc i j)).comp
    ((coreBound_deriv _ (s := 1) (t := 0) (by norm_num)).comp
      (coreBound_deriv _ (s := 2) (t := 1) (by norm_num)))

lemma schwartzCutoffError_firstOrder
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ i j, (c i j : EC n → ℂ).HasTemperateGrowth) (κ f : 𝓢(EC n, ℂ)) :
    schwartzCutoffError c κ f = ∑ i, ∑ j,
      (SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.smulLeftCLM ℂ (c i j) (∂_{stdOrthonormalBasis ℝ (EC n) i} κ) : 𝓢(EC n, ℂ))
        (∂_{stdOrthonormalBasis ℝ (EC n) j} f) +
      SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.smulLeftCLM ℂ (c i j) (∂_{stdOrthonormalBasis ℝ (EC n) j} κ) : 𝓢(EC n, ℂ))
        (∂_{stdOrthonormalBasis ℝ (EC n) i} f) +
      SchwartzMap.smulLeftCLM ℂ
        (SchwartzMap.smulLeftCLM ℂ (c i j)
          (∂_{stdOrthonormalBasis ℝ (EC n) i} (∂_{stdOrthonormalBasis ℝ (EC n) j} κ)) : 𝓢(EC n, ℂ)) f) := by
  simp only [schwartzCutoffError, schwartzDifferential, _root_.sub_apply,
    _root_.sum_apply, ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartz_second_product]
  simp only [map_add, schwartz_product_comm (hc i j) κ,
    schwartz_product_assoc (hc i j)]
  abel

 
theorem schwartzCutoffError_bound_integer
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ i j, (c i j : EC n → ℂ).HasTemperateGrowth) (κ : 𝓢(EC n, ℂ)) (k : ℕ) :
    CoreBound ((k : ℝ) + 1) (k : ℝ) (schwartzCutoffError c κ) := by
  change CoreBound ((k : ℝ) + 1) (k : ℝ) (fun f => schwartzCutoffError c κ f)
  simp_rw [schwartzCutoffError_firstOrder c hc κ]
  apply CoreBound.sum Finset.univ
  intro i _
  apply CoreBound.sum Finset.univ
  intro j _
  apply CoreBound.add
  · apply CoreBound.add
    · exact (coreBound_product_integer _ k).comp
        (coreBound_deriv _ (s := (k : ℝ) + 1) (t := (k : ℝ)) (by linarith))
    · exact (coreBound_product_integer _ k).comp
        (coreBound_deriv _ (s := (k : ℝ) + 1) (t := (k : ℝ)) (by linarith))
  · exact (coreBound_product_integer _ k).comp (CoreBound.id (by linarith))
end MetricLocalization

end
end

end OAI
