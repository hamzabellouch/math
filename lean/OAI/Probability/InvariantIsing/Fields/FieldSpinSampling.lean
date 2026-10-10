import OAI.Probability.InvariantIsing.Fields.FieldScalarOverlap
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorLabeled
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace OAI

/-! Actual spin sampling and Gaussian transitions for the scalar Ising
recursion. The transition kernels remain probabilities at zero variance. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def scalarSpinKernel : Kernel ℝ Bool :=
  ⟨fun z => gibbsProbability (PMF.uniformOfFintype Bool).toMeasure
      (fun σ => z * spinValue σ),
    measurable_gibbsProbability
      (ν := fun _ : ℝ => (PMF.uniformOfFintype Bool).toMeasure)
      (H := fun p : ℝ × Bool => p.1 * spinValue p.2) measurable_const
      (measurable_fst.mul ((measurable_of_finite spinValue).comp measurable_snd))⟩

instance scalarSpinKernel_markov : IsMarkovKernel scalarSpinKernel := by
  constructor
  intro z
  change IsProbabilityMeasure (gibbsProbability (PMF.uniformOfFintype Bool).toMeasure
    (fun σ => z * spinValue σ))
  infer_instance

private lemma integral_uniformBool (f : Bool → ℝ) :
    (∫ σ, f σ ∂(PMF.uniformOfFintype Bool).toMeasure) =
      (2 : ℝ)⁻¹ * (f false + f true) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp only [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_bool, ENNReal.toReal_inv,
    smul_eq_mul, Fintype.sum_bool]
  norm_num
  ring

theorem scalarSpinKernel_mean (z : ℝ) :
    (∫ σ, spinValue σ ∂scalarSpinKernel z) = Real.tanh z := by
  change (∫ σ, spinValue σ ∂gibbsProbability
    (PMF.uniformOfFintype Bool).toMeasure (fun σ => z * spinValue σ)) = _
  rw [gibbsProbability_eq_tilted _ _ Integrable.of_finite,
    integral_tilted_eq_div, integral_uniformBool, integral_uniformBool]
  simp only [spinValue, Bool.false_eq_true, ite_false, ite_true, mul_neg_one, mul_one]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  ring

def fieldTransitionKernel (ζ : ℝ) (v : ℝ≥0) (F : ℝ → ℝ) (hF : Measurable F) :
    Kernel ℝ ℝ := by
  have hν : Measurable (fun z : ℝ => gaussianReal z v) :=
    measurable_gaussianReal.comp (measurable_id.prodMk measurable_const)
  have hW : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (ζ * F p.2))) :=
    (((hF.comp measurable_snd).const_mul ζ).exp.ennreal_ofReal)
  have hm := measurable_normalizeMass.comp
    (measurable_random_withDensity (ν := fun z : ℝ => gaussianReal z v) hν hW)
  exact ⟨fun z => normalizeMass ((gaussianReal z v).withDensity
    (fun u => ENNReal.ofReal (Real.exp (ζ * F u)))),
      hm⟩

instance fieldTransitionKernel_markov (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) :
    IsMarkovKernel (fieldTransitionKernel ζ v F hF) :=
  ⟨fun _ => normalizeMass_probability _⟩

lemma fieldTransitionKernel_eq_tilted (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : ℝ) :
    fieldTransitionKernel ζ v F hF z = (gaussianReal z v).tilted (fun u => ζ * F u) := by
  exact normalizeMass_exp _ _ (hF.const_mul ζ)
    (integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hG ζ)

lemma fieldTransitionKernel_integral (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (a : ℝ → ℝ) (z : ℝ) :
    (∫ u, a u ∂fieldTransitionKernel ζ v F hF z) = fieldSpinTransition ζ v F a z := by
  rw [fieldTransitionKernel_eq_tilted ζ v F hF hG z]
  rfl

/-- Spin law at the end of the actual successive tilted Gaussian
transitions, starting from the given scalar field. -/
def fieldTailSpinKernel : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel ℝ Bool
  | [], _ => scalarSpinKernel
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldTailSpinKernel L ht ∘ₖ
      fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldTailSpinKernel_markov (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : IsMarkovKernel (fieldTailSpinKernel L hL) := by
  induction L with
  | nil => exact scalarSpinKernel_markov
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

theorem fieldTailSpinKernel_mean (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : ℝ) :
    (∫ σ, spinValue σ ∂fieldTailSpinKernel L hL z) =
      fieldScalarMean L (fun u => Real.log (Real.cosh u)) Real.tanh z := by
  induction L generalizing z with
  | nil => exact scalarSpinKernel_mean z
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    change (∫ σ, spinValue σ ∂(fieldTailSpinKernel L ht ∘ₖ
      fieldTransitionKernel av.1 av.2 (fieldScalarValue L (fun u => Real.log (Real.cosh u)))
        hreg.1) z) = _
    rw [Kernel.integral_comp (Integrable.of_finite)]
    simp_rw [ih ht]
    exact fieldTransitionKernel_integral av.1 av.2 _ hreg.1 hreg.2 _ z

end InvariantIsing

end

end OAI
