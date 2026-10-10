import OAI.Probability.InvariantIsing.Fields.FieldGaussianProduct
import OAI.Probability.InvariantIsing.Fields.FieldSpinProduct

namespace OAI

/-! Actual vector spin sampling for independent scalar cavity fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

private lemma measurable_field_product {N : ℕ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    Measurable (fun z : Fin N → ℝ => Measure.pi (fun i => κ (z i))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ => Measurable (fun z : Fin N → ℝ => (Measure.pi (fun i => κ (z i))) s))
    _root_.generateFrom_pi.symm isPiSystem_pi ?_ ?_ ?_ ?_ s hs
  · simp only [measure_empty]
    exact measurable_const
  · rintro s ⟨t, ht, rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ =>
      (κ.measurable_coe (ht i (mem_univ _))).comp (measurable_pi_apply i)
  · intro s hs ih
    have he (z : Fin N → ℝ) : (Measure.pi (fun i => κ (z i))) sᶜ =
        1 - (Measure.pi (fun i => κ (z i))) s := by
      rw [measure_compl hs (measure_ne_top _ _), measure_univ]
    simp_rw [he]
    exact measurable_const.sub ih
  · intro s hd hs ih
    have he (z : Fin N → ℝ) : (Measure.pi (fun i => κ (z i))) (⋃ n, s n) =
        ∑' n, (Measure.pi (fun i => κ (z i))) (s n) := measure_iUnion hd hs
    simp_rw [he]
    exact Measurable.tsum ih

def fieldVectorTransitionKernel (N : ℕ) (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  ⟨fun z => Measure.pi (fun i => fieldTransitionKernel ζ v F hF (z i)),
    measurable_field_product _⟩

instance fieldVectorTransitionKernel_markov (N : ℕ) (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) :
    IsMarkovKernel (fieldVectorTransitionKernel N ζ v F hF) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.pi _))⟩

lemma fieldVectorTransitionKernel_eq_tilted {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    fieldVectorTransitionKernel N ζ v F hF z =
      (Measure.pi (fun i => gaussianReal (z i) v)).tilted (fun y => ζ * ∑ i, F (y i)) :=
  (fieldGaussian_product_tilt ζ v F hF hG z).symm

lemma fieldVectorTransitionKernel_coordinate {N : ℕ} (ζ : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F)
    (a : ℝ → ℝ) (ha : Measurable a) (z : Fin N → ℝ) (j : Fin N) :
    (∫ y, a (y j) ∂fieldVectorTransitionKernel N ζ v F hF z) =
      fieldSpinTransition ζ v F a (z j) := by
  change (∫ y, a (y j) ∂Measure.pi (fun i => fieldTransitionKernel ζ v F hF (z i))) = _
  rw [integral_comp_eval ha.aestronglyMeasurable]
  exact fieldTransitionKernel_integral ζ v F hF hG a (z j)

def fieldVectorSpinKernel (N : ℕ) : Kernel (Fin N → ℝ) (Spin N) :=
  ⟨fun z => gibbsProbability (uniformSpinPrior N : Measure (Spin N)) (fieldEnergy z),
    measurable_gibbsProbability (ν := fun _ : Fin N → ℝ =>
      (uniformSpinPrior N : Measure (Spin N)))
      (H := fun p : (Fin N → ℝ) × Spin N => fieldEnergy p.1 p.2)
      measurable_const (by unfold fieldEnergy; fun_prop)⟩

instance fieldVectorSpinKernel_markov (N : ℕ) : IsMarkovKernel (fieldVectorSpinKernel N) := by
  constructor
  intro z
  change IsProbabilityMeasure (gibbsProbability (uniformSpinPrior N : Measure (Spin N))
    (fieldEnergy z))
  infer_instance

def fieldVectorTailSpinKernel (N : ℕ) : (L : List (ℝ × ℝ≥0)) →
    (∀ av ∈ L, 0 < av.1) → Kernel (Fin N → ℝ) (Spin N)
  | [], _ => fieldVectorSpinKernel N
  | av :: L, hL =>
    let ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    fieldVectorTailSpinKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2
        (fieldScalarValue L (fun z => Real.log (Real.cosh z))) hreg.1

instance fieldVectorTailSpinKernel_markov (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) : IsMarkovKernel (fieldVectorTailSpinKernel N L hL) := by
  induction L with
  | nil => exact fieldVectorSpinKernel_markov N
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    let _ := ih ht
    change IsMarkovKernel (_ ∘ₖ _)
    infer_instance

theorem fieldVectorTailSpinKernel_coordinate_mean (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (z : Fin N → ℝ) (j : Fin N) :
    (∫ σ, spinValue (σ j) ∂fieldVectorTailSpinKernel N L hL z) =
      fieldScalarMean L (fun u => Real.log (Real.cosh u)) Real.tanh (z j) := by
  induction L generalizing z with
  | nil => exact fieldSpinGibbs_coordinate_mean z j
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have hreg := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hmean := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    change (∫ σ, spinValue (σ j) ∂(fieldVectorTailSpinKernel N L ht ∘ₖ
      fieldVectorTransitionKernel N av.1 av.2
        (fieldScalarValue L (fun u => Real.log (Real.cosh u))) hreg.1) z) = _
    rw [Kernel.integral_comp (Integrable.of_finite)]
    simp_rw [ih ht]
    exact fieldVectorTransitionKernel_coordinate av.1 av.2 _ hreg.1 hreg.2 _ hmean.1 z j

end InvariantIsing

end

end OAI
