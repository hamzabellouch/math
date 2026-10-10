import Mathlib
import OAI.Probability.Ballisticity.Estimates.InteriorPairMeasureExt

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma probability_prod_initial_zero (μ ν : Measure C(unitInterval,ℝ))
    (hμ : ∀ᵐ P ∂μ,P 0=0) (hν : ∀ᵐ P ∂ν,P 0=0) [SFinite ν] :
    ∀ᵐ P : RealPathPair ∂μ.prod ν,P.1 0=0 ∧ P.2 0=0 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hμ] with P hP
  filter_upwards [hν] with Q hQ
  exact ⟨hP,hQ⟩

lemma normalJointPast_product_identification (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (hzero : ∀ᵐ P ∂μ,P.1 0=0 ∧ P.2 0=0) :
    μ=(μ.map Prod.fst).prod (μ.map Prod.snd) := by
  let : IsProbabilityMeasure (μ.map Prod.fst) := inferInstance
  let : IsProbabilityMeasure (μ.map Prod.snd) := inferInstance
  have hf : NormalSinglePast (μ.map Prod.fst) c := normalJointPast_single μ c h false
  have hg : NormalSinglePast (μ.map Prod.snd) c := normalJointPast_single μ c h true
  have h0f : ∀ᵐ P ∂μ.map Prod.fst,P 0=0 := by
    rw [ae_map_iff measurable_fst.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)]
    exact hzero.mono fun P hP => hP.1
  have h0g : ∀ᵐ P ∂μ.map Prod.snd,P 0=0 := by
    rw [ae_map_iff measurable_snd.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)]
    exact hzero.mono fun P hP => hP.2
  have hfull := fullNormalJointPast_of_cross μ c h hA hK hcross hz
  have hprod := normalSinglePast_prod (μ.map Prod.fst) (μ.map Prod.snd) c hf hg
  apply interior_pair_measure_ext
  intro I hI
  exact fullNormalJointPast_finite_uniqueness μ _ c hfull hprod hzero
    (probability_prod_initial_zero _ _ h0f h0g) I hI

lemma wiener_path_initial_zero (W : ProbabilityMeasure C(unitInterval,ℝ)) (T : ℝ)
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw T I) :
    ∀ᵐ P ∂(W : Measure C(unitInterval,ℝ)),P 0=0 := by
  have he := wiener_path_eval W T hW 0
  have he0 : ((0:unitInterval):ℝ)=0 := rfl
  simp only [he0,mul_zero,Real.toNNReal_zero,gaussianReal_zero_var] at he
  have hh : ∀ᵐ x ∂(W : Measure C(unitInterval,ℝ)).map (fun P => P 0),x=0 := by
    rw [he]
    simp
  exact (ae_map_iff (continuous_eval_const 0).measurable.aemeasurable (by measurability)).mp hh

end DirectionalTransience

end

end

end OAI
