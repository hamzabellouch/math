import Mathlib
import OAI.Probability.GaussianInformation.Kernel.LocalRules

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.FiniteMessage
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open NoisyDrift GaussianTools ReferenceGaussian Noise Bayes Projection Projection.Support
variable {d N : ℕ}
def localRule (rule : BlockRule d N) (v : Fin N) : LocalRule (d/16) d N where
  prob := fun t w => rule.prob (v,t) w
  measurable := fun w => (rule.measurable_prob w).comp (measurable_const.prodMk measurable_id)
  nonneg := fun input message => rule.nonneg_prob (v,input) message
  sum := fun input => rule.sum_prob (v,input)
noncomputable def rowSlice (μ : Measure (Ambient d × Fin N)) (rule : BlockRule d N) (w : Fin N) : Measure (Ambient d) :=
  ((μ.prod (rowLaw d)).withDensity (fun x =>
    ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w))).map (fun x => x.1.1)
lemma measurable_labels : Measurable (fun x : (Ambient d × Fin N) × Rows d => (x.1.2,x.2,labels x.2 x.1.1)) := by
  have hp : Measurable (fun x : (Ambient d × Fin N) × Rows d => labels x.2 x.1.1) := by
    change Measurable (fun x : (Ambient d × Fin N) × Mat (d/16) d => projectVector x.2 x.1.1)
    exact continuous_projectVector.measurable.comp (measurable_snd.prodMk (measurable_fst.fst))
  exact measurable_fst.snd.prodMk (measurable_snd.prodMk hp)
lemma outgoing_graph (μ : Measure (Ambient d × Fin N)) (rule : BlockRule d N) :
    outgoingLaw μ rule=∑ w : Fin N,(rowSlice μ rule w).map (fun s => (s,w)) := by
  unfold outgoingLaw rowSlice
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.map_map (show Measurable (fun s : Ambient d => (s,w)) from measurable_id.prodMk measurable_const)
    (show Measurable (fun x : (Ambient d × Fin N) × Rows d => x.1.1) from measurable_fst.fst)]
  rfl
lemma component_outgoing (μ : Measure (Ambient d × Fin N)) (rule : BlockRule d N) (w : Fin N) :
    component (outgoingLaw μ rule) w=rowSlice μ rule w := by
  rw [outgoing_graph,component_sum]
  simp [component_graph]
lemma response_joint_measurable (rule : BlockRule d N) (w : Fin N) :
    Measurable (fun x : Ambient d × Fin N => (localRule rule x.2).response w x.1) := by
  apply measurable_from_prod_countable_left
  intro v
  exact (localRule rule v).measurable_response w
lemma rowSlice_eq (μ : Measure (Ambient d × Fin N)) [IsFiniteMeasure μ] (rule : BlockRule d N) (w : Fin N) :
    rowSlice μ rule w=∑ v : Fin N,(component μ v).withDensity (fun s => ENNReal.ofReal ((localRule rule v).response w s)) := by
  have : IsProbabilityMeasure (rowLaw d) := by unfold rowLaw; infer_instance
  have hk : Measurable (fun x : (Ambient d × Fin N) × Rows d => ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w)) :=
    ((rule.measurable_prob w).comp (f := fun x : (Ambient d × Fin N) × Rows d => (x.1.2,x.2,labels x.2 x.1.1)) measurable_labels).ennreal_ofReal
  apply Measure.ext_of_lintegral
  intro f hf
  rw [rowSlice,lintegral_map hf (show Measurable (fun x : (Ambient d × Fin N) × Rows d => x.1.1) from measurable_fst.fst),
    lintegral_withDensity_eq_lintegral_mul _ hk (show Measurable (fun x : (Ambient d × Fin N) × Rows d => f x.1.1) from hf.comp measurable_fst.fst)]
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ (show Measurable (fun x : (Ambient d × Fin N) × Rows d => ENNReal.ofReal (rule.prob (x.1.2,x.2,labels x.2 x.1.1) w)*f x.1.1) from hk.mul (hf.comp measurable_fst.fst)).aemeasurable]
  have hrow (x : Ambient d × Fin N) :
      (∫⁻ y,ENNReal.ofReal (rule.prob (x.2,y,labels y x.1) w)*f x.1 ∂rowLaw d)=
        ENNReal.ofReal ((localRule rule x.2).response w x.1)*f x.1 := by
    have hme : Measurable (fun y : Rows d => ENNReal.ofReal (rule.prob (x.2,y,labels y x.1) w)) :=
      (hk.comp (f := fun y : Rows d => (x,y)) (measurable_const.prodMk measurable_id))
    rw [lintegral_mul_const _ hme]
    congr 1
    exact (ofReal_integral_eq_lintegral_ofReal ((localRule rule x.2).integrable_eval w x.1)
      (ae_of_all _ (fun y => (localRule rule x.2).nonneg _ _))).symm
  simp_rw [hrow]
  rw [lintegral_split μ (fun x => ENNReal.ofReal ((localRule rule x.2).response w x.1)*f x.1) ((response_joint_measurable rule w).ennreal_ofReal.mul (hf.comp measurable_fst)),
    lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro v _
  exact (lintegral_withDensity_eq_lintegral_mul _ ((localRule rule v).measurable_response w).ennreal_ofReal hf).symm
end KernelPotential.FiniteMessage

end OAI
