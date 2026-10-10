import Mathlib
import OAI.Probability.Perceptron.Interpolation.TerminalReplicaRestoration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma exp_add_integrable_of_bound (μ : Measure S) {H W : S→ℝ}
    (hi : Integrable (fun x => Real.exp (H x)) μ) (hW : Measurable W)
    {C : ℝ} (hb : ∀ x, W x≤C) : Integrable (fun x => Real.exp (H x+W x)) μ := by
  have h := hi.mul_bdd (hW.exp.aestronglyMeasurable) (ae_of_all μ fun x =>
    show ‖Real.exp (W x)‖≤Real.exp C by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (hb x))
  simpa only [Real.exp_add] using h

lemma product_leaf_restore (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G W : T→ℝ) (hH : Measurable H) (hG : Measurable G) (hW : Measurable W)
    (hi : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t))
    {C : ℝ} (hb : ∀ t, W t≤C) (r : ℕ) (F : (Fin r→T)→ℝ) (hF : Measurable F) :
    gibbsReplicaMean (μ.prod ν) (fun x => H x+W x.2) r (fun x => F (fun i => (x i).2))=
      gibbsReplicaMean ν (fun t => G t+W t) r F := by
  apply gibbsReplicaMean_product_leaf μ ν _ _ (hH.add (hW.comp measurable_snd)) (hG.add hW)
    (exp_add_integrable_of_bound _ hi (hW.comp measurable_snd) (fun x => hb x.2)) _ r F hF
  intro t
  change (∫ s, Real.exp (H (s,t)+W t) ∂μ)=Real.exp (G t+W t)
  simp only [Real.exp_add,integral_mul_const,hp]

lemma gibbsReplicaMean_congr (μ : Measure S) (H G : S→ℝ) (h : ∀ x,H x=G x)
    (r : ℕ) (F K : (Fin r→S)→ℝ) (hF : ∀ x,F x=K x) :
    gibbsReplicaMean μ H r F=gibbsReplicaMean μ G r K := by
  rw [show H=G from funext h,show F=K from funext hF]

end SphericalPerceptronFreeEnergy
end

end OAI
