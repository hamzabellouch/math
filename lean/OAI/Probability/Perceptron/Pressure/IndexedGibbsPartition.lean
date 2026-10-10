import Mathlib
import OAI.Probability.Perceptron.Variational.IndexedDiagonalField
import OAI.Probability.Perceptron.Variational.IndexedLeafTotal

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace SphericalPerceptronFreeEnergy

lemma indexedLeafProbability_terminal_integral {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (ν : ProbabilityMeasure S) {step : X×S → X} (hs : Measurable step) {H : X → ℝ}
    (hH : Measurable H) (n : ℕ) (b : IndexedCascadeBase n) (hb : IndexedCascadeGood n b)
    (hb' : 0 < ((indexedLeafMeasure n b) univ).toReal)
    (m : IndexedCascadeMarks S n) (x : X) :
    (∫ l, Real.exp (H (indexedLeafState step n (x,m) l)) ∂indexedLeafProbability n b) =
      decoratedTerminalTotal step H n (x,indexedCascadeRealize n (b,m)) /
        decoratedTerminalTotal step (fun _ => 0) n (x,indexedCascadeRealize n (b,m)) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (measurable_of_countable _).aestronglyMeasurable,
    indexedLeafProbability_terminal_identity ν hs hH n b hb hb',ENNReal.toReal_mul,ENNReal.toReal_inv]
  have he := indexedLeafMeasure_terminal_identity ν hs (H := fun _ => 0) measurable_const n b hb m x
  simp only [Real.exp_zero,ENNReal.ofReal_one,lintegral_one] at he
  unfold decoratedTerminalTotal
  rw [he,div_eq_mul_inv,mul_comm]

variable {S I : Type} [MeasurableSpace S] [Fintype I]
variable (ρ : Measure S) [IsProbabilityMeasure ρ]
variable {W : S → ℝ} {V : S → EuclideanSpace ℝ I}
variable (hWm : Measurable W) (hVm : Measurable V) {K C : ℝ}
variable (hW : ∀ s, |W s| ≤ K) (hV : ∀ s, ‖V s‖ ≤ C)

include hWm hVm hW hV

lemma vectorPartition_exp_terminal (c : ℝ) (a : EuclideanSpace ℝ I) :
    (∫ s, Real.exp (W s+inner ℝ (V s) a-c) ∂ρ) =
      Real.exp (vectorLogPartition ρ W (fun s => innerSL ℝ (V s)) a-c) := by
  have hm : Measurable (fun s => innerSL ℝ (V s)) := (innerSL ℝ).continuous.measurable.comp hVm
  have hb : ∀ s, ‖innerSL ℝ (V s)‖ ≤ C := by simpa only [innerSL_apply_norm] using hV
  simp only [Real.exp_sub,integral_div,vectorLogPartition]
  rw [Real.exp_log (vectorPartition_pos ρ hWm hm hW hb a)]
  rfl

lemma indexedGaussian_spin_partition (n : ℕ) (root : I → ℝ) (step : ℕ → I → ℝ)
    (b : IndexedCascadeBase n) (c : ℝ) (g : ℕ → ℝ) :
    tiltPartition (ρ.prod (indexedLeafProbability n b)) (fun x => W x.1+
      countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
        (indexedGaussianRowLength (I := I) n) g x-c) 1 =
    ∫ l, Real.exp (vectorLogPartition ρ W (fun s => innerSL ℝ (V s))
      (indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
        ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
          (indexedGaussianDisorder n I g).2) l 0)-c) ∂indexedLeafProbability n b := by
  let F : S×IndexedLeaf n → ℝ := fun x => W x.1+
      countableGaussianField (indexedGaussianRow n (hierarchyRowCoefficients n root step) V)
        (indexedGaussianRowLength (I := I) n) g x-c
  have hm : Measurable F := ((hWm.comp measurable_fst).add
    ((countableGaussianField_measurable (indexedGaussianRow_measurable n _ hVm)
      (indexedGaussianRowLength_measurable n)).comp (measurable_const.prodMk measurable_id))).sub measurable_const
  change (∫ x, Real.exp (1*F x) ∂ρ.prod (indexedLeafProbability n b)) = _
  simp only [one_mul]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le) hm.exp.aestronglyMeasurable,
    lintegral_prod_symm _ hm.exp.ennreal_ofReal.aemeasurable]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (measurable_of_countable _).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro l
  let a := indexedLeafState (gaussianLinearMarkStep (fun j => diagonalMark (step j))) n
    ((fun _ => diagonalMark root (indexedGaussianDisorder n I g).1),
      (indexedGaussianDisorder n I g).2) l 0
  have he (s : S) : F (s,l) = W s+inner ℝ (V s) a-c := by
    dsimp only [F]
    rw [indexedGaussianRow_diagonal_identity]
  simp_rw [he]
  rw [← vectorPartition_exp_terminal ρ hWm hVm hW hV c a]
  apply (ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  have hv' : ∀ s, ‖innerSL ℝ (V s)‖ ≤ C := by simpa only [innerSL_apply_norm] using hV
  have hi := vectorPartition_integrable ρ hWm ((innerSL ℝ).continuous.measurable.comp hVm) hW hv' a
  simpa only [Real.exp_sub,Function.comp_apply,innerSL_apply_apply] using hi.div_const (Real.exp c)

end SphericalPerceptronFreeEnergy
end

end OAI
