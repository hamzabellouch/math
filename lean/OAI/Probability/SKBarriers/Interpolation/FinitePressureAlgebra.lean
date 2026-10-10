import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarMassStability

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_mono (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0  ≤  m i)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    (hfg : ∀ z, f z ≤ g z) (x : ℝ) : hierarchyPressure n m f x ≤ hierarchyPressure n m g x := by
  induction n with
  | zero => exact hfg x
  | succ n ih =>
    exact ih (fun i => m i.castSucc) (fun i => hm i.castSucc)
      (hf.gaussianStep _) (hg.gaussianStep _)
      (fun z => gaussianStep_mono hf hg (hm (Fin.last n)) hfg z)

theorem hierarchyPressure_add_const (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (c : ℝ) :
    hierarchyPressure n m (fun z => f z+c)=fun x => hierarchyPressure n m f x+c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hierarchyPressure,gaussianStep_add_prefix hf (fun _ => c)]
    exact ih _ (hf.gaussianStep _)

section Terminal
variable {E A T : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype A] [Nonempty A] [Fintype T] [Nonempty T]

theorem affineLogPartition_const_weight (c : ℝ) (L : A → E →L[ℝ] ℝ) :
    affineLogPartition (fun _ => c) L=fun z => affineLogPartition (fun _ => 0) L z+c := by
  funext z
  simp only [affineLogPartition,zero_add,Real.exp_add,← Finset.mul_sum]
  rw [Real.log_mul (Real.exp_ne_zero _) (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne',Real.log_exp]
  ring

omit [Nonempty A] in
theorem affineLogPartition_restrict (e : T → A) (he : Function.Injective e)
    (c : A → ℝ) (L : A → E →L[ℝ] ℝ) (z : E) :
    affineLogPartition (c ∘ e) (L ∘ e) z ≤ affineLogPartition c L z := by
  unfold affineLogPartition
  apply Real.log_le_log (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)
  classical
  change (∑ t : T, (fun a => Real.exp (c a+L a z)) (e t)) ≤ ∑ a : A, Real.exp (c a+L a z)
  rw [← Finset.sum_image (s:=Finset.univ) (f:=fun a => Real.exp (c a+L a z)) (g:=e)
    (fun a _ b _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)

theorem affineLogPartition_product (N : ℕ) (c : Fin N → A → ℝ)
    (L : Fin N → A → E →L[ℝ] ℝ) :
    affineLogPartition (fun s : Fin N → A => ∑ i, c i (s i)) (fun s => ∑ i, L i (s i))=
      fun z => ∑ i, affineLogPartition (c i) (L i) z := by
  funext z
  simp only [affineLogPartition,sum_apply,← Finset.sum_add_distrib,Real.exp_sum]
  rw [← Fintype.prod_sum (fun i a => Real.exp (c i a+L i a z)),Real.log_prod]
  intro i _
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
end Terminal

end SK.Analytic

end
end

end OAI
