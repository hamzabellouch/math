import Mathlib
import OAI.Geometry.WeakHessian.Calculus.RadialGammaLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile176
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [ProperSpace X] [SigmaFinite m] in
lemma driftBochner_split (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {V g ξ : X → ℝ} (hg : IsTestFunction m g)
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x,|V x| ≤ B) (hC : ∀ x,|ξ x| ≤ C) :
    driftBochner m V g ξ =
      -(∫ x,Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x ∂m)+
      (∫ x,Real.exp (V x)*ξ x*(laplacian m g x+gamma m V g x)^2 ∂m)+
      (∫ x,(Real.exp (V x)*(laplacian m g x+gamma m V g x))*gamma m ξ g x ∂m) := by
  have hgs := (laplacian_isLaplacian hg.1).1
  have hA := (laplacian_isLaplacian hg.1).2.1.add (memLp_gamma_of_lipschitz hfin hpar hV hgs)
  have hw := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hwb : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := ae_of_all _ fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hi : Integrable (fun x => Real.exp (V x)*ξ x*(laplacian m g x+gamma m V g x)^2) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_sq.bdd_mul hξ.continuous.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using ae_of_all m hC)).bdd_mul hw hwb
  have hj : Integrable (fun x => (Real.exp (V x)*(laplacian m g x+gamma m V g x))*gamma m ξ g x) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_mul (memLp_gamma_of_lipschitz hfin hpar hξ hgs)).bdd_mul hw hwb
  unfold driftBochner
  rw [add_assoc,← integral_add hi hj]
  congr 1
  congr 1
  funext x
  ring

omit [ProperSpace X] [SigmaFinite m] in
lemma driftBochner_radialCutoff_tendsto (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) (o : X) {V g ξ : X → ℝ}
    (hg : IsTestFunction m g) (hq : Sobolev m (fun y => gamma m g g y/2))
    {L T : ℝ≥0} (hV : LipschitzWith L V) (hξ : LipschitzWith T ξ)
    {B C : ℝ} (hB : ∀ x,|V x| ≤ B) (hC : ∀ x,|ξ x| ≤ C) (hξS : Sobolev m ξ) :
    Tendsto (fun n => driftBochner m V g (fun x => ξ x*radialCutoff o n x)) atTop
      (𝓝 (driftBochner m V g ξ)) := by
  have hgs := (laplacian_isLaplacian hg.1).1
  let A := fun x => laplacian m g x+gamma m V g x
  have hA : MemLp A 2 m := (laplacian_isLaplacian hg.1).2.1.add (memLp_gamma_of_lipschitz hfin hpar hV hgs)
  have hw := (Real.continuous_exp.comp hV.continuous).aestronglyMeasurable (μ := m)
  have hwb : ∀ᵐ x ∂m, |Real.exp (V x)| ≤ Real.exp B := ae_of_all _ fun x => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x))
  have hwb' : ∀ᵐ x ∂m, ‖Real.exp (V x)‖ ≤ Real.exp B := by simpa only [Real.norm_eq_abs] using hwb
  have hi1 : Integrable (fun x => Real.exp (V x)*gamma m ξ (fun y => gamma m g g y/2) x) m :=
    (integrable_gamma hfin hξS hq).bdd_mul hw hwb'
  have hm1 : MemLp (fun x => Real.exp (V x)*ξ x) 2 m := by
    simpa only [mul_comm,Function.comp_apply] using memLp_mul_bounded hξS.1 hw hwb
  have ht1 := integral_gamma_radialCutoff_tendsto hfin hpar o hξS.2.1 hq hi1 hm1
  have hi2 : Integrable (fun x => Real.exp (V x)*ξ x*A x^2) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_sq.bdd_mul hξ.continuous.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using ae_of_all m hC)).bdd_mul hw hwb'
  have ht2 := integral_radialCutoff_tendsto o hi2
  have hi3 : Integrable (fun x => (Real.exp (V x)*A x)*gamma m ξ g x) m := by
    simpa only [mul_assoc,Function.comp_apply,Pi.add_apply,Pi.mul_apply] using (hA.integrable_mul (memLp_gamma_of_lipschitz hfin hpar hξ hgs)).bdd_mul hw hwb'
  have hm3 : MemLp (fun x => (Real.exp (V x)*A x)*ξ x) 2 m := by
    have H := memLp_mul_bounded (memLp_mul_bounded hA hξ.continuous.aestronglyMeasurable (ae_of_all m hC)) hw hwb
    convert H using 1
    funext x; simp only [Function.comp_apply]; ring
  have ht3 := integral_gamma_radialCutoff_tendsto hfin hpar o hξS.2.1 hgs hi3 hm3
  have hcB (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]; exact radialCutoff_le_one o n x
  have hcutL (n : ℕ) := lipschitz_mul_bounded hξ (radialCutoff_lipschitz o n) hC (hcB n)
  have hcutB (n : ℕ) (x : X) : |ξ x*radialCutoff o n x| ≤ |C| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hcB n x) (abs_nonneg _)).trans (by simpa using (hC x).trans (le_abs_self C))
  have he (n : ℕ) : (∫ x,Real.exp (V x)*(ξ x*radialCutoff o n x)*A x^2 ∂m) =
      ∫ x,(Real.exp (V x)*ξ x*A x^2)*radialCutoff o n x ∂m := by
    congr 1; funext x; ring
  have ht2' : Tendsto (fun n => ∫ x,Real.exp (V x)*(ξ x*radialCutoff o n x)*A x^2 ∂m) atTop
      (𝓝 (∫ x,Real.exp (V x)*ξ x*A x^2 ∂m)) := by
    simpa only [he] using ht2
  simpa only [driftBochner_split hfin hpar hg hV (hcutL _) hB (hcutB _),
    driftBochner_split hfin hpar hg hV hξ hB hC,A] using (ht1.neg.add ht2').add ht3
end WeakHessian

end
end InlinedFile176

end OAI
