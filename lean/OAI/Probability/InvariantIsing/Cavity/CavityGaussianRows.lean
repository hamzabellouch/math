import OAI.Probability.InvariantIsing.Cavity.CavityGaussianSpectral
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

/-! Gaussian rows used to generate the finite fresh frames. Their empirical
Gram matrices converge almost surely to the identity at fixed frame width. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

def cavityGaussianRow (q : ℕ) : Measure (Fin q → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (q : ℕ) : IsProbabilityMeasure (cavityGaussianRow q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin q => gaussianReal 0 1)))

def cavityGaussianRows (q : ℕ) : Measure (ℕ → Fin q → ℝ) :=
  Measure.infinitePi (fun _ => cavityGaussianRow q)

instance (q : ℕ) : IsProbabilityMeasure (cavityGaussianRows q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => cavityGaussianRow q)))

lemma cavityGaussianRow_eval_law {q : ℕ} (i : Fin q) :
    HasLaw (fun x : Fin q → ℝ => x i) (gaussianReal 0 1) (cavityGaussianRow q) :=
  ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : Fin q => gaussianReal 0 1) i).map_eq⟩

lemma cavityGaussianRow_product_integrable {q : ℕ} (i j : Fin q) :
    Integrable (fun x : Fin q → ℝ => x i * x j) (cavityGaussianRow q) := by
  have hi : MemLp (fun x : Fin q → ℝ => x i) 2 (cavityGaussianRow q) := by
    simpa using (cavityGaussianRow_eval_law i).memLp (memLp_id_gaussianReal 2)
  have hj : MemLp (fun x : Fin q → ℝ => x j) 2 (cavityGaussianRow q) := by
    simpa using (cavityGaussianRow_eval_law j).memLp (memLp_id_gaussianReal 2)
  exact hi.integrable_mul hj

lemma cavityGaussianRow_product_integral {q : ℕ} (i j : Fin q) :
    (∫ x : Fin q → ℝ, x i * x j ∂cavityGaussianRow q) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hvar := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral measurable_id.aemeasurable] at hvar
    simp only [id_eq, integral_id_gaussianReal, sub_zero, NNReal.coe_one] at hvar
    have hl := (cavityGaussianRow_eval_law i).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    simpa only [pow_two, Function.comp_apply, ite_true] using hl.trans hvar
  · have hi : iIndepFun (fun k : Fin q => fun x : Fin q → ℝ => x k) (cavityGaussianRow q) :=
      iIndepFun_pi (fun _ => aemeasurable_id)
    have h := (hi.indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    have hm k : (∫ x : Fin q → ℝ, x k ∂cavityGaussianRow q) = 0 := by
      simpa only [Function.comp_apply, integral_id_gaussianReal] using
        (cavityGaussianRow_eval_law k).integral_comp (f := fun x : ℝ => x) (by fun_prop)
    simpa only [hm, zero_mul, ite_eq_right hij] using h

lemma cavityGaussianRows_eval_law (q n : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x n) (cavityGaussianRow q) (cavityGaussianRows q) := by
  refine ⟨(measurable_pi_apply n).aemeasurable, ?_⟩
  exact Measure.infinitePi_map_eval (fun _ : ℕ => cavityGaussianRow q) n

/-- The fixed-width Gaussian Gram matrix tends to the identity. -/
theorem cavityGaussianRows_gram_tendsto (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n i j => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ))
        atTop (𝓝 (1 : Matrix (Fin q) (Fin q) ℝ)) := by
  have hp (i j : Fin q) : ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun n => (∑ k ∈ Finset.range n, x k i * x k j) / (n : ℝ))
        atTop (𝓝 (if i = j then 1 else 0)) := by
    let f := fun x : Fin q → ℝ => x i * x j
    have hf : Measurable f := by fun_prop
    have hind : iIndepFun (fun k => fun x : ℕ → Fin q → ℝ => f (x k)) (cavityGaussianRows q) :=
      iIndepFun_infinitePi (fun _ => hf)
    have hid (k : ℕ) : IdentDistrib (fun x : ℕ → Fin q → ℝ => x k)
        (fun x : ℕ → Fin q → ℝ => x 0) (cavityGaussianRows q) (cavityGaussianRows q) :=
      ⟨(cavityGaussianRows_eval_law q k).aemeasurable,
        (cavityGaussianRows_eval_law q 0).aemeasurable,
        (cavityGaussianRows_eval_law q k).map_eq.trans (cavityGaussianRows_eval_law q 0).map_eq.symm⟩
    have hmean : (∫ x, f (x 0) ∂cavityGaussianRows q) = if i = j then 1 else 0 := by
      exact ((cavityGaussianRows_eval_law q 0).integral_comp hf.aestronglyMeasurable).trans
        (cavityGaussianRow_product_integral i j)
    have h := strong_law_ae_real (fun k (x : ℕ → Fin q → ℝ) => f (x k))
      ((cavityGaussianRows_eval_law q 0).integrable_comp (cavityGaussianRow_product_integrable i j))
      (fun k l hkl => hind.indepFun hkl) (fun k => (hid k).comp hf)
    simpa only [hmean, f] using h
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hp i))] with x hx
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.one_apply] using hx i j

end InvariantIsing

end

end OAI
