import OAI.Probability.InvariantIsing.Fields.FieldCanonicalEndpoint

namespace OAI

/-! Exponential endpoint bounds compose additively over Markov kernels.
The proof includes integrability, so no undefined Bochner integral is
used in the recursive Gaussian moment estimates. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

theorem kernel_exp_bound_comp (κ η : Kernel ℝ ℝ) [IsMarkovKernel κ] [IsMarkovKernel η]
    (t A B : ℝ)
    (hκ : ∀ z, Integrable (fun y => Real.exp (t * y)) (κ z) ∧
      (∫ y, Real.exp (t * y) ∂κ z) ≤ Real.exp (t * z + A))
    (hη : ∀ z, Integrable (fun y => Real.exp (t * y)) (η z) ∧
      (∫ y, Real.exp (t * y) ∂η z) ≤ Real.exp (t * z + B)) (z : ℝ) :
    Integrable (fun y => Real.exp (t * y)) ((η ∘ₖ κ) z) ∧
      (∫ y, Real.exp (t * y) ∂(η ∘ₖ κ) z) ≤ Real.exp (t * z + A + B) := by
  have hm : StronglyMeasurable (fun y : ℝ => Real.exp (t * y)) := by fun_prop
  have hH : Integrable (fun x => ∫ y, Real.exp (t * y) ∂η x) (κ z) := by
    apply ((hκ z).1.const_mul (Real.exp B)).mono' hm.integral_kernel.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le))]
    simpa only [Real.exp_add, mul_comm] using (hη x).2
  have hI : Integrable (fun y => Real.exp (t * y)) ((η ∘ₖ κ) z) := by
    apply (ProbabilityTheory.integrable_comp_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => (hη x).1), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hH
  refine ⟨hI, ?_⟩
  rw [Kernel.integral_comp hI]
  calc
    _ ≤ ∫ x, Real.exp B * Real.exp (t * x) ∂κ z :=
      integral_mono hH ((hκ z).1.const_mul (Real.exp B))
        (fun x => by simpa only [Real.exp_add, mul_comm] using (hη x).2)
    _ = Real.exp B * (∫ x, Real.exp (t * x) ∂κ z) := integral_const_mul _ _
    _ ≤ Real.exp B * Real.exp (t * z + A) :=
      mul_le_mul_of_nonneg_left (hκ z).2 (Real.exp_pos B).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end InvariantIsing

end

end OAI
