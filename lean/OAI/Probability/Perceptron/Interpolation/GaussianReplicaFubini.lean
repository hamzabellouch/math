import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshMarkedKernel

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {S E : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
  [SecondCountableTopology S] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussianRows_joint_continuous {r : ℕ} {v : S→E} (hv : Continuous v) :
    Continuous (fun p : E×(Fin r→S) => gaussianRows (fun i => v (p.2 i)) p.1) := by
  change Continuous (fun p : E×(Fin r→S) => WithLp.toLp 2 (fun i => inner ℝ (v (p.2 i)) p.1))
  fun_prop

lemma twoFreshReplica_fubini {r : ℕ} (ν : Measure (Fin r→S)) [IsProbabilityMeasure ν]
    (v : S→E) (hv : Continuous v) (G : (Fin r→S)→ℝ) (hG : Measurable G)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |G x|≤C)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    (∫ g, ∫ x, G x*Ψ (gaussianRows (fun i => v (x i)) g.1)*
      Φ (gaussianRows (fun i => v (x i)) g.2) ∂ν
      ∂(stdGaussian E).prod (stdGaussian E)) =
    ∫ x, G x*freshMarkedMatrixKernel Ψ (Matrix.gram ℝ (fun i => v (x i)))*
      freshMarkedMatrixKernel Φ (Matrix.gram ℝ (fun i => v (x i))) ∂ν := by
  let P := (stdGaussian E).prod (stdGaussian E)
  have hc₁ : Continuous (fun p : (E×E)×(Fin r→S) =>
      Ψ (gaussianRows (fun i => v (p.2 i)) p.1.1)) :=
    Ψ.continuous.comp ((gaussianRows_joint_continuous (r:=r) hv).comp
      (continuous_fst.fst.prodMk continuous_snd))
  have hc₂ : Continuous (fun p : (E×E)×(Fin r→S) =>
      Φ (gaussianRows (fun i => v (p.2 i)) p.1.2)) :=
    Φ.continuous.comp ((gaussianRows_joint_continuous (r:=r) hv).comp
      (continuous_fst.snd.prodMk continuous_snd))
  have hm : Measurable (fun p : (E×E)×(Fin r→S) => G p.2*
      Ψ (gaussianRows (fun i => v (p.2 i)) p.1.1)*Φ (gaussianRows (fun i => v (p.2 i)) p.1.2)) :=
    ((hG.comp measurable_snd).mul hc₁.measurable).mul hc₂.measurable
  have hi : Integrable (fun p : (E×E)×(Fin r→S) => G p.2*
      Ψ (gaussianRows (fun i => v (p.2 i)) p.1.1)*Φ (gaussianRows (fun i => v (p.2 i)) p.1.2))
      (P.prod ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (C*‖Ψ‖*‖Φ‖)
    exact ae_of_all _ fun p => by
      simp only [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (mul_le_mul (hb _) (Ψ.norm_coe_le_norm _) (abs_nonneg _) hC)
        (Φ.norm_coe_le_norm _) (abs_nonneg _) (mul_nonneg hC (norm_nonneg _))
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp_rw [mul_assoc]
    rw [integral_const_mul,freshMarkedMatrixKernel_two]

lemma gibbs_twoFreshReplica_fubini {r : ℕ} (μ : Measure S) [IsProbabilityMeasure μ]
    {H : S→ℝ} (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (v : S→E) (hv : Continuous v) (G : (Fin r→S)→ℝ) (hG : Measurable G)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x, |G x|≤C)
    (Ψ Φ : EuclideanSpace ℝ (Fin r) →ᵇ ℝ) :
    (∫ g, gibbsReplicaMean μ H r (fun x => G x*Ψ (gaussianRows (fun i => v (x i)) g.1)*
      Φ (gaussianRows (fun i => v (x i)) g.2)) ∂(stdGaussian E).prod (stdGaussian E)) =
    gibbsReplicaMean μ H r (fun x => G x*freshMarkedMatrixKernel Ψ (Matrix.gram ℝ (fun i => v (x i)))*
      freshMarkedMatrixKernel Φ (Matrix.gram ℝ (fun i => v (x i)))) := by
  let := tilt_law_probability_of_integrable μ (by simpa only [one_mul] using hi :
    Integrable (fun x => Real.exp (1*H x)) μ)
  simp_rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  exact twoFreshReplica_fubini _ v hv G hG hC hb Ψ Φ
end SphericalPerceptronFreeEnergy
end

end OAI
