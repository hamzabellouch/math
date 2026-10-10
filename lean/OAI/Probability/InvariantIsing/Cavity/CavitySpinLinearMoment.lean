import OAI.Probability.InvariantIsing.Cavity.CavityLinearGaussianMoment
import OAI.Probability.InvariantIsing.Cavity.CavityRootedGaussian

namespace OAI

/-! The remaining linear/spin tilt preserves uniform Gaussian radial moments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_independent_spin_marginal {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d k : ℕ}
    (P : Measure Ω) (κ : Kernel Ω X) [IsMarkovKernel κ]
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((κ ×ₖ Kernel.const Ω π) ∘ₘ P).map (fun x => Y x.1) = (κ ∘ₘ P).map Y := by
  change ((κ ×ₖ Kernel.const Ω π) ∘ₘ P).map (Y ∘ Prod.fst) = _
  rw [← Measure.map_map hY measurable_fst, Measure.map_comp P _ measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]

theorem cavity_spin_linear_tilt_gaussian_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {d k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω X) [IsMarkovKernel κ]
    (Y : X → EuclideanSpace ℝ (Fin d)) (hY : Measurable Y)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hLaw : (κ ∘ₘ P).map Y = multivariateGaussian 0 S)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    {M : ℝ} (hSM : ‖S‖ ≤ M) (p : ℕ) :
    let ν := κ ×ₖ Kernel.const Ω π
    let V := fun x : X × Spin k => cavityLogFactor 0 L C (Y x.1) x.2
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (V x)) (ν ω) ∧
      Integrable (fun x => ‖Y x.1‖^p) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ x, ‖Y x.1‖^p ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ x, ‖Y x.1‖^p ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d p (cavityMatrixMass L + cavityMatrixMass C) M := by
  intro ν V
  have hv : Measurable V := by
    unfold V cavityLogFactor cavityQuadratic
    have hy : ∀ i, Measurable (fun x : X × Spin k => Y x.1 i) :=
      fun i => (EuclideanSpace.proj i).measurable.comp (hY.comp measurable_fst)
    have he : ∀ i, Measurable (fun x : X × Spin k => spinValue (x.2 i)) := by
      intro i
      exact (measurable_of_countable (spinValue : Bool → ℝ)).comp
        ((measurable_pi_apply i).comp measurable_snd)
    fun_prop
  exact cavity_linear_tilt_gaussian_moment P ν (fun x => V x.2) (fun x => Y x.1)
    (hv.comp measurable_snd) (hY.comp measurable_fst) S hS
    ((cavity_independent_spin_marginal P κ Y hY π).trans hLaw) hSM
    (add_nonneg (cavityMatrixMass_nonneg L) (cavityMatrixMass_nonneg C)) p
    (fun _ x => cavity_linear_logFactor_growth L C (Y x.1) x.2)

end InvariantIsing

end

end OAI
