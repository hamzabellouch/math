import OAI.Probability.InvariantIsing.Cavity.CavityGaussianMarkedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityGroupBlockGaussian
import OAI.Probability.InvariantIsing.Cavity.CavityMarkedTopology

namespace OAI

/-! The Gaussian marks attached to a sampled spectral block. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace InvariantIsing

variable {m r q : ℕ} {E : Type*} [MeasurableSpace E]

def cavityBlockMarkedLaw (Q : ProbabilityMeasure E) (ρ : Fin m → ℝ)
    (b : E → SpectralBlock m r) :
    ProbabilityMeasure (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :=
  cavityGaussianMarkedLaw (Q.map (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))))

lemma cavityBlockMarkedLaw_integral (Q : ProbabilityMeasure E) (ρ : Fin m → ℝ)
    (b : E → SpectralBlock m r) (hb : Measurable b)
    (f : SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) → ℝ)
    (hf : Measurable f) {C : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) :
    (∫ p, f p ∂(cavityBlockMarkedLaw (q := q) Q ρ b : Measure
      (SpectralBlock m r × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))))) =
      ∫ x, ∫ y, f (b x,y) ∂multivariateGaussian 0 (cavityGroupBlockCovariance q ρ (b x))
        ∂(Q : Measure E) := by
  let Z := SpectralBlock m r × Matrix (Fin m × (Fin r × Fin q)) (Fin m × (Fin r × Fin q)) ℝ
  let g : Z → ℝ := fun p => ∫ y, f (p.1,y) ∂multivariateGaussian 0 p.2
  have hfm : Measurable (fun p : Z × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) =>
      f (p.1.1,p.2)) := hf.comp (measurable_fst.fst.prodMk measurable_snd)
  have hg : Measurable g :=
    hfm.stronglyMeasurable.integral_kernel_prod_right' (κ := cavityGaussianKernel) |>.measurable
  have hmap : Measurable (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))) :=
    hb.prodMk ((continuous_cavityGroupBlockCovariance q ρ).measurable.comp hb)
  change (∫ p, f p ∂(cavityGaussianMarkedLaw
    (Q.map (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))))) : ℝ) = _
  rw [cavityGaussianMarkedLaw_integral _ f hf hbound]
  change (∫ p, g p ∂((Q : Measure E).map
    (fun x => (b x, cavityGroupBlockCovariance q ρ (b x))))) = _
  rw [integral_map hmap.aemeasurable hg.aestronglyMeasurable]

end InvariantIsing

end

end OAI
