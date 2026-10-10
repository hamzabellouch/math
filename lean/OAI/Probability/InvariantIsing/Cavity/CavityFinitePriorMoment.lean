import OAI.Probability.InvariantIsing.Cavity.CavityFinitePriorBound
import OAI.Probability.InvariantIsing.Cavity.CavityLabeledPriorMoment

namespace OAI

/-! Ordinary fourth moments for the actual finite spectral cavity prior. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_finite_prior_fourth_moment {m d n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (g : Fin d → Fin m) (p : OverlapPath)
    (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let P := cavityLabeledDisorderLaw n (chainExponent cut)
      (cavityFiniteRootCovariance ρ eig hρ hsum g p q)
      (cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q)
    (∀ᵐ ω ∂P, Integrable (fun x => ‖(cavityLabeledEndpoint n (ω, x)).1‖^4)
      (cavityLabeledPriorKernel n R π ω)) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω) P ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω, x)).1‖^4
      ∂cavityLabeledPriorKernel n R π ω ∂P) ≤
        cavityGaussianLinearMomentBound d 4 0 (∑ a, (ρ a)⁻¹) := by
  intro R P
  have hroot : (cavityFiniteRootCovariance ρ eig hρ hsum g p q).PosSemidef :=
    cavityFiniteCovariance_root_posSemidef ρ eig hρ hsum g
      (cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop 0)
      (finite_overlap_value_mem_unit p cut hcut q hp 0).1
  exact cavity_labeled_prior_fourth_moment n (chainExponent cut)
    (cavityFiniteRootCovariance ρ eig hρ hsum g p q) R
    (cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q)
    hroot
    (cavityFiniteCovariancePath_posDef ρ eig hρ hsum g p cut hfirst hlast q hq hp htop n).posSemidef
    (cavityFiniteNoiseCovariance_posSemidef ρ eig hρ hsum g p cut hcut hfirst hlast q hq hp htop)
    π (cavity_finite_prior_covariance_bound ρ eig hρ hsum g p cut hcut hfirst hlast q hq hp htop)

end InvariantIsing

end

end OAI
