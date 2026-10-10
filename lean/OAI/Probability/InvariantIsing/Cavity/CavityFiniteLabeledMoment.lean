import OAI.Probability.InvariantIsing.Cavity.CavityLabeledTiltMoment

namespace OAI

/-! The full tilted moments in the literal finite labeled model, with
all geometric and spectral hypotheses specialized to the cavity data. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_labeled_moment {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (ℓ : ℕ) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
    (∀ᵐ ω ∂P, Integrable (fun x => Real.exp (cavityLabeledPotential n K L C (ω,x)))
        (cavityLabeledPriorKernel n R π ω) ∧
      Integrable (fun x => ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ)
        ((cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)))) ∧
    Integrable (fun ω => ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x))) P ∧
    (∫ ω, ∫ x, ‖(cavityLabeledEndpoint n (ω,x)).1‖^ℓ
      ∂(cavityLabeledPriorKernel n R π ω).tilted (fun x => cavityLabeledPotential n K L C (ω,x)) ∂P) ≤
      cavityGaussianLinearMomentBound d ℓ (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K R S S₀ P
  have hm := cavity_finite_original_moment ρ eig hρ hsum B hB g a ha p cut hcut hfirst hlast
    q hq hp htop L C π ℓ
  exact cavity_labeled_tilted_radial_moment n (chainExponent cut)
    (chainExponent_admissible hcut hfirst hlast) S₀ R S K L C π ℓ
    (hm.1.mono fun _ h => h.1) ⟨hm.1.mono (fun _ h => h.2), hm.2⟩

end InvariantIsing

end

end OAI
