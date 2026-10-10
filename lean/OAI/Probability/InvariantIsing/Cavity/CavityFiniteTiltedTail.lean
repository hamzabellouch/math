import OAI.Probability.InvariantIsing.Cavity.CavityFiniteLabeledMoment
import OAI.Probability.InvariantIsing.Cavity.CavityTiltedTail
import OAI.Probability.InvariantIsing.Cavity.CavityStrictUniformPath

namespace OAI

/-! The full finite spectral cavity laws are uniformly tight, including
when their strict overlap discretization has increasing depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_finite_labeled_square_tail {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] {A : ℝ} (hA : 0 < A) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let R := cavityFiniteCovariancePath ρ eig hρ hsum g p q n
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := cavityLabeledDisorderLaw n (chainExponent cut) S₀ S
    (∫ ω, ((cavityLabeledPriorKernel n R π ω).tilted
      (fun x => cavityLabeledPotential n K L C (ω,x))).real
        {x | A < ‖(cavityLabeledEndpoint n (ω,x)).1‖} ∂P) ≤
      cavityGaussianLinearMomentBound d 2 (cavityMatrixMass L + cavityMatrixMass C)
        (ρ a)⁻¹ / A^2 := by
  intro K R S S₀ P
  have h := cavity_finite_labeled_moment ρ eig hρ hsum B hB g a ha
    p cut hcut hfirst hlast q hq hp htop L C π 2
  have ht := cavity_random_tilted_square_tail P (cavityLabeledPriorKernel n R π)
    (cavityLabeledPriorKernel n R π).measurable (cavityLabeledPotential n K L C)
    (fun z => ‖(cavityLabeledEndpoint n z).1‖)
    (measurable_cavityLabeledPotential n K L C)
    ((measurable_cavityLabeledEndpoint n).fst.norm)
    (h.1.mono fun _ hx => hx.1) (h.1.mono fun _ hx => hx.2) h.2.1 hA h.2.2
  simpa only [abs_norm] using ht

theorem cavity_strict_finite_labeled_tight {m d N k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    ∀ ε > 0, ∃ A > 0, ∀ᶠ n in atTop,
      (∫ ω, ((cavityLabeledPriorKernel n
        (cavityFiniteCovariancePath ρ eig hρ hsum g (cavityStrictUniformPath p n)
          (cavityStrictUniformLevels p n) n) π ω).tilted
        (fun x => cavityLabeledPotential n K L C (ω,x))).real
          {x | A < ‖(cavityLabeledEndpoint n (ω,x)).1‖}
        ∂cavityLabeledDisorderLaw n (chainExponent (uniformCut n))
          (cavityFiniteRootCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (cavityStrictUniformLevels p n))
          (cavityFiniteNoiseCovariance ρ eig hρ hsum g (cavityStrictUniformPath p n)
            (uniformCut n) (cavityStrictUniformLevels p n))) < ε := by
  intro K
  apply cavity_tightness_of_square_tail _ (fun _ => 0) tendsto_const_nhds
  intro n A hA
  simpa only [zero_add, K] using cavity_finite_labeled_square_tail ρ eig hρ hsum B hB
    g a ha (cavityStrictUniformPath p n) (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (cavityStrictUniformLevels p n)
    (cavityStrictUniformLevels_strict p n) (cavityStrictUniformPath_on_cell p n)
    (cavityStrictUniformLevels_mem p n (Fin.last n)).2 L C π hA

end InvariantIsing

end

end OAI
