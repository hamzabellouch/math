import OAI.Probability.InvariantIsing.Spectral.SpectralCanonicalSymbols
import OAI.Probability.InvariantIsing.Fields.CanonicalRootReconstruction

namespace OAI

/-! The actual off-diagonal and diagonal limiting Ward equations identify
the canonical spectral-group paths and their deterministic diagonals. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

 theorem spectralCanonical_identification {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0) :
    let p := spectralSpinQuantilePath Q hP hn
    (∀ a, q a.castSucc = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ s ∂pathMeasure, ∀ a, spectralGroupQuantilePath Q hn a s =
        spectralGroupPath ρ eig hρ hρsum p a s := by
  intro p
  have hs := spectralCanonical_symbols hgg hG q hq hd hE hP hn ρ eig hρ hρsum hoff hdiag
  apply canonical_groups_identification_of_symbols_rootWard ρ eig hρ hρsum p
    (spectralGroupQuantilePath Q hn) (fun a => q a.castSucc)
  · intro a
    filter_upwards [hs] with s hs
    exact hs a
  · exact spectralPartition_quantile_sum hgg hG q hq hd (fun e => hE e e.injective) hP hn
  · intro a b
    exact (spectralCanonicalWard_pair hgg hG q hq hd hE hP hn ρ eig a b (hoff a b) (hdiag a b)).2

end InvariantIsing

end

end OAI
