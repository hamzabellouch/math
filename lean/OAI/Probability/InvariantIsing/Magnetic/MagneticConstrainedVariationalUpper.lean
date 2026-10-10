import OAI.Probability.InvariantIsing.Magnetic.MagneticConstrainedUpper
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticPressure_variational_upper
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (N : ℕ → ℕ) (hN : ∀ k, 3 ≤ N k) (hNlim : Tendsto N atTop atTop) (m : ℕ)
    (μ : (k : ℕ) → Measure (SpecialOrthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    (hμinv : ∀ k, (μ k).IsMulLeftInvariant)
    (eig : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : 0 < K) (heig : ∀ k i, |eig k i| ≤ K)
    (I : (k : ℕ) → Fin m → Finset (Fin (N k)))
    (hdis : ∀ k, Set.PairwiseDisjoint (Set.univ : Set (Fin m)) (I k))
    (hcover : ∀ k, Finset.univ.biUnion (I k) = Finset.univ)
    (lam : Fin m → ℝ) (hlam : ∀ k a i, i ∈ I k a → eig k i = lam a)
    (ρ : Fin m → ℝ) (hρpos : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hρ : Tendsto (fun k a => ((I k a).card : ℝ) / N k) atTop (𝓝 ρ))
    {A : Type*} [Fintype A] [DecidableEq A]
    (group : ∀ k, Fin (N k) → A) (count : ℕ → A → ℕ)
    (hcount : ∀ k a, count k a ≤ spinGroupSize (group k) a)
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1)
    (hc : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mag a)/2))
    (hgroup : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γ a) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        restrictedRotatedPressure (spinGroupSlice (group k) (count k)) (eig k) (specialRotation U) (fun _ => 0) ∂μ k) ≤
      (magneticVariationalFunctional (finiteR ρ lam hρpos hρsum) γ mag).toReal + ε := by
  intro ε hε
  obtain ⟨p, S, hS, hp⟩ := exists_finiteMagneticEntropy_trial
    ρ lam hρpos hρsum γ mag hγ hγsum (fun a => (hmag a).le) (half_pos hε)
  have hup := finiteSpectrum_magneticPressure_upper hhaar hgauss N hN hNlim m μ hμinv
    eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ group count hcount γ mag hmag hc hgroup p S hS.le (ε / 2) (half_pos hε)
  filter_upwards [hup] with k hk
  linarith

end InvariantIsing

end

end OAI
