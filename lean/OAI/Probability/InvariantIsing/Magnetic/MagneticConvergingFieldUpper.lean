import OAI.Probability.InvariantIsing.Magnetic.MagneticConvergingVariationalUpper
import OAI.Probability.InvariantIsing.Core.FiniteVariationalBounds
import OAI.Probability.InvariantIsing.Fields.SpinGroupFieldPressure
import OAI.Probability.InvariantIsing.Magnetic.RestrictedPressureFluctuation

namespace OAI

/-! The finite-spectrum pressure upper bound after taking the path infimum,
under Haar and Gaussian concentration hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem finiteSpectrum_magneticFieldPressure_converging_upper
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
    (γs mags : ℕ → A → ℝ) (γ mag : A → ℝ)
    (hγs : Tendsto γs atTop (𝓝 γ)) (hmags : Tendsto mags atTop (𝓝 mag))
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a|<1)
    (hc : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mags k a)/2))
    (hgroup : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γs k a) (b : A → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∫ U : SpecialOrthogonal (N k),
        restrictedRotatedPressure (spinGroupSlice (group k) (count k)) (eig k) (specialRotation U) (fun i => b (group k i)) ∂μ k) ≤
      (magneticVariationalFunctional (finiteR ρ lam hρpos hρsum) γ mag).toReal +
        (∑ a, γ a*b a*mag a) + ε := by
  intro ε hε
  obtain ⟨B,hB,hfluc⟩ := haar_restrictedPressure_mean_fluctuation hhaar
  have hf : Tendsto (fun k => ∑ a, γs k a*b a*mags k a) atTop
      (𝓝 (∑ a, γ a*b a*mag a)) := by
    apply tendsto_finsetSum
    intro a _
    exact (((tendsto_pi_nhds.mp hγs) a).mul_const (b a)).mul ((tendsto_pi_nhds.mp hmags) a)
  have hup := finiteSpectrum_magneticPressure_converging_variational_upper hhaar hgauss
    N hN hNlim m μ hμinv eig K hK heig I hdis hcover lam hlam ρ hρpos hρsum hρ
    group count hcount γs mags γ mag hγs hmags hγ hγsum hmag hc hgroup (ε/2) (half_pos hε)
  filter_upwards [hup, hf.eventually (Iio_mem_nhds (show (∑ a, γ a*b a*mag a)<
    (∑ a, γ a*b a*mag a)+ε/2 by linarith))] with k hk hfk
  rw [mean_restrictedRotatedPressure_group_field (by have := hN k; omega) (μ k)
    (group k) (count k) (hcount k) (γs k) (mags k) b (hgroup k) (hc k) (eig k)
    (hfluc (N k) (hN k) (μ k) inferInstance (hμinv k) _
      (spinGroupSlice_nonempty (group k) (count k) (hcount k)) (eig k) (fun _ => 0) K hK (heig k)).1]
  linarith

end InvariantIsing

end

end OAI
