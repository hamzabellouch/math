import OAI.Probability.InvariantIsing.Pressure.RandomPressureBound

namespace OAI

/-! The complete in-probability, L1 and expectation clauses of Proposition gen:random. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_pressure_limit
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (eig : (N : ℕ) → Ω → Fin N → ℝ) (Y : ℕ → Ω → ℝ)
    (heig : ∀ N, Measurable (eig N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (fun ω => (eig N ω,fun _ => 0)) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hweak : TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω))) atTop
      (fun _ => LevyProkhorov.ofMeasure ν))
    (hexcess : TendstoInMeasure P (fun k ω => spectralExcess (eig (k+1) ω) a b)
      atTop (fun _ => 0))
    (hUI : UniformIntegrable (fun k => Y (k+1)) 1 P) :
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) ∧
    Tendsto (fun k => eLpNorm (fun ω => Y (k+1) ω-
      (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) 1 P) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ ω, Y (k+1) ω ∂P) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hp := random_pressure_tendsto_in_measure hhaar hgauss hpub P eig Y heig hY H hlaw
    ν a b hcompact hbound ha hb hweak hexcess
  exact ⟨hp,pressure_L1_of_probability_and_uniformIntegrability P _ _ hUI hp⟩

end InvariantIsing

end

end OAI
