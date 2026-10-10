import OAI.Probability.InvariantIsing.Pressure.RandomOrbitAlmostSure
import OAI.Probability.InvariantIsing.Pressure.GeneralSpectralPressure

namespace OAI

/-! The almost-sure random-spectrum pressure theorem, under the conditional
orbit law in Proposition gen:random. No global integrability is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_pressure_tendsto_ae
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
    (hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ eig N ω i ∧ eig N ω i ≤ b+ε)
    (hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1) ω)) atTop (𝓝 ν)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  have hbounded : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop,
      spectralRadius (eig (k+1) ω) ≤ K := hno.mono fun ω hω =>
    spectralRadius_eventually_bounded_of_no_outliers (fun N => eig N ω) a b hω
  have ht := ae_random_orbit_pressure_sub_mean hhaar P
    (fun N ω => (eig N ω,fun _ => 0)) Y
    (fun N => (heig N).prodMk measurable_const) hY H hlaw hbounded
  filter_upwards [ht,hno,hweak] with ω hω hn hw
  have hm := general_spectral_mean_pressure_tendsto hhaar hgauss hpub H
    (fun N => eig N ω) ν a b hcompact hbound ha hb hn hw
  have hadd := hω.add (hm.comp (tendsto_add_atTop_nat 1))
  simp only [dataPhysicalPressure,Function.comp_apply,sub_add_cancel,zero_add] at hadd
  exact (tendsto_add_atTop_iff_nat 1).mp hadd

end InvariantIsing

end

end OAI
