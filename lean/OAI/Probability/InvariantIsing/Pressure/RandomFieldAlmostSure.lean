import OAI.Probability.InvariantIsing.Pressure.RandomOrbitAlmostSure

namespace OAI

/-! Almost-sure extension of Theorem7.1 to a joint conditional orbit law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_field_pressure_tendsto_ae
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d : (N : ℕ) → Ω → FieldSpectralData N) (Y : ℕ → Ω → ℝ)
    (hd : ∀ N, Measurable (d N)) (hY : ∀ N, Measurable (Y N))
    (H : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (H N)]
    [∀ N, (H N).IsMulRightInvariant]
    (hlaw : ∀ N, ConditionalFieldOrbitLaw P (d N) (Y N) (H N))
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      ∀ i, a-ε ≤ (d N ω).1 i ∧ (d N ω).1 i ≤ b+ε)
    (hweak : ∀ᵐ ω ∂P, Tendsto (fun k =>
      empiricalSpectralLaw (Nat.succ_pos k) (d (k+1) ω).1) atTop (𝓝 ν))
    (ξ : ProbabilityMeasure ℝ) (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (hw : ∀ᵐ ω ∂P, Tendsto (fun k => fieldWassersteinOne
      (empiricalSpectralLaw (Nat.succ_pos k) (d (k+1) ω).2) ξ) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun N => Y N ω) atTop
      (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) := by
  have hbounded : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop,
      spectralRadius ((d (k+1) ω).1) ≤ K := hno.mono fun ω hω =>
    spectralRadius_eventually_bounded_of_no_outliers (fun N => (d N ω).1) a b hω
  have ht := ae_random_orbit_pressure_sub_mean hhaar P d Y hd hY H hlaw hbounded
  filter_upwards [ht,hno,hweak,hw] with ω hω hn hweakω hwω
  have hm := general_mean_wasserstein_field_pressure_tendsto hhaar hgauss hpub H
    (fun N => (d N ω).1) ν a b hcompact hbound ha hb hn hweakω
    (fun N => (d N ω).2) ξ hξ hwω
  have hadd := hω.add (hm.comp (tendsto_add_atTop_nat 1))
  simp only [dataPhysicalPressure,Function.comp_apply,sub_add_cancel,zero_add] at hadd
  exact (tendsto_add_atTop_iff_nat 1).mp hadd

end InvariantIsing

end

end OAI
