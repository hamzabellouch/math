import OAI.Probability.InvariantIsing.Spectral.SelectedSpectralPressure
import OAI.Probability.InvariantIsing.Spectral.SelectedOrbitAlmostSure
import OAI.Probability.InvariantIsing.Spectral.SelectedSpectralExcess
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace OAI

/-! Proposition gen:random: convergence in probability from weak empirical
convergence and vanishing edge excess, with no independence across dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology
namespace InvariantIsing

theorem random_pressure_tendsto_in_measure
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
      atTop (fun _ => 0)) :
    TendstoInMeasure P (fun k => Y (k+1)) atTop
      (fun _ => (variationalFunctional (measureR (ν : Measure ℝ) b)).toReal) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun k => (hY (k+1)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨u,hu,hwu⟩ := (hweak.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨v,hv,hev⟩ := (hexcess.comp (hns.comp hu).tendsto_atTop).exists_seq_tendsto_ae
  let s := ns ∘ u ∘ v
  have hs : StrictMono s := hns.comp (hu.comp hv)
  have hws : ∀ᵐ ω ∂P, Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos (s k))
      (eig (s k+1) ω)) atTop (𝓝 ν) := by
    filter_upwards [hwu] with ω hω
    exact (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp
      (hω.comp hv.tendsto_atTop)
  have hbs : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ᶠ k in atTop, spectralRadius (eig (s k+1) ω) ≤ K := by
    filter_upwards [hev] with ω hω
    exact selected_spectralRadius_bounded s (fun k => eig (s k+1) ω) a b hω
  have ht := ae_selected_orbit_pressure_sub_mean hhaar P s hs.id_le
    (fun k ω => (eig (s k+1) ω,fun _ => 0)) (fun k => Y (s k+1))
    (fun k => (heig (s k+1)).prodMk measurable_const) (fun k => hY (s k+1)) H
    (fun k => hlaw (s k+1)) hbs
  refine ⟨u ∘ v,hu.comp hv,?_⟩
  filter_upwards [ht,hws,hev] with ω htω hwω heω
  have hm := selected_spectral_pressure_tendsto hhaar hgauss hpub H
    (fun k => s k+1) (fun k => Nat.succ_pos _) ((tendsto_add_atTop_nat 1).comp hs.tendsto_atTop)
    (fun k => eig (s k+1) ω) ν a b hcompact hbound ha hb
    (selected_no_outliers_of_excess (fun k => s k+1) (fun k => eig (s k+1) ω) a b heω) hwω
  have hh := htω.add hm
  simpa only [s,Function.comp_apply,dataPhysicalPressure,sub_add_cancel,zero_add] using hh

end InvariantIsing

end

end OAI
