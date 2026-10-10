import OAI.Analysis.IrrationalRotation.Model.TrimmedCircleSamplingGraph
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingGraph
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphRatioCaps
import OAI.Analysis.IrrationalRotation.Sampling.RationalGraphSampling

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleParameterData

theorem samplingDensity_false_eq_orbitGraphDensity (p : CircleParameterData)
    (θ : ℝ) (j n : ℕ) (x : Circle) :
    p.samplingDensity θ j n false x = p.orbitGraphDensity θ j n x := by
  simp only [samplingDensity, orbitGraphDensity, orientedKernel,
    Bool.false_eq_true, ↓reduceIte]

theorem samplingGraphAverage_ae_fst (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) {P : Circle → Prop}
    (hP : ∀ᵐ x ∂circleMeasure, P x) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r, P xy.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  rw [p.samplingGraphAverage_first_marginal θ j r hm]
  exact (withDensity_absolutelyContinuous _ _).ae_le hP

theorem trimmedSamplingGraphAverage_finite (p : CircleParameterData) (θ : ℝ)
    (A j r : ℕ) (hm : 0 < p.m j) :
    IsFiniteMeasure (p.trimmedSamplingGraphAverage θ A j r) := by
  have := p.samplingGraphAverage_finite θ j r hm
  unfold trimmedSamplingGraphAverage
  infer_instance

theorem trimmedSamplingGraphAverage_ae_good (p : CircleParameterData) (θ : ℝ)
    (A j r : ℕ) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      xy.1 ∈ p.rationalGraphGood A j :=
  ae_restrict_mem ((p.measurableSet_rationalGraphGood A j).preimage measurable_fst)

theorem trimmedSamplingGraphAverage_ae_density_graph (p : CircleParameterData)
    (θ : ℝ) (A j r : ℕ) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      ∃ n ∈ p.samples j r, 0 < p.orbitGraphDensity θ j n xy.1 ∧
        xy.2 = samplingTranslation θ n xy.1 := by
  have h := ae_restrict_of_ae (s := Prod.fst ⁻¹' p.rationalGraphGood A j)
    (p.samplingGraphAverage_ae_positive_density_graph θ j r)
  simpa only [trimmedSamplingGraphAverage, samplingDensity_false_eq_orbitGraphDensity] using h

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimmedSamplingGraphAverage_ae_ordered {A j r : ℕ}
    (hA : 1 ≤ A) (hj : 1 ≤ j) (hr : r < p.q (p.blockEnd (j - 1)))
    (ht : p.q A • ((p.shift j r : ℝ) : Circle) = 0) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      ∀ i, A ≤ i → p.coordinate i xy.1 ≤ p.coordinate i xy.2 := by
  filter_upwards [p.trimmedSamplingGraphAverage_ae_good θ A j r,
    p.trimmedSamplingGraphAverage_ae_density_graph θ A j r] with xy hg hd
  obtain ⟨n, hn, hpos, he⟩ := hd
  rw [he]
  exact hp.ordered_of_rationalGraphGood hA hj xy.1 hg (p.shift j r) ht
    (hp.samples_phase j hj r hr n hn).2
    (hp.samples_range j hj r hr n hn).2 hpos.ne'

theorem trimmedSamplingGraphAverage_ae_ratio_cap {A j r : ℕ}
    (hA : 1 ≤ A) (hj : 1 ≤ j) (hr : r < p.q (p.blockEnd (j - 1)))
    (ht : p.q A • ((p.shift j r : ℝ) : Circle) = 0) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      ∀ v : ℤ, p.floorCocycle θ v xy.2 / p.floorCocycle θ v xy.1 ≤
        Real.exp (p.rationalGraphPrefixCost A) := by
  obtain ⟨s, hs, hfull, hinv, hcap⟩ := hp.exists_uniform_rationalGraph_cap_set
  have hstart := ae_restrict_of_ae (s := Prod.fst ⁻¹' p.rationalGraphGood A j)
    (p.samplingGraphAverage_ae_fst θ j r (hp.m_pos j hj) hfull)
  filter_upwards [hstart, p.trimmedSamplingGraphAverage_ae_good θ A j r,
    p.trimmedSamplingGraphAverage_ae_density_graph θ A j r] with xy hx hg hd
  obtain ⟨n, hn, hpos, he⟩ := hd
  rw [he]
  exact hcap A j n hA hj xy.1 hx hg (p.shift j r) ht
    (hp.samples_phase j hj r hr n hn).2
    (hp.samples_range j hj r hr n hn).2 hpos.ne'

theorem trimmedSamplingGraphAverage_ae_positive_graph {A j r : ℕ}
    (hj : 1 ≤ j) (hr : r < p.q (p.blockEnd (j - 1))) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      ∃ n ∈ p.samples j r, 0 < n ∧ xy.2 = samplingTranslation θ n xy.1 := by
  exact ae_restrict_of_ae (hp.samplingGraphAverage_ae_positive_graph j hj r hr)

theorem trimmedSamplingGraphAverage_ae_rational {A j r : ℕ}
    (hA : 1 ≤ A) (hj : 1 ≤ j) (hAa : A ≤ p.blockEnd (j - 1))
    (hr : r < p.q A) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j
        (r * (p.q (p.blockEnd (j - 1)) / p.q A)),
      (∃ n ∈ p.samples j (r * (p.q (p.blockEnd (j - 1)) / p.q A)),
        0 < n ∧ xy.2 = samplingTranslation θ n xy.1) ∧
      (∀ i, A ≤ i → p.coordinate i xy.1 ≤ p.coordinate i xy.2) ∧
      ∀ v : ℤ, p.floorCocycle θ v xy.2 / p.floorCocycle θ v xy.1 ≤
        Real.exp (p.rationalGraphPrefixCost A) := by
  obtain ⟨hindex, hshift⟩ := hp.rational_sampling_index hAa hr
  have ht : p.q A • ((p.shift j (r * (p.q (p.blockEnd (j - 1)) / p.q A)) : ℝ) : Circle) = 0 := by
    rw [hshift]
    simpa only [Int.cast_natCast, natCast_zsmul] using
      CircleCharacterDynamics.zsmul_rational_eq_zero
        (q := (p.q A : ℤ)) (d := (p.q A : ℤ))
        (by exact_mod_cast (hp.q_pos A).ne') dvd_rfl (r : ℤ)
  exact (hp.trimmedSamplingGraphAverage_ae_positive_graph hj hindex).and
    ((hp.trimmedSamplingGraphAverage_ae_ordered hA hj hindex ht).and
      (hp.trimmedSamplingGraphAverage_ae_ratio_cap hA hj hindex ht))

end Invariant233.CircleParameterLaws

end

end OAI
