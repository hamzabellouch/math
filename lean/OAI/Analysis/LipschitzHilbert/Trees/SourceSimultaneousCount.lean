import OAI.Analysis.LipschitzHilbert.Estimates.SimultaneousCountPowers
import OAI.Analysis.LipschitzHilbert.Trees.SourceCountParameters

namespace OAI

/-! The simultaneous-count proposition for the manuscript's actual scales. -/

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

/-- The lower threshold for `L` is independent of the finite top family.
The dyadic branching parameter, enlarged width, and short-time cutoff are
the original manuscript choices. No extra counting or transfer estimate
is assumed. -/
theorem eventually_source_simultaneous_count_universal (Lip : ℝ≥0)
    (a k p t c c0 J : ℝ) (ha : 0 ≤ a) (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p)
    (ht : 2 * a + p + 1 ≤ t) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (u : ℝ × ℝ → ℝ), LipschitzWith Lip u →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], ∀ m tau : ℝ,
      Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
      m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      ∀ (T : ι → SlopeBox) (d : ι → ℝ) (E : ι → Set (ℝ × ℝ)),
        (∀ i, (T i).length ≤ tau) →
        (∀ i, MeasurableSet (E i)) →
        (∀ i, (volume.prod volume) (E i) ≠ ∞) →
        (∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a) →
        (∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i)) →
        (∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i) →
        (∀ i, 0 ≤ d i) → (∀ i, (T i).width = m * (T i).length * d i) →
        ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
          (volume.prod volume).real bad ≤
            (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
          ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
            (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
            (∀ i ∈ I, d i ≤ rho / SourceParameters.branching L ^ 2) →
            (∀ i ∈ I, ∀ j ∈ I,
              |(T i).slope - (T j).slope| ≤ SourceParameters.branching L * rho) →
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
            (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  filter_upwards [eventually_ge_atTop (15 : ℝ),
    eventually_ge_atTop (240 * (1 + c) * (|Real.log 768| + |2 * p| + J)),
    SourceParameters.eventually_count_parameters p c Lip Lip.coe_nonneg]
    with L hL hlarge hparameters
  intro u hu ι _ _ m tau hml hmu hta htau T d E hlength hE hfinite hbox harea hwitness hd hwidth
  obtain ⟨hB, hM, hcM, hMB, hscales⟩ := hparameters
  obtain ⟨hm, hsmall⟩ := hscales m tau hml hmu hta htau
  exact simultaneous_separated_count_powers T u hu hL ha hap hkp ht hlarge hM hc0 hc hcM
    hB hMB hm d E hE hfinite hbox harea hwitness hd hwidth
    (fun i => hsmall (T i).length (T i).length_pos.le (hlength i))

theorem eventually_source_simultaneous_count_uniform
    (u : ℝ × ℝ → ℝ) {Lip : ℝ≥0} (hu : LipschitzWith Lip u)
    (a k p t c c0 J : ℝ) (ha : 0 ≤ a) (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p)
    (ht : 2 * a + p + 1 ≤ t) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], ∀ m tau : ℝ,
      Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
      m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      ∀ (T : ι → SlopeBox) (d : ι → ℝ) (E : ι → Set (ℝ × ℝ)),
        (∀ i, (T i).length ≤ tau) →
        (∀ i, MeasurableSet (E i)) →
        (∀ i, (volume.prod volume) (E i) ≠ ∞) →
        (∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a) →
        (∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i)) →
        (∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i) →
        (∀ i, 0 ≤ d i) → (∀ i, (T i).width = m * (T i).length * d i) →
        ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
          (volume.prod volume).real bad ≤
            (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
          ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
            (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
            (∀ i ∈ I, d i ≤ rho / SourceParameters.branching L ^ 2) →
            (∀ i ∈ I, ∀ j ∈ I,
              |(T i).slope - (T j).slope| ≤ SourceParameters.branching L * rho) →
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
            (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  filter_upwards [eventually_source_simultaneous_count_universal Lip a k p t c c0 J
    ha hap hkp ht hc0 hc] with L hL
  exact hL u hu

theorem eventually_source_simultaneous_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ℝ × ℝ → ℝ) {Lip : ℝ≥0} (hu : LipschitzWith Lip u)
    (a k p t c c0 J : ℝ) (ha : 0 ≤ a) (hap : a + 1 ≤ p) (hkp : k + 1 ≤ p)
    (ht : 2 * a + p + 1 ≤ t) (hc0 : 0 ≤ c0) (hc : 4 * (c0 + 1) + 1 ≤ c) :
    ∀ᶠ L : ℝ in atTop, ∀ m tau : ℝ,
      Real.exp (L ^ (9 / 10 : ℝ)) ≤ m →
      m ≤ 2 * Real.exp (L ^ (9 / 10 : ℝ)) →
      0 ≤ tau → tau ≤ Real.exp (-(L ^ (97 / 100 : ℝ))) →
      ∀ (T : ι → SlopeBox) (d : ι → ℝ) (E : ι → Set (ℝ × ℝ)),
        (∀ i, (T i).length ≤ tau) →
        (∀ i, MeasurableSet (E i)) →
        (∀ i, (volume.prod volume) (E i) ≠ ∞) →
        (∀ i, ∀ w ∈ E i, (T i).radius w ≤ L ^ a) →
        (∀ i, L ^ (-a) * (T i).length * (T i).width ≤ (volume.prod volume).real (E i)) →
        (∀ i, ∀ w ∈ E i, |u w - (T i).slope| ≤ c0 * d i) →
        (∀ i, 0 ≤ d i) → (∀ i, (T i).width = m * (T i).length * d i) →
        ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ (volume.prod volume) bad ≠ ∞ ∧
          (volume.prod volume).real bad ≤
            (∑ i, (T i).length * (T i).width) * Real.exp (-J * L) ∧
          ∀ z ∉ bad, ∀ rho : ℝ, 0 < rho → ∀ I : Finset ι,
            (∀ i ∈ I, (T i).radius z ≤ L ^ k) →
            (∀ i ∈ I, d i ≤ rho / SourceParameters.branching L ^ 2) →
            (∀ i ∈ I, ∀ j ∈ I,
              |(T i).slope - (T j).slope| ≤ SourceParameters.branching L * rho) →
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
            (I.card : ℝ) ≤ L ^ (t + 4) / 100 := by
  filter_upwards [eventually_source_simultaneous_count_uniform u hu a k p t c c0 J
    ha hap hkp ht hc0 hc] with L hL
  exact hL ι

end LipschitzHilbert

end

end OAI
