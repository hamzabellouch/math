import OAI.NumberTheory.DukePrimeDegree.Entropy.EntropyUpper

namespace OAI

/-!
# Subexponential name covers and zero entropy

The criterion concerns the finite-observation definition of metric entropy. Its hypotheses ask for
high-mass collections of orbit names, not for an entropy inequality.
-/

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology Classical

namespace DukePrimeDegree

open PrimeDegreePackets

/-- Subexponentially many names covering arbitrarily high mass give
zero entropy rate for an observation. -/
theorem observationEntropyRate_le_zero_of_good_names {Y α : Type*}
    [MeasurableSpace Y] [Fintype α] [DecidableEq α]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ) (P : Y → α)
    (hP : ∀ a, MeasurableSet {y | P y = a})
    (hcover : ∀ ε : ℝ, 0 < ε →
      ∃ G : ∀ N : ℕ, Finset (Fin N → α),
        (∀ᶠ N : ℕ in atTop, (G N).Nonempty) ∧
        (∀ᶠ N : ℕ in atTop,
          (∑ w, if w ∈ G N then 0 else μ.real {y | orbitName T P N y = w}) ≤ ε) ∧
        (∀ᶠ N : ℕ in atTop, Real.log (G N).card ≤ ε * N)) :
    observationEntropyRate μ T P ≤ 0 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hden : 0 < 1 + Real.log (Fintype.card α : ℝ) := by
    linarith [Real.log_natCast_nonneg (Fintype.card α)]
  let ε := δ / (1 + Real.log (Fintype.card α : ℝ))
  have hε : 0 < ε := div_pos hδ hden
  obtain ⟨G, hne, hbad, hcard⟩ := hcover ε hε
  have h := observationEntropyRate_le_of_good_names μ hT P hP G hne hbad hcard
  have hid : ε + ε * Real.log (Fintype.card α) = δ := by
    calc
      ε + ε * Real.log (Fintype.card α) =
          ε * (1 + Real.log (Fintype.card α)) := by ring
      _ = δ := div_mul_cancel₀ _ (ne_of_gt hden)
  simpa only [zero_add, hid] using h

/-- If every finite observation admits subexponential high-mass name
covers, the metric entropy is zero. -/
theorem measureEntropy_eq_zero_of_good_names {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] {T : Y → Y}
    (hT : MeasurePreserving T μ μ)
    (hcover : ∀ (k : ℕ) (P : Y → Fin k)
      (_hP : ∀ a, MeasurableSet {y | P y = a}) (ε : ℝ), 0 < ε →
      ∃ G : ∀ N : ℕ, Finset (Fin N → Fin k),
        (∀ᶠ N : ℕ in atTop, (G N).Nonempty) ∧
        (∀ᶠ N : ℕ in atTop,
          (∑ w, if w ∈ G N then 0 else μ.real {y | orbitName T P N y = w}) ≤ ε) ∧
        (∀ᶠ N : ℕ in atTop, Real.log (G N).card ≤ ε * N)) :
    measureEntropy μ T = 0 := by
  apply le_antisymm _ bot_le
  simp only [measureEntropy, iSup_le_iff]
  intro k P hP
  exact ENNReal.ofReal_eq_zero.mpr
    (observationEntropyRate_le_zero_of_good_names μ hT P hP (hcover k P hP)) |>.le

end DukePrimeDegree

end OAI
