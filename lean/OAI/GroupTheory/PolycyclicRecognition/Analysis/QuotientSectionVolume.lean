import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuotientSectionHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHaarImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslatedBoxMass

namespace OAI

/-! # Volume bounds at arbitrary translated quotient locations

The admissible set only needs separate bounds on its ideal and quotient
coordinates. Its coordinates need not be independent or form a product.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Pointwise ENNReal

variable {N Q : Type*} [Group N] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup Q]
  [SecondCountableTopology Q]
  [MeasurableSpace N] [MeasurableSpace Q] [BorelSpace N] [BorelSpace Q]
  (π : N →* Q) (hπ : Continuous π) (s : C(Q, N)) (hs : ∀ q, π (s q) = q)
  (μQ : Measure Q) (μI : Measure π.ker) [SFinite μQ] [SFinite μI]

omit [IsTopologicalGroup Q] [SFinite μQ] in
/-- Separate coordinate restrictions bound the actual pushed-forward
measure by the measure of the containing product set. -/
theorem quotientSection_measure_le (E : Set N) (T : Set Q) (B : Set π.ker)
    (hE : ∀ n ∈ E, π n ∈ T ∧ quotientSectionResidual π s hs n ∈ B) :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) E ≤
      μQ T * μI B := by
  let e := quotientSectionHomeomorph π hπ s hs
  rw [e.symm.measurableEmbedding.map_apply]
  calc
    _ ≤ (μQ.prod μI) (T ×ˢ B) := by
      apply measure_mono
      intro p hp
      have hh := hE (e.symm p) hp
      change e (e.symm p) ∈ T ×ˢ B at hh
      simpa only [e.apply_symm_apply] using hh
    _ = _ := Measure.prod_prod T B

omit [SFinite μQ] in
/-- A left translate contributes no extra quotient volume, even if the
translated set is arbitrarily far from the identity. -/
theorem quotientSection_translated_measure_le [μQ.IsMulLeftInvariant]
    (E : Set N) (T : Set Q) (B : Set π.ker) (q₀ : Q) (α : Q ≃ Q)
    (J : ℝ≥0∞) (hα : μQ (α '' T) = J * μQ T)
    (hE : ∀ n ∈ E, π n ∈ q₀ • (α '' T) ∧ quotientSectionResidual π s hs n ∈ B) :
    (Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) E ≤
      J * μQ T * μI B := by
  have hh := quotientSection_measure_le π hπ s hs μQ μI E (q₀ • (α '' T)) B hE
  rwa [measure_smul, hα] at hh

omit [SFinite μQ] in
/-- The same bound in real Haar volume, with the exact exponential
multiplier. Finiteness is needed only to pass from extended real volume. -/
theorem quotientSection_translated_real_volume_le [μQ.IsMulLeftInvariant]
    (E : Set N) (T : Set Q) (B : Set π.ker) (q₀ : Q) (α : Q ≃ Q)
    (d : ℝ) (hα : μQ (α '' T) = ENNReal.ofReal (Real.exp d) * μQ T)
    (hT : μQ T ≠ ⊤) (hB : μI B ≠ ⊤)
    (hE : ∀ n ∈ E, π n ∈ q₀ • (α '' T) ∧ quotientSectionResidual π s hs n ∈ B) :
    ((Measure.map (quotientSectionHomeomorph π hπ s hs).symm (μQ.prod μI)) E).toReal ≤
      Real.exp d * (μQ T).toReal * (μI B).toReal := by
  have hh := quotientSection_translated_measure_le π hπ s hs μQ μI E T B q₀ α
    (ENNReal.ofReal (Real.exp d)) hα hE
  have hfinite : ENNReal.ofReal (Real.exp d) * μQ T * μI B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) hB
  have hr := ENNReal.toReal_mono hfinite hh
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg d)] using hr

end PolycyclicRecognition

end

end OAI
