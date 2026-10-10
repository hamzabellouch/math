import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal

theorem centeredNormalizedNative_detection
    {C Ω T Y X : Type*} [MeasurableSpace C] [Fintype Ω] [Fintype T]
    [Fintype Y] [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    {Tests : Ω → Type*} (physical : Ω → T → Y)
    (slices : ∀ z, Tests z → Finset T) (tests : ∀ z, Tests z → T → ℂ)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Y → X → ℤ) (w : X → ℕ) (degree : ℕ) (budget : ℝ)
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (r : FiniteProbabilityWeights Y) (f : Y → ℂ) {α β : ℝ} (hα : 0 < α)
    (hdetect : ∀ center,
      α / 2 ≤ sampledSliceSeminorm (law center) physical slices tests f →
      ∃ (c : ∀ j, J j → ℝ) (Q : Y → ℂ),
        Q ∈ twistedNativeSampleFunctions w degree budget sample
          (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
            W.eval N (fun j => subtractConstant (c j) (poly j)) (sample t)) ∧
        β ≤ ‖r.correlation f Q‖)
    (hlarge : α ≤ sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
      physical slices tests f) :
    ∃ Q ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        W.eval N poly (sample t)), β ≤ ‖r.correlation f Q‖ := by
  obtain ⟨center, hcenter⟩ := exists_center_of_sampledSliceSeminorm μ law hweight
    physical slices tests f hα hlarge
  obtain ⟨c, Q, hQ, hcorr⟩ := hdetect center hcenter
  exact ⟨Q, twistedNativeSampleFunctions_subtractConstant_subset N poly c sample w degree budget hQ,
    hcorr⟩

end Erdos3.VectorPolynomial

end

end OAI
