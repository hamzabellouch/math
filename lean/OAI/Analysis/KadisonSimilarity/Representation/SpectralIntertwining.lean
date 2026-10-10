import OAI.Analysis.KadisonSimilarity.Derivation.CyclicSpectralIsometry
import OAI.Analysis.KadisonSimilarity.Representation.SpectralDensityIsometry
import OAI.Analysis.KadisonSimilarity.Representation.ContinuousL2Multiplication

namespace OAI

/-! Both spectral coordinate maps intertwine the continuous scalar action.
The identities are proved first on continuous functions and extended by density. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

namespace VectorSpectralMeasure
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)

theorem cyclicMap_intertwines (f : C(X, ℂ)) (ξ : Lp ℂ 2 (measure Φ v)) :
    cyclicMap Φ v (continuousL2Mul (measure Φ v) f ξ) = Φ f (cyclicMap Φ v ξ) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
    (μ := measure Φ v) (𝕜 := ℂ) (by norm_num)).induction
      (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) ξ
  obtain ⟨g, rfl⟩ := hy
  rw [continuousL2Mul_toLp, cyclicMap_toLp, cyclicMap_toLp, map_mul]
  rfl

end VectorSpectralMeasure

variable (μ : Measure X) (u : X → ℝ≥0) (hu : Measurable u)
  (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

omit [T2Space X] in
theorem weightedContinuousVector_mul (f g : C(X, ℂ)) :
    continuousL2Mul μ f (weightedContinuousVector μ u hu hL2 g) =
      weightedContinuousVector μ u hu hL2 (f * g) := by
  apply Lp.ext
  filter_upwards [continuousL2Mul_ae μ f (weightedContinuousVector μ u hu hL2 g),
    weightedContinuousVector_ae μ u hu hL2 g,
    weightedContinuousVector_ae μ u hu hL2 (f * g)] with x hm hg hfg
  rw [hm, hg, hfg, ContinuousMap.mul_apply]
  ring

variable [IsFiniteMeasure (squaredDensityMeasure μ u)]
  [(squaredDensityMeasure μ u).WeaklyRegular]

theorem spectralDensityIsometry_intertwines (f : C(X, ℂ))
    (ξ : Lp ℂ 2 (squaredDensityMeasure μ u)) :
    spectralDensityIsometry μ u hu hL2
      (continuousL2Mul (squaredDensityMeasure μ u) f ξ) =
        continuousL2Mul μ f (spectralDensityIsometry μ u hu hL2 ξ) := by
  refine (ContinuousMap.toLp_denseRange (E := ℂ) (p := 2)
    (μ := squaredDensityMeasure μ u) (𝕜 := ℂ) (by norm_num)).induction
      (fun y hy => ?_) (isClosed_eq (by fun_prop) (by fun_prop)) ξ
  obtain ⟨g, rfl⟩ := hy
  rw [continuousL2Mul_toLp, spectralDensityIsometry_toLp, spectralDensityIsometry_toLp,
    weightedContinuousVector_mul]

end KadisonSimilarity

end

end OAI
