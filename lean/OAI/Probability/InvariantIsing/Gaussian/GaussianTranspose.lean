import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternSingularMinimum

namespace OAI

/-! Transposition preserves the actual standard Gaussian array law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def gaussianPatternTranspose (N m : ℕ) :
    EuclideanSpace ℝ (Fin N × Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.prodComm (Fin N) (Fin m))

lemma gaussianPatternTranspose_apply {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) (i : Fin N) :
    gaussianPatternTranspose N m z (j,i) = z (i,j) := rfl

lemma gaussianPatternTranspose_array {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternArray (gaussianPatternTranspose N m z) = (gaussianPatternArray z)ᵀ := rfl

lemma gaussianPatternTranspose_hasLaw {N m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → EuclideanSpace ℝ (Fin N × Fin m)) (hZ : HasLaw Z (stdGaussian _) P) :
    HasLaw (fun ω => gaussianPatternTranspose N m (Z ω)) (stdGaussian _) P := by
  have hT : HasLaw (gaussianPatternTranspose N m)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin N)))
      (stdGaussian (EuclideanSpace ℝ (Fin N × Fin m))) :=
    ⟨(gaussianPatternTranspose N m).continuous.measurable.aemeasurable,
      stdGaussian_map (gaussianPatternTranspose N m)⟩
  exact hT.comp hZ

end InvariantIsing

end

end OAI
