import OAI.Probability.StrongRayleigh.FiniteDPPGenerating
import OAI.Probability.StrongRayleigh.MatrixStability

namespace OAI

universe u_1 u_2

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace Problem336AdditiveD139

theorem IsFiniteDeterminantalLaw.stronglyRayleighFinite_of_isHermitian
    {F : Type u_1} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    {K : F → F → ℂ} (hμ : IsFiniteDeterminantalLaw μ K)
    (hK : (Matrix.of K).IsHermitian) : StronglyRayleighFinite μ := by
  classical
  intro z hz
  rw [finiteGeneratingValue_eq_det μ K hμ z]
  have heq : ((1 : Matrix F F ℂ) + Matrix.of (fun i j => (z i - 1) * K i j)) =
      1 - Matrix.of K + Matrix.diagonal z * Matrix.of K := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.of_apply, Matrix.diagonal_mul]
    ring
  rw [heq]
  exact hermitian_pencil_det_ne_zero hK z hz

theorem IsFiniteDeterminantalLaw.stronglyRayleighFinite
    {F : Type u_2} [Fintype F] {μ : ProbabilityMeasure (F → Bool)}
    {K : F → F → ℂ} (hμ : IsFiniteDeterminantalLaw μ K)
    (hK : PositiveContractionFinite K) : StronglyRayleighFinite μ := by
  exact hμ.stronglyRayleighFinite_of_isHermitian hK.isHermitian

end Problem336AdditiveD139

end

end OAI
