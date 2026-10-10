import OAI.Analysis.OperatorAlgebra.UnitaryMeanProperties
import OAI.Analysis.OperatorAlgebra.FiniteHilbertCompression
import OAI.Analysis.Nuclearity.MatrixCPMapExtension

namespace OAI

/-! The concrete unitary-orbit average is unital and completely positive,
and hence contractive. -/

noncomputable section
open Filter
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private lemma orbitMatrix_inner {n : ℕ}
    (M : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : Fin n => H)) :
    inner ℂ (matrixOperator M x) x = ∑ j, ∑ k, inner ℂ (M j k (x k)) (x j) := by
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner]

lemma unitaryOrbitMeanCLM_cp (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x)) :
    CompletelyPositive (unitaryOrbitMeanCLM ω U hU) := by
  intro n M hM
  apply (NonUnitalStarAlgHom.map_le_map_iff
    (matrixOperatorHom (n := Fin n) (H := H)) matrixOperator_injective).mp
  rw [map_zero]
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  let f (j k : Fin n) := unitaryOrbitCoefficient U hU (M j k) (x k) (x j)
  have hsum : complexSymmetricMean ω (∑ j, ∑ k, f j k) =
      ∑ j, ∑ k, complexSymmetricMean ω (f j k) := by
    change complexSymmetricMeanCLM ω (∑ j, ∑ k, f j k) = _
    simp only [map_sum]
    rfl
  have hn : 0 ≤ inner ℂ (matrixOperator (matrixLinearMap (unitaryOrbitMeanCLM ω U hU) M) x) x := by
    rw [orbitMatrix_inner]
    simp only [matrixLinearMap_apply]
    change 0 ≤ ∑ j, ∑ k, inner ℂ (unitaryOrbitMean ω U hU (M j k) (x k)) (x j)
    simp_rw [unitaryOrbitMean_inner]
    change 0 ≤ ∑ j, ∑ k, complexSymmetricMean ω (f j k)
    rw [← hsum]
    apply complexSymmetricMean_nonneg ω hω
    intro t
    let y : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 (fun k => U t (x k))
    have hp : 0 ≤ matrixOperator M := map_nonneg (matrixOperatorHom (n := Fin n) (H := H)) hM
    have hy := (ContinuousLinearMap.nonneg_iff_isPositive.mp hp).inner_nonneg_left y
    rw [orbitMatrix_inner] at hy
    simpa only [BoundedContinuousFunction.sum_apply, f, unitaryOrbitCoefficient_apply,
      y] using hy
  exact ⟨Complex.ext rfl hn.2, hn.1⟩

lemma unitaryOrbitMeanCLM_one (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x)) :
    unitaryOrbitMeanCLM ω U hU 1 = 1 :=
  unitaryOrbitMean_fix ω hω U hU 1 (fun _ _ => rfl)

lemma unitaryOrbitMeanCLM_norm_le (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (U : ℝ → H ≃ₗᵢ[ℂ] H) (hU : ∀ x, Continuous (fun t => U t x)) :
    ‖unitaryOrbitMeanCLM ω U hU‖ ≤ 1 := by
  apply cp_norm_le_one_of_one _ (unitaryOrbitMeanCLM_cp ω hω U hU)
  rw [unitaryOrbitMeanCLM_one ω hω U hU]
  exact ContinuousLinearMap.norm_id_le

end WeakPureInfiniteness

end

end OAI
