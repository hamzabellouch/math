import Mathlib
import OAI.Analysis.Conductivity.Sobolev.VoltageH1Completion

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology TopologicalSpace Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma uniform_matrix_laminate_coverage {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    (A : Symmetric3)
    (hA : ∀ v : Coord3, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A.val *ᵥ v) ∧
      v ⬝ᵥ (A.val *ᵥ v) ≤ C * (v ⬝ᵥ v)) :
    A ∈ matrixFiniteLaminate (laminateLower c C) (laminateUpper C) := by
  obtain ⟨Q,hQ,α,he⟩ := exists_orthogonal_diagonalization A.property
  refine ⟨Q,hQ,α,(uniform_laminate_coverage hc hcC).2.2 α ?_,he⟩
  intro i
  let v : Coord3 := Pi.single i 1
  have hnorm : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = 1 := by
    rw [orthogonal_dotProduct hQ]
    simp [v,dotProduct,Pi.single_apply]
  have hback : Qᵀ *ᵥ (Q *ᵥ v) = v := by
    rw [mulVec_mulVec,hQ.1,one_mulVec]
  have hval : (Q *ᵥ v) ⬝ᵥ (A.val *ᵥ (Q *ᵥ v)) = α i := by
    rw [he,conjugateDiagonal_quadratic,hback]
    simp [v,Pi.single_apply]
  simpa only [hnorm,hval,mul_one] using hA (Q *ᵥ v)

theorem finite_field_scalarization
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    [SeparableSpace (Lp FieldVector 2 (μ.restrict U))]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hu : MemLp u 2 (μ.restrict U))
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (huH1 : (hu.toLp _,hE.toLp _) ∈ voltageH1Jets μ U)
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hbound : ∀ᵐ x ∂μ, x ∈ U → ∀ v : Coord3,
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((A x).val *ᵥ v) ∧
      v ⬝ᵥ ((A x).val *ᵥ v) ≤ C * (v ⬝ᵥ v)) :
    ∃ (z : voltageH1Jets μ U) (F : Lp FieldVector 2 (μ.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (μ.restrict U) ∧
      z.val-(hu.toLp _,hE.toLp _) ∈ zeroVoltageJets μ U ∧
      (∀ᵐ x ∂μ.restrict U, s x ∈ Icc (laminateLower c C) (laminateUpper C) ∧
        F x = s x • (z.val.2 x)) ∧
      (∀ W : voltageH1Jets μ U, inner ℝ W.val.2 F = inner ℝ W.val.2 (hF.toLp _)) ∧
      (∀ W : zeroVoltageJets μ U, inner ℝ W.val.2 F = 0) := by
  apply exact_scalarization_H1 μ (uniform_laminate_coverage hc hcC).1
    (uniform_laminate_coverage hc hcC).2.1 hUb hUm u A hAm hu hE hF huH1 hint hdiv hreg
  filter_upwards [hbound] with x hx hxU
  exact uniform_matrix_laminate_coverage hc hcC (A x) (hx hxU)

end ScalarConductivity

end
end

end OAI
