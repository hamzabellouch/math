import OAI.Analysis.StructuralCrouzeix.Model
import OAI.Analysis.StructuralCrouzeix.SimilarityMinimum

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Matrix Topology ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Kronecker
namespace StructuralCrouzeix
open CompleteCrouzeix

lemma strictPositive_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {H : HermitianMatrix n} (hH : StrictPositive H) :
    (H : Matrix n n ℂ).PosDef := by
  obtain ⟨ε, hε, hle⟩ := hH
  have hp : ((H : Matrix n n ℂ) - ε • 1).PosSemidef := hle
  have hh := (Matrix.PosDef.one.smul hε).add_posSemidef hp
  simpa only [add_sub_cancel] using hh

lemma strictlyFeasible_of_stable {n : ℕ} [Nonempty (Fin n)]
    {T : Matrix (Fin n) (Fin n) ℂ} (hT : spectralRadius ℂ T < 1) :
    StrictlyFeasible T := by
  obtain ⟨τ,H,hlo,hhi,hstein⟩ := exists_strict_metric hT
  refine ⟨τ,H,H.property,strictPositive_posDef hlo,?_,?_⟩
  · simpa only [Algebra.algebraMap_eq_smul_one, AddSubgroup.coe_sub,
      selfAdjoint.val_smul, selfAdjoint.val_one] using strictPositive_posDef hhi
  · exact strictPositive_posDef hstein

lemma minimizing_posDef {n : ℕ} [Nonempty (Fin n)]
    {T H : Matrix (Fin n) (Fin n) ℂ} {τ : ℝ}
    (h : IsMinimizing T τ H) : H.PosDef := by
  have hp := (h.1.1 : (H-1).PosSemidef)
  have hh := Matrix.PosDef.one.add_posSemidef hp
  simpa only [add_sub_cancel] using hh

lemma minimizing_sqrt_le_two (D : AdmissibleDomain)
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain)
    {τ : ℝ} {H : Matrix (Fin n) (Fin n) ℂ}
    (h : IsMinimizing (matrixAnalyticEval A D.interior.toDisk) τ H) :
    Real.sqrt τ ≤ 2 := by
  obtain ⟨R,hR,hr,hc⟩ := D.exists_two_similarity A hW
  exact (optimal_metric_sqrt_le_similarity h.1 h.2 hR
    ((matrix_contractivity_iff _).mp hc)).trans hr

theorem optimal_metric_bundle (D : AdmissibleDomain)
    {n : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
    (hW : numericalRange A ⊆ D.domain) :
    let T := matrixAnalyticEval A D.interior.toDisk
    StrictlyFeasible T ∧
    ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ 2 ∧
      (∃ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H) ∧
      ∀ H : Matrix (Fin n) (Fin n) ℂ, IsMinimizing T (κ^2) H →
        let S := CFC.sqrt H
        let A' := S*A*S⁻¹
        let B := S*T*S⁻¹
        H.PosDef ∧ IsUnit S ∧
        B = matrixAnalyticEval A' D.interior.toDisk ∧
        Bᴴ*B ≤ 1 ∧ spectralRadius ℂ B < 1 ∧
        ‖S‖*‖S⁻¹‖ = κ ∧
        (∀ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R →
          (R*T*R⁻¹)ᴴ*(R*T*R⁻¹) ≤ 1 → κ ≤ ‖R‖*‖R⁻¹‖) := by
  let T := matrixAnalyticEval A D.interior.toDisk
  have hA : spectrum ℂ A ⊆ D.domain := (spectrum_subset_numericalRange A).trans hW
  have hT : spectralRadius ℂ T < 1 := D.coordinate_stable A hA
  refine ⟨strictlyFeasible_of_stable hT, ?_⟩
  obtain ⟨τ,H₀,hf,hp,hm⟩ := exists_optimal_metric hT
  have ht : 0 ≤ τ := zero_le_one.trans hf.one_le
  have hsq : (Real.sqrt τ)^2 = τ := Real.sq_sqrt ht
  have hk : 1 ≤ Real.sqrt τ := by
    have hh := Real.sqrt_le_sqrt hf.one_le
    simpa only [Real.sqrt_one] using hh
  refine ⟨Real.sqrt τ,hk,minimizing_sqrt_le_two D A hW ⟨hf,hm⟩,?_,?_⟩
  · exact ⟨H₀,by simpa only [hsq] using (show IsMinimizing T τ H₀ from ⟨hf,hm⟩)⟩
  intro H hH
  have hH' : IsMinimizing T τ H := by simpa only [hsq] using hH
  have hpos := minimizing_posDef hH'
  have hu := metric_sqrt_isUnit hpos
  refine ⟨hpos,hu,?_,?_,?_,?_,?_⟩
  · exact (matrixAnalyticEval_similarity hu A D.interior.toDisk).symm
  · exact (matrix_contractivity_iff _).mpr (metric_similarity_contraction hH'.1 hpos)
  · simpa only [spectralRadius_eq_of_unital,spectrum_matrix_similarity hu] using hT
  · exact optimal_metric_condition_eq_from_minimality hH'.1 hpos hH'.2
  · intro R hR hc
    exact optimal_metric_sqrt_le_similarity hH'.1 hH'.2 hR
      ((matrix_contractivity_iff _).mp hc)

end StructuralCrouzeix
end

end OAI
