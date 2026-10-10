import OAI.Geometry.Relativity.CKS.CKSFoliationJet
import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def leadingD (j : MassInput) : ScalarJet :=
  (-3/4:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (j.1 0))) (lowerMatrixJet (j.1 1))
def leadingT (j : MassInput) : ScalarJet :=
  (1/2:ℝ) • traceProductJet (inverseMatrixJet (lowerMatrixJet (j.1 0))) (j.2.1 1-lowerMatrixJet (j.1 1))
def leadingLapse (j : MassInput) : ScalarJet := (-1/2:ℝ) • j.2.2.2 0
def leadingU (j : MassInput) : ScalarJet := leadingD j+leadingLapse j

lemma coefficientD_zero (j : MassInput) : coefficientD 0 j = leadingD j := by
  simp only [coefficientD,coefficientMetric_zero,Prod.fst_zero,mulMatrixJet_zero,add_zero,
    leadingD]
  erw [traceProductJet_smul]
  rw [smul_smul]
  congr 1
  ring
lemma coefficientT_zero (j : MassInput) : coefficientT 0 j = leadingT j := by
  simp only [coefficientT,coefficientMetric_zero,Prod.fst_zero,mulMatrixJet_zero,add_zero,leadingT]
lemma coefficientV_zero (j : MassInput) : coefficientV 0 j = j.2.2.2 0 := by
  simp only [coefficientV,Prod.fst_zero,powJet_zero_succ,productJet_zero_left,add_zero,sub_zero]
lemma sqrtJet_one : sqrtJet (constantJet 1) = constantJet 1 := by
  ext a b <;> simp [sqrtJet,constantJet]
lemma reciprocalJet_constant (c : ℝ) : reciprocalJet (constantJet c) = constantJet (1/c) := by
  ext a b <;> simp [reciprocalJet,constantJet]
lemma lapseCorrection_zero (j : MassInput) : lapseCorrection (0,j) = leadingLapse j := by
  have hden : foliationDen (0,j) = constantJet 1 := by
    simp [foliationDen]
  unfold lapseCorrection
  rw [coefficientV_zero,hden,sqrtJet_one,← constantJet_add,productJet_constant_left,
    ← constantJet_smul,reciprocalJet_constant,productJet_constant_right]
  unfold leadingLapse
  module
lemma uCorrection_zero (j : MassInput) : uCorrection (0,j) = leadingU j := by
  simp only [uCorrection,Prod.fst_zero,powJet_zero_succ,productJet_zero_left,add_zero,
    coefficientD_zero,lapseCorrection_zero,leadingU]

lemma foliation_uniform_lipschitz {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, LipschitzOnWith C foliationCoefficients
      (Metric.cthickening δ ((fun j : MassInput => ((0:ScalarThreeJet),j)) '' K)) := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace MassParameter := FiniteDimensional.proper ℝ MassParameter
  let K₀ : Set MassParameter := (fun j : MassInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hs : K₀ ⊆ foliationRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact foliationRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδs⟩ := hK₀.exists_cthickening_subset_open foliationRegion_open hs
  have hl : LocallyLipschitzOn foliationRegion foliationCoefficients := by
    intro p hp
    have hd := (foliationCoefficients_smooth hp).of_le (by simp : (1:ℕ∞ω) ≤ ∞)
    obtain ⟨C,u,hu,hC⟩ := hd.exists_lipschitzOnWith
    exact ⟨C,u,mem_nhdsWithin_of_mem_nhds hu,hC⟩
  exact ⟨δ,hδ,(hl.mono hδs).exists_lipschitzOnWith_of_compact (hK₀.cthickening (r := δ))⟩

attribute [local irreducible] coefficientD coefficientT coefficientShift lapseCorrection uCorrection

theorem cks_foliation_leading_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ∀ z : ScalarThreeJet, ∀ j : MassInput, R₀ ≤ r → ‖z‖ ≤ 1/r →
      j.1 0 ∈ K → ‖j‖ ≤ B →
      ‖coefficientD z j-leadingD j‖ ≤ C/r ∧
      ‖coefficientT z j-leadingT j‖ ≤ C/r ∧
      ‖lapseCorrection (z,j)-leadingLapse j‖ ≤ C/r ∧
      ‖uCorrection (z,j)-leadingU j‖ ≤ C/r := by
  obtain ⟨δ,hδ,C,hC⟩ := foliation_uniform_lipschitz (boundedMassFamily_compact hK B)
    (fun j hj => hreg _ hj.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,C.coe_nonneg,?_⟩
  intro r z j hr hz hj hB
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  have hh := parameter_lipschitz_zero_estimate hC (boundedMassFamily_mem hj hB) (hz.trans hd)
  have hbound : (C:ℝ)*‖z‖ ≤ C/r := by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hz C.coe_nonneg
  have ht := hh.trans hbound
  simp only [foliationCoefficients,Prod.mk_sub_mk,coefficientD_zero,coefficientT_zero,
    lapseCorrection_zero,uCorrection_zero] at ht
  obtain ⟨hD,hrest⟩ := norm_prod_le_iff.mp ht
  obtain ⟨hT,hrest⟩ := norm_prod_le_iff.mp hrest
  obtain ⟨_,hrest⟩ := norm_prod_le_iff.mp hrest
  obtain ⟨hL,hU⟩ := norm_prod_le_iff.mp hrest
  exact ⟨hD,hT,hL,hU⟩

end
end CKSMixedGeometry

end

end OAI
