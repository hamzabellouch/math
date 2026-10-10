import Mathlib
import OAI.Geometry.Borsuk.Projectors.NegativeQuadratic
import OAI.Geometry.Borsuk.Support.FacetTangent

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section LocalModel
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [DecidableEq ι] in
lemma Admissible.signedExtension_kernel_coordinate {f : E → ι → ℝ} (hf : Admissible f)
    {A : M} (hA : IsSelfAdjoint A) {c : E} (hc : ‖c‖ = 1) (hAc : op A c = 0)
    {i : ι} (hi : 0 < f c i) : signedExtension f A i = 0 := by
  obtain ⟨hp,hn⟩ := matrix_parts_kernel hA hAc
  simp only [signedExtension,Pi.sub_apply,
    hf.positiveExtension_kernel (CFC.posPart_nonneg A) hc hp hi,
    hf.positiveExtension_kernel (CFC.negPart_nonneg A) hc hn hi,sub_self]

noncomputable def localBlockModel (f : E → ι → ℝ) (c : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) (A : M) : ι → ℝ :=
  blockScalar c A • f c + facetTangent a (D (blockOff c e A)) + signedExtension f (blockCorner e A)

omit [Nonempty ν] [Fintype ι] in
lemma localBlockModel_odd (f : E → ι → ℝ) (c : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) (A : M) :
    localBlockModel f c e a D (-A) = -localBlockModel f c e a D A := by
  simp only [localBlockModel,blockScalar,blockOff,blockCorner,map_neg,neg_apply,inner_neg_right,neg_smul,
    signedExtension_odd,neg_add_rev]
  abel

lemma Admissible.localBlockModel_continuousOn {f : E → ι → ℝ} (hf : Admissible f)
    (c : E) (e : W →ₗᵢ[ℝ] E) {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (D : W ≃L[ℝ] W) :
    ContinuousOn (localBlockModel f c e a D) {A : M | IsSelfAdjoint A} := by
  apply ContinuousOn.add
  · exact ((blockScalar_continuous c).smul continuous_const).continuousOn.add
      ((facetTangent a).continuous_of_finiteDimensional.comp
        (D.continuous.comp (blockOff_continuous c e))).continuousOn
  · exact hf.signedExtension_continuousOn.comp (blockCorner_continuous e).continuousOn
      (fun A hA => blockCorner_selfAdjoint e hA)

lemma Admissible.localBlockModel_on_facet {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hI : ∀ i ∈ I, 0 < f c i)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A) {i : ι} (hi : i ∈ I) :
    localBlockModel f c e a D A i = blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i := by
  have hz := hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
    (blockCorner_kernel e he A) (hI i hi)
  simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hz,add_zero]

lemma Admissible.localBlockModel_sum_facet {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A) :
    ∑ i ∈ I, localBlockModel f c e a D A i = blockScalar c A := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    apply Finset.sum_subset (Finset.subset_univ I)
    intro i _ hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  calc
    _ = ∑ i ∈ I, (blockScalar c A * f c i + facetTangent a (D (blockOff c e A)) i) :=
      Finset.sum_congr rfl (fun i hi => hf.localBlockModel_on_facet hc e he a hp D hA hi)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,hs,facetTangent_sum,mul_one,add_zero]

lemma Admissible.localBlockModel_ne_zero {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A) (hAz : A ≠ 0) :
    localBlockModel f c e a D A ≠ 0 := by
  intro hz
  have ha : blockScalar c A = 0 := by
    rw [← hf.localBlockModel_sum_facet hc e he a hIc D hA,hz]
    simp
  have hb : blockOff c e A = 0 := by
    apply D.injective
    apply (facetTangent_injective a)
    rw [map_zero,map_zero]
    ext i
    by_cases hi : i ∈ I
    · have hp : ∀ j ∈ I, 0 < f c j := fun j hj => (mem_positiveSupport f c j).mp (hIc.symm ▸ hj)
      have hh := hf.localBlockModel_on_facet hc e he a hp D hA hi
      rw [hz,ha] at hh
      simpa using hh.symm
    · exact facetTangent_zero_outside a _ hi
  have hC : blockCorner e A = 0 := by
    apply (hf.signedExtension_eq_zero_iff (blockCorner_selfAdjoint e hA)).mp
    simpa only [localBlockModel,ha,hb,zero_smul,map_zero,zero_add] using hz
  exact hAz (block_data_zero c e hc he hes hA ha hb hC)
end LocalModel
end BorsukNine

end OAI
