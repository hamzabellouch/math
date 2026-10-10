import Mathlib
import OAI.Geometry.Borsuk.LocalParity.LocalModel
import OAI.Geometry.Borsuk.MatrixGeometry.BlockParts

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
section ModelRay
variable {k : ℕ} {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix ν ν ℝ
lemma Admissible.localBlockModel_ray {f : E → ι → ℝ} (hf : Admissible f)
    {c : E} (hc : ‖c‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0)
    (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (hIc : positiveSupport f c = I)
    (D : W ≃L[ℝ] W) {A : M} (hA : IsSelfAdjoint A)
    {y : ι → ℝ} {rho d : ℝ} (hr : 0 < rho) (hd : 0 < d)
    (hyi : ∀ i ∈ I, y i = rho * f c i) (hyo : ∀ i ∉ I, y i ≤ 0)
    (hM : localBlockModel f c e a D A = d • y) :
    blockOff c e A = 0 ∧ 0 < blockScalar c A ∧
    localBlockModel f c e a D A = signedExtension f A ∧
    A⁺ = blockScalar c A • rankOne c := by
  have hp : ∀ i ∈ I, 0 < f c i := fun i hi => (mem_positiveSupport f c i).mp (hIc.symm ▸ hi)
  have hfo : ∀ i ∉ I, f c i = 0 := by
    intro i hi
    apply le_antisymm _ (hf.nonneg c hc i)
    exact le_of_not_gt (fun h => hi (hIc ▸ (mem_positiveSupport f c i).mpr h))
  have hs : ∑ i ∈ I, f c i = 1 := by
    rw [← hf.sum_one c hc]
    exact Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hfo i hi)
  have ha : blockScalar c A = d*rho := by
    rw [← hf.localBlockModel_sum_facet hc e he a hIc D hA,hM]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = ∑ i ∈ I, d * (rho * f c i) := Finset.sum_congr rfl (fun i hi => by rw [hyi i hi])
      _ = _ := by simp only [← Finset.mul_sum,hs,mul_one]
  have ht (i : ι) (hi : i ∈ I) : facetTangent a (D (blockOff c e A)) i = 0 := by
    have hh := hf.localBlockModel_on_facet hc e he a hp D hA hi
    rw [hM,ha] at hh
    simp only [Pi.smul_apply,smul_eq_mul,hyi i hi] at hh
    nlinarith
  have hb : blockOff c e A = 0 := by
    apply D.injective
    apply (facetTangent_injective a)
    rw [map_zero,map_zero]
    ext i
    by_cases hi : i ∈ I
    · exact ht i hi
    · exact facetTangent_zero_outside a _ hi
  have hC : blockCorner e A ≤ 0 := by
    apply hf.signedExtension_nonpos (blockCorner_selfAdjoint e hA)
    intro i
    by_cases hi : i ∈ I
    · exact (hf.signedExtension_kernel_coordinate (blockCorner_selfAdjoint e hA) hc
        (blockCorner_kernel e he A) (hp i hi)).le
    · have hh := congrFun hM i
      simp only [localBlockModel,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hb,map_zero,
        add_zero,hfo i hi,mul_zero,zero_add] at hh
      rw [hh]
      exact mul_nonpos_of_nonneg_of_nonpos hd.le (hyo i hi)
  have hap : 0 < blockScalar c A := ha ▸ mul_pos hd hr
  refine ⟨hb,hap,?_,(block_parts e hc he hes hA hb hap.le hC).1⟩
  rw [hf.block_extension e hc he hes hA hb hap.le hC]
  simp only [localBlockModel,hb,map_zero,add_zero]
end ModelRay
end BorsukNine

end OAI
