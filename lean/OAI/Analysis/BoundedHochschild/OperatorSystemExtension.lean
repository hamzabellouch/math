import OAI.Analysis.BoundedHochschild.OperatorSystemFunctionals

namespace OAI

/-! Positive scalar extension from an operator system. No multiplicative
closure or closedness of the subspace is required. -/

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_positive_operatorSystem_extension
    (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (hstar : ∀ a ∈ S, star a ∈ S) (f : S →ₗ[ℂ] ℂ)
    (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a) :
    ∃ F : A →ₚ[ℂ] ℂ, ∀ a : S, F (a : A) = f a := by
  let c := (f ⟨1, h1⟩).re
  have hc : 0 ≤ c := (hf ⟨1, h1⟩ zero_le_one).1
  let g := operatorSystemRealFunctional S h1 f hf
  have hg : ‖g‖ ≤ c := by
    apply g.opNorm_le_bound hc
    intro a
    exact positive_subspace_real_bound S h1 f hf (operatorSystemRealInclusion S a)
      a.property.2
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (operatorSystemRealPart S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ c := by
    apply G.opNorm_le_bound hc
    intro a
    exact (G₀.le_opNorm (sa a)).trans
      (mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg a))
  have hG1 : G 1 = c := by
    exact hG₀ ⟨1, h1, IsSelfAdjoint.one A⟩
  let F : A →ₚ[ℂ] ℂ :=
    PositiveLinearMap.mk₀ (NaimarkZFC.selfAdjointComplexify G.toLinearMap) (fun a ha => by
      let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
      change 0 ≤ NaimarkZFC.selfAdjointComplexify G.toLinearMap (x : A)
      rw [NaimarkZFC.selfAdjointComplexify_coe]
      exact ⟨selfAdjoint_nonneg_of_norm_le G c hGn hG1 x ha, by simp⟩)
  have hsa (a : S) (ha : IsSelfAdjoint (a : A)) : F (a : A) = f a := by
    let b : operatorSystemRealPart S := ⟨a, a.property, ha⟩
    let x : selfAdjoint A := ⟨a, ha⟩
    change NaimarkZFC.selfAdjointComplexify G.toLinearMap (x : A) = f a
    rw [NaimarkZFC.selfAdjointComplexify_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    apply Complex.ext
    · simp
    · simpa using (positive_subspace_selfAdjoint_im S h1 f hf a ha).symm
  refine ⟨F, fun a => ?_⟩
  have hr : (realPart (a : A) : A) ∈ S := by
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact S.smul_mem _ (S.add_mem a.property (hstar a a.property))
  have hi : (imaginaryPart (a : A) : A) ∈ S := by
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact S.smul_mem _ (S.smul_mem _ (S.sub_mem a.property (hstar a a.property)))
  let ar : S := ⟨realPart (a : A), hr⟩
  let ai : S := ⟨imaginaryPart (a : A), hi⟩
  have ha : a = ar + Complex.I • ai := by
    apply Subtype.ext
    exact (realPart_add_I_smul_imaginaryPart (a : A)).symm
  rw [ha]
  change F ((ar : A) + Complex.I • (ai : A)) = f (ar + Complex.I • ai)
  simp only [map_add, map_smul]
  rw [hsa ar (realPart (a : A)).property, hsa ai (imaginaryPart (a : A)).property]

end BoundedHochschild.KadisonRingrose

end

end OAI
