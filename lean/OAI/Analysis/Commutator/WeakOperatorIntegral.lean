import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory Filter

namespace Kadison.WeakOperatorIntegral

variable {ι E F : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem exists_integral (μ : Measure ι) [IsProbabilityMeasure μ]
    (T : ι → E →L[ℂ] F) (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
    (C : ℝ) (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) :
    ∃ V : E →L[ℂ] F, ‖V‖ ≤ C ∧ ∀ x y,
      inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ := by
  let L : E → F → ℂ := fun x y => ∫ i, inner ℂ (T i x) y ∂μ
  have hL : ∀ x y, ‖L x y‖ ≤ C*‖x‖*‖y‖ := by
    intro x y
    have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun i => inner ℂ (T i x) y)
      (C := C*‖x‖*‖y‖) (Eventually.of_forall (fun i =>
        (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg y))))
    simpa only [probReal_univ,mul_one] using h
  have haddY : ∀ x y z, L x (y+z)=L x y+L x z := by
    intro x y z
    simp only [L,inner_add_right,integral_add (hI x y) (hI x z)]
  have hsmulY : ∀ x (a : ℂ) y, L x (a • y)=a * L x y := by
    intro x a y
    simp only [L,inner_smul_right,integral_const_mul]
  let q : E → StrongDual ℂ F := fun x =>
    ({ toFun := L x
       map_add' := haddY x
       map_smul' := fun a y => hsmulY x a y } : F →ₗ[ℂ] ℂ).mkContinuous
      (C*‖x‖) (hL x)
  have hq : ∀ x y, q x y=L x y := fun _ _ => rfl
  have haddX : ∀ x z y, L (x+z) y=L x y+L z y := by
    intro x z y
    simp only [L,map_add,inner_add_left,integral_add (hI x y) (hI z y)]
  have hsmulX : ∀ (a : ℂ) x y, L (a • x) y=star a * L x y := by
    intro a x y
    simp only [L,map_smul,inner_smul_left,RCLike.star_def,integral_const_mul]
  let V₀ : E →ₗ[ℂ] F :=
    { toFun := fun x => (InnerProductSpace.toDual ℂ F).symm (q x)
      map_add' := by
        intro x z
        apply ext_inner_right ℂ
        intro y
        simp only [inner_add_left,InnerProductSpace.toDual_symm_apply,hq,haddX]
      map_smul' := by
        intro a x
        apply ext_inner_right ℂ
        intro y
        simp only [inner_smul_left,InnerProductSpace.toDual_symm_apply,hq,hsmulX,
          RingHom.id_apply,RCLike.star_def] }
  have hV : ∀ x, ‖V₀ x‖ ≤ C*‖x‖ := by
    intro x
    change ‖(InnerProductSpace.toDual ℂ F).symm (q x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (mul_nonneg hC (norm_nonneg x)) (hL x)
  refine ⟨V₀.mkContinuous C hV,LinearMap.mkContinuous_norm_le _ hC hV,?_⟩
  intro x y
  exact InnerProductSpace.toDual_symm_apply

omit [CompleteSpace F] in
theorem integral_unique (μ : Measure ι) (T : ι → E →L[ℂ] F)
    {V W : E →L[ℂ] F}
    (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)
    (hW : ∀ x y, inner ℂ (W x) y = ∫ i, inner ℂ (T i x) y ∂μ) : V = W := by
  ext x
  apply ext_inner_right ℂ
  intro y
  exact (hV x y).trans (hW x y).symm

end Kadison.WeakOperatorIntegral

end

end
end

end OAI
