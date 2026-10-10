import OAI.Analysis.Pureness.Tensor.SpatialPowersSmallAverage

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A H E : Type*} [CStarAlgebra A] [CStarAlgebra E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

private lemma hom_zero_of_small_averages {B D : Type*} [CStarAlgebra B] [CStarAlgebra D]
    (Φ : B →⋆ₐ[ℂ] D) (x e : B) (av : ℕ → ℕ → B → B)
    (hsub : ∀ m n, av m n (x-e) = av m n x-av m n e)
    (hfix : ∀ m n, n ≠ 0 → av m n e = e)
    (hzero : ∀ m n, Φ (av m n x) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ m n, n ≠ 0 ∧ ‖av m n (x-e)‖ < ε) :
    Φ e = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_gt
  intro ε hε
  obtain ⟨m, n, hn, hb⟩ := hsmall ε hε
  have hav : av m n (x-e) = av m n x-e :=
    (hsub m n).trans (congrArg (fun v => av m n x-v) (hfix m n hn))
  have hm : Φ (av m n (x-e)) = -Φ e := by
    rw [hav, map_sub, hzero, zero_sub]
  have hnorm : ‖Φ e‖ ≤ ‖av m n (x-e)‖ := by
    calc
      _ = ‖-Φ e‖ := (norm_neg _).symm
      _ = ‖Φ (av m n (x-e))‖ := congrArg norm hm.symm
      _ ≤ _ := NonUnitalStarAlgHom.norm_apply_le Φ.toNonUnitalStarAlgHom _
  exact hnorm.trans_lt hb

include hα in

theorem spatialFreeGroupHom_expectation_kernel
    (Φ : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ] E)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) (hx : Φ x = 0) :
    Φ (spatialCoefficientExpectation (G := FreeGroup ℕ) α x) = 0 := by
  let e := spatialCoefficientExpectation (G := FreeGroup ℕ) α x
  let z := x-e
  have hz : spatialGroupFourier α (1 : FreeGroup ℕ) z = 0 :=
    (map_sub (spatialGroupFourier α (1 : FreeGroup ℕ)) x e).trans
      ((congrArg (fun v : A => spatialGroupFourier α (1 : FreeGroup ℕ) x-v)
        (spatialGroupFourier_left (G := FreeGroup ℕ) α hα
          (spatialGroupFourier α (1 : FreeGroup ℕ) x))).trans (sub_self _))
  exact hom_zero_of_small_averages Φ x e (spatialFreeGroupAverage α)
    (fun m n => unitaryAverage_sub
      (B := representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
      (fun i : Fin n => spatialGroupUnitary α (FreeGroup.of (m+i.val))) x e)
    (fun m n hn => spatialGroupAverage_fixed_left α hn
      (fun i : Fin n => FreeGroup.of (m+i.val)) _)
    (fun m n => unitaryAverage_map_zero
      (B := representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
      (fun i : Fin n => spatialGroupUnitary α (FreeGroup.of (m+i.val))) Φ x hx)
    (fun ε hε => exists_small_spatial_centered_average α hα z hz ε hε)

include hα in

theorem spatialFreeGroupHom_injective
    (Φ : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ] E)
    (hl : Function.Injective (fun a : A => Φ (spatialCompletionMap α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype (a ⊗ₜ[ℂ] 1)))) :
    Function.Injective Φ :=
  spatialHom_injective_of_expectation_kernel α hα Φ hl
    (spatialFreeGroupHom_expectation_kernel α hα Φ)
end CuntzPureness

end

end OAI
