import OAI.Analysis.KadisonKastler.SpatialStateHomogeneity

namespace OAI

/-! # State defects of transitions between two comparing unitaries

Two unitaries carrying the same state close to a prescribed state differ
by a unitary with small state commutator. These quantitative identities
are used to compare their actions on bicentralizer elements.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem sandwich_unitary_inverse_defect_norm (φ : A →L[ℂ] ℂ)
    (u : unitary A) :
    ‖sandwichFunctional φ (star u).val-φ‖=‖sandwichFunctional φ u.val-φ‖ := by
  have he : sandwichFunctional (sandwichFunctional φ u.val-φ) (star u).val=
      -(sandwichFunctional φ (star u).val-φ) := by
    rw [sandwichFunctional_sub,sandwichFunctional_comp,Unitary.coe_star,
      u.property.1,sandwichFunctional_one]
    abel
  have hn := sandwichFunctional_isometry_norm
    (sandwichFunctional φ u.val-φ) (star u).val (star u).property.1
    (norm_unitary_le_one (star u))
  rwa [he,norm_neg] at hn

theorem sandwich_unitary_transition_norm (φ : A →L[ℂ] ℂ)
    (u v : unitary A) :
    ‖sandwichFunctional φ ((star v)*u).val-φ‖=
      ‖sandwichFunctional φ u.val-sandwichFunctional φ v.val‖ := by
  have he : sandwichFunctional (sandwichFunctional φ u.val-
      sandwichFunctional φ v.val) (star v).val =
      sandwichFunctional φ ((star v)*u).val-φ := by
    rw [sandwichFunctional_sub,sandwichFunctional_comp,sandwichFunctional_comp,
      Unitary.coe_star,v.property.1,sandwichFunctional_one]
    rfl
  have hn := sandwichFunctional_isometry_norm
    (sandwichFunctional φ u.val-sandwichFunctional φ v.val) (star v).val
    (star v).property.1 (norm_unitary_le_one (star v))
  rwa [he] at hn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorStateCommutator_norm_eq_sandwich (ξ : H) (u : unitary (Algebra M)) :
    ‖vectorStateCommutator ξ u.val‖=
      ‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional ξ‖ := by
  have hle : ‖vectorStateCommutator ξ u.val‖ ≤
      ‖sandwichFunctional (vectorFunctional ξ) (star u).val-vectorFunctional ξ‖ := by
    apply (vectorStateCommutator ξ u.val).opNorm_le_bound (norm_nonneg _)
    intro b
    have he : vectorStateCommutator ξ u.val b =
        (sandwichFunctional (vectorFunctional (M := M) ξ) (star u).val-
          vectorFunctional (M := M) ξ) (b*u.val) := by
      simp only [sub_apply,sandwichFunctional_apply,Unitary.coe_star,star_star]
      change vectorFunctional ξ (u.val*b-b*u.val)=
        vectorFunctional ξ (u.val*(b*u.val)*star u.val)-vectorFunctional ξ (b*u.val)
      rw [map_sub,mul_assoc u.val,mul_assoc b,u.property.2,mul_one]
    rw [he]
    exact (((sandwichFunctional (vectorFunctional ξ) (star u).val-
      vectorFunctional ξ).le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg b)
          (norm_unitary_le_one u))) (norm_nonneg _)))
  have he := sandwich_unitary_inverse_defect_norm (vectorFunctional (M := M) ξ) u
  apply le_antisymm (hle.trans he.le)
  rw [← he]
  exact sandwich_unitary_state_norm_sub_le ξ u

theorem unitary_state_transition_defect (ξ η : H) (u v : unitary (Algebra M)) :
    ‖vectorStateCommutator ξ ((star v)*u).val‖ ≤
      ‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional η‖+
      ‖sandwichFunctional (vectorFunctional ξ) v.val-vectorFunctional η‖ := by
  rw [vectorStateCommutator_norm_eq_sandwich,sandwich_unitary_transition_norm]
  calc
    _ = ‖(sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional η)+
        (vectorFunctional η-sandwichFunctional (vectorFunctional ξ) v.val)‖ := by
      congr 1
      abel
    _ ≤ _ := norm_add_le _ _
    _ = _ := by rw [norm_sub_rev (vectorFunctional η)]

end

end KadisonKastler

end OAI
