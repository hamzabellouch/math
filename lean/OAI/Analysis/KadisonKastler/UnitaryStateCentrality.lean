import OAI.Analysis.KadisonKastler.UnitaryStateTransition
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! # Transporting state-centrality through a comparing unitary -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem algebraUnitary_intertwines (u : unitary (Algebra M)) (a : Algebra M) (ξ : H) :
    Unitary.linearIsometryEquiv (ambientAlgebraUnitary u) (a.val ξ)=
      (Unitary.conjStarAlgAut ℂ (Algebra M) u a).val
        (Unitary.linearIsometryEquiv (ambientAlgebraUnitary u) ξ) := by
  symm
  change ((u.val*a*star u.val)*u.val).val ξ=(u.val*a).val ξ
  rw [mul_assoc (u.val*a),u.property.1,mul_one]

theorem unitary_stateCommutator_conjugate_norm (ξ : H)
    (u : unitary (Algebra M)) (a : Algebra M) :
    ‖vectorStateCommutator ξ (star u.val*a*u.val)‖=
      ‖vectorStateCommutator (u.val.val ξ) a‖ := by
  have h := spatial_stateCommutator_norm (Unitary.conjStarAlgAut ℂ (Algebra M) (star u))
    (Unitary.linearIsometryEquiv (ambientAlgebraUnitary (star u)))
    (algebraUnitary_intertwines (star u)) ξ a
  have he : (Unitary.linearIsometryEquiv (ambientAlgebraUnitary (star u))).symm ξ=
      u.val.val ξ := by
    change (star (star u.val.val)) ξ=u.val.val ξ
    rw [star_star]
  rw [he] at h
  simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,star_star] using h.symm

theorem vectorStateCommutator_state_distance (ξ η : H) (a : Algebra M) :
    ‖vectorStateCommutator ξ a-vectorStateCommutator η a‖ ≤
      2*‖vectorFunctional (M := M) ξ-vectorFunctional η‖*‖a‖ := by
  let d := vectorFunctional (M := M) ξ-vectorFunctional η
  apply (vectorStateCommutator ξ a-vectorStateCommutator η a).opNorm_le_bound
    (by positivity)
  intro b
  have he : (vectorStateCommutator ξ a-vectorStateCommutator η a) b=d (a*b-b*a) := rfl
  rw [he]
  have hc : ‖a*b-b*a‖ ≤ 2*‖a‖*‖b‖ := by
    calc
      _ ≤ ‖a*b‖+‖b*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖b‖+‖b‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = _ := by ring
  calc
    _ ≤ ‖d‖*‖a*b-b*a‖ := d.le_opNorm _
    _ ≤ ‖d‖*(2*‖a‖*‖b‖) := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = _ := by ring

theorem unitary_comparison_centrality (ξ η : H) (u v : unitary (Algebra M)) :
    ‖vectorStateCommutator ξ (star u.val*v.val*u.val)‖ ≤
      ‖vectorStateCommutator η v.val‖+
        2*‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional η‖ := by
  rw [unitary_stateCommutator_conjugate_norm]
  have h := vectorStateCommutator_state_distance (u.val.val ξ) η v.val
  rw [← sandwichFunctional_vectorFunctional] at h
  calc
    _ ≤ ‖vectorStateCommutator η v.val‖+
        ‖vectorStateCommutator (u.val.val ξ) v.val-vectorStateCommutator η v.val‖ := by
      have he : vectorStateCommutator (u.val.val ξ) v.val=
          vectorStateCommutator η v.val+
          (vectorStateCommutator (u.val.val ξ) v.val-vectorStateCommutator η v.val) := by abel
      nth_rw 1 [he]
      exact norm_add_le _ _
    _ ≤ ‖vectorStateCommutator η v.val‖+
        2*‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional η‖*‖v.val‖ :=
      add_le_add le_rfl h
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right (by positivity) (norm_unitary_le_one v))

end

end KadisonKastler

end OAI
