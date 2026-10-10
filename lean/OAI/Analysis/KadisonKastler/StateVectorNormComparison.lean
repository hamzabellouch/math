import OAI.Analysis.KadisonKastler.UnitaryStateTransition

namespace OAI

/-! # Reference-vector norms under a state comparison

Norm convergence of vector states controls the squared vector norm of
each fixed bounded operator. The conjugated version applies this to
unitaries comparing two faithful states.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vector_norm_sq_le_state_distance (ξ η : H) (a : Algebra M) :
    ‖a.val η‖^2 ≤ ‖a.val ξ‖^2+
      ‖vectorFunctional (M := M) η-vectorFunctional ξ‖*‖a‖^2 := by
  let f := vectorFunctional (M := M) η-vectorFunctional ξ
  have he : (f (star a*a)).re=‖a.val η‖^2-‖a.val ξ‖^2 := by
    dsimp only [f]
    rw [sub_apply,vectorFunctional_star_mul_self,vectorFunctional_star_mul_self]
    norm_cast
  have h := Complex.re_le_norm (f (star a*a))
  have hb := f.le_opNorm (star a*a)
  have hn : ‖star a*a‖=‖a‖^2 := by rw [CStarRing.norm_star_mul_self,pow_two]
  rw [hn] at hb
  rw [he] at h
  have hh := h.trans hb
  dsimp only [f] at hh
  linarith only [hh]

theorem conjugate_vector_norm_sq_le_state_distance (ξ η : H)
    (u : unitary (Algebra M)) (a : Algebra M) :
    ‖(u.val*a*star u.val).val η‖^2 ≤ ‖a.val ξ‖^2+
      ‖sandwichFunctional (vectorFunctional ξ) u.val-vectorFunctional η‖*‖a‖^2 := by
  let b : Algebra M := u.val*a*star u.val
  have hb : b*u.val=u.val*a := by
    dsimp only [b]
    rw [mul_assoc (u.val*a),u.property.1,mul_one]
  have hv : b.val (u.val.val ξ)=u.val.val (a.val ξ) :=
    congrArg (fun c : Algebra M => c.val ξ) hb
  have hn : ‖b‖=‖a‖ := by
    change ‖u.val*a*(star u).val‖=‖a‖
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  have hu : ‖u.val.val (a.val ξ)‖=‖a.val ξ‖ :=
    Unitary.norm_map (ambientAlgebraUnitary u) _
  have h := vector_norm_sq_le_state_distance (u.val.val ξ) η b
  rw [hv,hu,hn,
    ← sandwichFunctional_vectorFunctional,norm_sub_rev] at h
  exact h

end

end KadisonKastler

end OAI
