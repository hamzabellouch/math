import OAI.Analysis.KadisonKastler.ModularPositiveReal
import OAI.Analysis.KadisonKastler.StandardTypeIIIVector
import OAI.Analysis.KadisonKastler.CommonRightProjection

namespace OAI

/-! # Uniqueness on the commutant-unitary orbit of the reference vector

A vector in the generated positive cone which is obtained from the
reference vector by a commutant unitary must be the reference vector.
The proof uses the centralizer identity and positivity of the quadratic
operator attached to `1 - J u J`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {ξ : H}

local instance positiveOrbitRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem positiveCone_commutant_unitary_fixed (d : ModularConjugationData M ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic d.conjugation a ξ))
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M.commutant)
    (hη : (u : H →L[ℂ] H) ξ ∈ modularPositiveCone (M := M) d.conjugation ξ) :
    (u : H →L[ℂ] H) ξ = ξ := by
  let J := d.conjugation
  let η := (u : H →L[ℂ] H) ξ
  let q := conjugationUnitary J d.involutive u
  have hqM : (q : H →L[ℂ] H) ∈ M := d.left_mem ⟨u,hu⟩
  have hηJ : J η = η :=
    modularPositiveCone_fixed J (d.right_mem le_rfl) ξ d.fixes_vector hη
  have hqξ : (q : H →L[ℂ] H) ξ = η := by
    change J ((u : H →L[ℂ] H) (J ξ)) = η
    rw [d.fixes_vector]
    exact hηJ
  have hcomm : (q : H →L[ℂ] H) * star (u : H →L[ℂ] H) =
      star (u : H →L[ℂ] H) * q :=
    VonNeumannAlgebra.mem_commutant_iff.mp (M.commutant.toStarSubalgebra.star_mem' hu) q hqM
  have hqustar : (q : H →L[ℂ] H) (star (u : H →L[ℂ] H) ξ) = ξ := by
    calc
      _ = star (u : H →L[ℂ] H) ((q : H →L[ℂ] H) ξ) :=
        congrArg (fun T : H →L[ℂ] H => T ξ) hcomm
      _ = ξ := by
        rw [hqξ]
        change (star (u : H →L[ℂ] H) * u) ξ = ξ
        rw [Unitary.star_mul_self_of_mem u.property,one_apply_eq_self]
  have hqstarξ : star (q : H →L[ℂ] H) ξ = star (u : H →L[ℂ] H) ξ := by
    calc
      _ = star (q : H →L[ℂ] H) ((q : H →L[ℂ] H) (star (u : H →L[ℂ] H) ξ)) := by
        rw [hqustar]
      _ = _ := by
        change (star (q : H →L[ℂ] H) * q) (star (u : H →L[ℂ] H) ξ) = _
        rw [Unitary.star_mul_self_of_mem q.property,one_apply_eq_self]
  have hcentral (x : Algebra M) :
      inner ℂ ξ (((q : H →L[ℂ] H) * x.val) ξ) =
        inner ℂ ξ ((x.val * q) ξ) := by
    change inner ℂ ξ ((q : H →L[ℂ] H) (x.val ξ)) =
      inner ℂ ξ (x.val ((q : H →L[ℂ] H) ξ))
    calc
      _ = inner ℂ (star (q : H →L[ℂ] H) ξ) (x.val ξ) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
      _ = inner ℂ (star (u : H →L[ℂ] H) ξ) (x.val ξ) := by rw [hqstarξ]
      _ = inner ℂ ξ ((u : H →L[ℂ] H) (x.val ξ)) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
      _ = inner ℂ ξ (x.val ((u : H →L[ℂ] H) ξ)) := by
        exact congrArg (inner ℂ ξ)
          (congrArg (fun T : H →L[ℂ] H => T ξ)
            (VonNeumannAlgebra.mem_commutant_iff.mp hu x.val x.property).symm)
      _ = _ := by rw [hqξ]
  have hconj : conjugationOperator J (star (q : H →L[ℂ] H)) = star (u : H →L[ℂ] H) := by
    change conjugationOperator J (star (conjugationOperator J u)) = _
    rw [← conjugationOperator_star J d.involutive,conjugationOperator_twice J d.involutive]
  have hstar : star (u : H →L[ℂ] H) ξ = η := by
    have he := d.centralizer_vector ⟨q,hqM⟩ hcentral
    change conjugationOperator J (star (q : H →L[ℂ] H)) ξ = (q : H →L[ℂ] H) ξ at he
    rwa [hconj,hqξ] at he
  have hqη : (q : H →L[ℂ] H) η = ξ := by rw [← hstar,hqustar]
  let a : Algebra M := 1 - ⟨q,hqM⟩
  have hrighta : conjugationOperator J a.val = 1 - (u : H →L[ℂ] H) := by
    change conjugationOperator J (1 - conjugationOperator J u) = _
    rw [conjugationOperator_sub,conjugationOperator_one J d.involutive,
      conjugationOperator_twice J d.involutive]
  have haξ : modularQuadratic J a ξ = (2 : ℝ) • (ξ-η) := by
    change (1 - (q : H →L[ℂ] H)) (conjugationOperator J a.val ξ) = _
    rw [hrighta,sub_apply,one_apply_eq_self]
    change (1 - (q : H →L[ℂ] H)) (ξ-η) = _
    simp only [sub_apply,one_apply_eq_self,map_sub,hqξ,hqη,two_smul]
    abel
  have h := modularPositiveCone_acute J d.involutive (d.right_mem le_rfl) ξ hpos
    (modularQuadratic_mem_positiveCone J ξ a) hη
  rw [haξ,real_inner_smul_left,inner_sub_left,real_inner_self_eq_norm_sq] at h
  change 0 ≤ 2 * (inner ℝ ξ η - ‖η‖ ^ 2) at h
  have hnorm : ‖η‖ = ‖ξ‖ := Unitary.norm_map u ξ
  have he := norm_sub_sq_real ξ η
  have hsq : ‖ξ-η‖ ^ 2 ≤ 0 := by
    rw [he,← hnorm]
    nlinarith only [h]
  have hz : ‖ξ-η‖ = 0 := by nlinarith only [hsq,sq_nonneg ‖ξ-η‖]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end

end KadisonKastler

end OAI
