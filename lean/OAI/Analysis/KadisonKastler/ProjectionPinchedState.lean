import OAI.Analysis.KadisonKastler.ScaledCentralProjectionCut
import OAI.Analysis.FactorGeneration.LocalizedStates

namespace OAI

/-! # Pinching a vector state across an almost central projection

This is the first state approximation in Haagerup's Lemma 3.6
(Acta Math.158(1987), p.138). The pinched state is constructed from
two vector functionals and retains faithfulness. Its norm distance from
the original state is controlled by the left/right projection gap.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem vectorFunctional_norm_sub_le (ξ η : H) :
    ‖vectorFunctional (M := M) ξ - vectorFunctional η‖ ≤
      ‖ξ-η‖ * (‖ξ‖+‖η‖) := by
  apply (vectorFunctional (M := M) ξ - vectorFunctional η).opNorm_le_bound
    (M := ‖ξ-η‖ * (‖ξ‖+‖η‖)) (mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  intro x
  change ‖inner ℂ ξ (x.val ξ) - inner ℂ η (x.val η)‖ ≤ _
  have he : inner ℂ ξ (x.val ξ) - inner ℂ η (x.val η) =
      inner ℂ (ξ-η) (x.val ξ) + inner ℂ η (x.val (ξ-η)) := by
    rw [map_sub,inner_sub_left,inner_sub_right]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℂ (ξ-η) (x.val ξ)‖ + ‖inner ℂ η (x.val (ξ-η))‖ := norm_add_le _ _
    _ ≤ ‖ξ-η‖ * ‖x.val ξ‖ + ‖η‖ * ‖x.val (ξ-η)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖ξ-η‖ * (‖x.val‖ * ‖ξ‖) + ‖η‖ * (‖x.val‖ * ‖ξ-η‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (x.val.le_opNorm _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (x.val.le_opNorm _) (norm_nonneg _))
    _ = (‖ξ-η‖ * (‖ξ‖+‖η‖)) * ‖x‖ := by change _ = _ * ‖x.val‖; ring

def projectionReflection (p : H →L[ℂ] H) : H →L[ℂ] H := (2:ℂ) • p - 1

theorem projectionReflection_unitary {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    projectionReflection p ∈ unitary (H →L[ℂ] H) := by
  have hs : star (projectionReflection p) = projectionReflection p := by
    simp only [projectionReflection,star_sub,star_smul,hp.isSelfAdjoint.star_eq,star_one,
      star_ofNat]
  have hm : projectionReflection p * projectionReflection p = 1 := by
    simp only [projectionReflection,sub_mul,mul_sub,smul_mul_smul,mul_one,one_mul,
      hp.isIdempotentElem.eq]
    module
  exact ⟨by rw [hs,hm],by rw [hs,hm]⟩

def projectionPinchedState (p : H →L[ℂ] H) (ξ : H) : Algebra M →L[ℂ] ℂ :=
  vectorFunctional (p ξ) + vectorFunctional ((1-p) ξ)

theorem projectionPinchedState_reflection (p : H →L[ℂ] H) (ξ : H) :
    projectionPinchedState (M := M) p ξ =
      (1/2:ℂ) • (vectorFunctional ξ + vectorFunctional (projectionReflection p ξ)) := by
  ext x
  change inner ℂ (p ξ) (x.val (p ξ)) + inner ℂ ((1-p) ξ) (x.val ((1-p) ξ)) =
    (1/2:ℂ) * (inner ℂ ξ (x.val ξ) +
      inner ℂ (projectionReflection p ξ) (x.val (projectionReflection p ξ)))
  simp only [projectionReflection,sub_apply,one_apply_eq_self,smul_apply,map_sub,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,map_ofNat]
  norm_num
  ring

theorem vectorFunctional_commuting_unitary (ξ : H) (u : unitary (H →L[ℂ] H))
    (hu : (u : H →L[ℂ] H) ∈ M.commutant) :
    vectorFunctional (M := M) ((u : H →L[ℂ] H) ξ) = vectorFunctional ξ := by
  ext x
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp hu x.val x.property
  change inner ℂ ((u : H →L[ℂ] H) ξ) (x.val ((u : H →L[ℂ] H) ξ)) = _
  rw [show x.val ((u : H →L[ℂ] H) ξ) = (u : H →L[ℂ] H) (x.val ξ) from
    congrArg (fun T : H →L[ℂ] H => T ξ) hc]
  exact Unitary.inner_map_map u ξ (x.val ξ)

theorem projectionPinchedState_norm_sub_le {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqM : q ∈ M.commutant) (ξ : H) :
    ‖projectionPinchedState (M := M) p ξ - vectorFunctional ξ‖ ≤
      2 * ‖(p-q) ξ‖ * ‖ξ‖ := by
  let u : unitary (H →L[ℂ] H) := ⟨projectionReflection p,projectionReflection_unitary hp⟩
  let v : unitary (H →L[ℂ] H) := ⟨projectionReflection q,projectionReflection_unitary hq⟩
  have hvM : (v : H →L[ℂ] H) ∈ M.commutant :=
    M.commutant.sub_mem (M.commutant.smul_mem hqM _) M.commutant.one_mem
  have hv := vectorFunctional_commuting_unitary (M := M) ξ v hvM
  have he : projectionPinchedState (M := M) p ξ - vectorFunctional ξ =
      (1/2:ℂ) • (vectorFunctional ((u : H →L[ℂ] H) ξ) -
        vectorFunctional ((v : H →L[ℂ] H) ξ)) := by
    rw [hv,projectionPinchedState_reflection]
    change (1/2:ℂ) • (vectorFunctional ξ + vectorFunctional ((u : H →L[ℂ] H) ξ)) -
      vectorFunctional ξ = _
    module
  have hd : ‖(u : H →L[ℂ] H) ξ - (v : H →L[ℂ] H) ξ‖ = 2 * ‖(p-q) ξ‖ := by
    have hdv : (u : H →L[ℂ] H) ξ - (v : H →L[ℂ] H) ξ = (2:ℂ) • ((p-q) ξ) := by
      change ((2:ℂ) • p - 1) ξ - ((2:ℂ) • q - 1) ξ = _
      simp only [sub_apply,smul_apply,one_apply_eq_self,smul_sub]
      module
    rw [hdv,norm_smul]
    norm_num
  rw [he,norm_smul]
  have hn := vectorFunctional_norm_sub_le (M := M)
    ((u : H →L[ℂ] H) ξ) ((v : H →L[ℂ] H) ξ)
  rw [hd,Unitary.norm_map u,Unitary.norm_map v] at hn
  calc
    ‖(1/2:ℂ)‖ * ‖vectorFunctional ((u : H →L[ℂ] H) ξ) -
        vectorFunctional ((v : H →L[ℂ] H) ξ)‖ ≤
        ‖(1/2:ℂ)‖ * (2 * ‖(p-q) ξ‖ * (‖ξ‖+‖ξ‖)) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by norm_num; ring

end

end KadisonKastler

end OAI
