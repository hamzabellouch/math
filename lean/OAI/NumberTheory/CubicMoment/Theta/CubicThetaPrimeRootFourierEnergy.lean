import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierResolution
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAverageBound

namespace OAI

/-! Parseval for the actual root projections, first on each orbit and
then on the finite arithmetic cover. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeRootFourierProjection_value {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (k : Residues p) (F : cubicThetaPrimeRootSections p)
    (y : CubicThetaPoint) :
    (cubicThetaPrimeRootFourierProjection hp k F).val y=
      (norm p:ℂ)⁻¹*cubicThetaFiniteFourier p hp.2.ne_zero
        (fun r => (cubicThetaPrimeRootResidueOperator hp r F).val y) (-k) := by
  let ev : cubicThetaPrimeRootSections p →ₗ[ℂ] ℂ :=
    { toFun := fun G => G.val y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change ev (cubicThetaPrimeRootFourierProjection hp k F)=_
  rw [cubicThetaPrimeRootFourierProjection_apply,map_smul,map_sum]
  change (norm p:ℂ)⁻¹*(∑ r : Residues p,
    star (residueFourierChar p hp.2.ne_zero (k*r))*
      (cubicThetaPrimeRootResidueOperator hp r F).val y)=_
  unfold cubicThetaFiniteFourier
  apply congrArg (fun z : ℂ => (norm p:ℂ)⁻¹*z)
  apply Finset.sum_congr rfl
  intro r _
  rw [cubicThetaResidueFourier_star]
  change residueFourierChar p hp.2.ne_zero (-(k*r))*
      (cubicThetaPrimeRootResidueOperator hp r F).val y=
    (cubicThetaPrimeRootResidueOperator hp r F).val y*
      residueFourierChar p hp.2.ne_zero ((-k)*r)
  exact (congrArg (fun a : Residues p => residueFourierChar p hp.2.ne_zero a*
    (cubicThetaPrimeRootResidueOperator hp r F).val y) (neg_mul k r).symm).trans
      (mul_comm _ _)

theorem cubicThetaPrimeRootFourierProjection_orbit_energy {p : Eisenstein}
    (hp : primaryPrime p) [Fintype (Residues p)] (F : cubicThetaPrimeRootSections p)
    (q : CubicThetaPrimeRootCover hp) :
    (∑ k : Residues p,(cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootFourierProjection hp k F) q)^2)=
      (norm p)⁻¹*∑ r : Residues p,(cubicThetaPrimeRootSectionNorm hp
        (cubicThetaPrimeRootResidueOperator hp r F) q)^2 := by
  induction q using Quotient.inductionOn with
  | h y =>
    let f : Residues p → ℂ := fun r => (cubicThetaPrimeRootResidueOperator hp r F).val y
    have hcard : (Fintype.card (Residues p):ℝ)=norm p := by
      rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
      exact normNat_cast p
    have hn : (∑ k : Residues p,‖cubicThetaFiniteFourier p hp.2.ne_zero f (-k)‖^2)=
        ∑ k : Residues p,‖cubicThetaFiniteFourier p hp.2.ne_zero f k‖^2 := by
      have he := Equiv.sum_comp (Equiv.neg (Residues p))
        (fun k => ‖cubicThetaFiniteFourier p hp.2.ne_zero f k‖^2)
      change (∑ k : Residues p,‖cubicThetaFiniteFourier p hp.2.ne_zero f (-k)‖^2)=_ at he
      exact he
    change (∑ k : Residues p,‖(cubicThetaPrimeRootFourierProjection hp k F).val y‖^2)=
      (norm p)⁻¹*∑ r : Residues p,‖f r‖^2
    simp_rw [cubicThetaPrimeRootFourierProjection_value,norm_mul,norm_inv,
      Complex.norm_of_nonneg (norm_nonneg p),mul_pow]
    rw [←Finset.mul_sum,hn,cubicThetaFiniteFourier_norm_sq,hcard]
    field_simp [ne_of_gt (norm_pos_of_ne_zero hp.2.ne_zero)]

end CubicFirstMoment

end

end OAI
