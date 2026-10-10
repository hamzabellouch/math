import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAverage
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSectionNorm

namespace OAI

/-! Contraction of the actual root average in the quotient square norm.
The bound follows from finite Cauchy--Schwarz and the proved measure transport. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeRootAverage_value {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (F : cubicThetaPrimeRootSections p) (y : CubicThetaPoint) :
    (cubicThetaPrimeRootAverage hp F).val y=
      (norm p:ℂ)⁻¹*∑ r : Residues p,(cubicThetaPrimeRootResidueOperator hp r F).val y := by
  let ev : cubicThetaPrimeRootSections p →ₗ[ℂ] ℂ :=
    { toFun := fun G => G.val y, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  change ev (cubicThetaPrimeRootAverage hp F)=
    (norm p:ℂ)⁻¹*∑ r : Residues p,ev (cubicThetaPrimeRootResidueOperator hp r F)
  rw [cubicThetaPrimeRootAverage_apply,map_smul,map_sum]
  rfl

theorem cubicThetaPrimeRootAverage_norm_sq {p : Eisenstein} (hp : primaryPrime p)
    [Fintype (Residues p)] (F : cubicThetaPrimeRootSections p)
    (q : CubicThetaPrimeRootCover hp) :
    (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootAverage hp F) q)^2≤
      (norm p)⁻¹*∑ r : Residues p,
        (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootResidueOperator hp r F) q)^2 := by
  induction q using Quotient.inductionOn with
  | h y =>
    let v : Residues p → ℂ := fun r => (cubicThetaPrimeRootResidueOperator hp r F).val y
    have hcard : (Fintype.card (Residues p):ℝ)=norm p := by
      rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
      exact normNat_cast p
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Residues p => (1:ℝ)) (fun r => ‖v r‖)
    simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hcard] at hcs
    have hs : ‖∑ r : Residues p,v r‖^2≤norm p*∑ r : Residues p,‖v r‖^2 :=
      ((sq_le_sq₀ (_root_.norm_nonneg _) (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))).mpr
        (norm_sum_le Finset.univ v)).trans hcs
    change ‖(cubicThetaPrimeRootAverage hp F).val y‖^2≤
      (norm p)⁻¹*∑ r : Residues p,‖(cubicThetaPrimeRootResidueOperator hp r F).val y‖^2
    rw [cubicThetaPrimeRootAverage_value]
    simp only [norm_mul,norm_inv,Complex.norm_of_nonneg (norm_nonneg p),mul_pow]
    change (norm p)⁻¹^2*‖∑ r : Residues p,v r‖^2≤(norm p)⁻¹*∑ r : Residues p,‖v r‖^2
    calc
      _ ≤ (norm p)⁻¹^2*(norm p*∑ r : Residues p,‖v r‖^2) :=
        mul_le_mul_of_nonneg_left hs (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt (norm_pos_of_ne_zero hp.2.ne_zero)]

lemma cubicThetaPrimeRootResidueOperator_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)
      (cubicThetaPrimeRootCoverMeasure hp)) (r : Residues p) :
    Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootResidueOperator hp r F) q)^2) (cubicThetaPrimeRootCoverMeasure hp) := by
  have he := (cubicThetaPrimeRootCoverTranslate_measurePreserving hp
    (residueRepresentative p r)).integrable_comp_of_integrable hF
  change Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp
    (cubicThetaPrimeRootSectionTranslate hp (residueRepresentative p r) F) q)^2) _
  simpa only [Function.comp_def,cubicThetaPrimeRootSectionTranslate_norm] using he

theorem cubicThetaPrimeRootAverage_mass_le {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p)
    (hF : Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)
      (cubicThetaPrimeRootCoverMeasure hp)) :
    (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootAverage hp F) q)^2
      ∂cubicThetaPrimeRootCoverMeasure hp)≤
      ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let D := fun q => (norm p)⁻¹*∑ r : Residues p,
    (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootResidueOperator hp r F) q)^2
  have hi := cubicThetaPrimeRootResidueOperator_integrable hp F hF
  have hD : Integrable D (cubicThetaPrimeRootCoverMeasure hp) :=
    (integrable_finsetSum Finset.univ (fun r _ => hi r)).const_mul _
  have hA : Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootAverage hp F) q)^2) (cubicThetaPrimeRootCoverMeasure hp) := by
    apply hD.mono'
      ((cubicThetaPrimeRootSectionNorm_continuous hp _).pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact cubicThetaPrimeRootAverage_norm_sq hp F q)
  have hm (r : Residues p) :
      (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootResidueOperator hp r F) q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp)=
        ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp :=
    cubicThetaPrimeRootSectionTranslate_mass hp (residueRepresentative p r) F
  have hcard : (Fintype.card (Residues p):ℝ)=norm p := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact normNat_cast p
  calc
    _ ≤ ∫ q, D q ∂cubicThetaPrimeRootCoverMeasure hp :=
      integral_mono hA hD (cubicThetaPrimeRootAverage_norm_sq hp F)
    _ = _ := by
      dsimp only [D]
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun r _ => hi r)]
      simp_rw [hm]
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard,
        inv_mul_cancel_left₀ (ne_of_gt (norm_pos_of_ne_zero hp.2.ne_zero))]

end CubicFirstMoment

end

end OAI
