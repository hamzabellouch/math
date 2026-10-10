import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierEnergy

namespace OAI

/-! Exact Parseval decomposition of the genuine arithmetic-cover mass. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaPrimeRootFourierProjection_integrable {p : Eisenstein}
    (hp : primaryPrime p) (F : cubicThetaPrimeRootSections p)
    (hF : Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)
      (cubicThetaPrimeRootCoverMeasure hp)) (k : Residues p) :
    Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootFourierProjection hp k F) q)^2)
      (cubicThetaPrimeRootCoverMeasure hp) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let D := fun q => (norm p)⁻¹*∑ r : Residues p,
    (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootResidueOperator hp r F) q)^2
  have hi := cubicThetaPrimeRootResidueOperator_integrable hp F hF
  have hD : Integrable D (cubicThetaPrimeRootCoverMeasure hp) :=
    (integrable_finsetSum Finset.univ (fun r _ => hi r)).const_mul _
  apply hD.mono'
    ((cubicThetaPrimeRootSectionNorm_continuous hp _).pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ∑ j : Residues p,(cubicThetaPrimeRootSectionNorm hp
        (cubicThetaPrimeRootFourierProjection hp j F) q)^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    _ = D q := cubicThetaPrimeRootFourierProjection_orbit_energy hp F q

theorem cubicThetaPrimeRootFourierProjection_mass_sum {p : Eisenstein}
    (hp : primaryPrime p) [Fintype (Residues p)] (F : cubicThetaPrimeRootSections p)
    (hF : Integrable (fun q => (cubicThetaPrimeRootSectionNorm hp F q)^2)
      (cubicThetaPrimeRootCoverMeasure hp)) :
    (∑ k : Residues p,∫ q, (cubicThetaPrimeRootSectionNorm hp
      (cubicThetaPrimeRootFourierProjection hp k F) q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp := by
  have hi := cubicThetaPrimeRootFourierProjection_integrable hp F hF
  have ht := cubicThetaPrimeRootResidueOperator_integrable hp F hF
  rw [←integral_finsetSum Finset.univ (fun k _ => hi k)]
  simp_rw [cubicThetaPrimeRootFourierProjection_orbit_energy hp F]
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun r _ => ht r)]
  have hm (r : Residues p) :
      (∫ q, (cubicThetaPrimeRootSectionNorm hp (cubicThetaPrimeRootResidueOperator hp r F) q)^2
        ∂cubicThetaPrimeRootCoverMeasure hp)=
        ∫ q, (cubicThetaPrimeRootSectionNorm hp F q)^2 ∂cubicThetaPrimeRootCoverMeasure hp :=
    cubicThetaPrimeRootSectionTranslate_mass hp (residueRepresentative p r) F
  simp_rw [hm]
  have hcard : (Fintype.card (Residues p):ℝ)=norm p := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact normNat_cast p
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard,
    inv_mul_cancel_left₀ (ne_of_gt (norm_pos_of_ne_zero hp.2.ne_zero))]

end CubicFirstMoment

end

end OAI
