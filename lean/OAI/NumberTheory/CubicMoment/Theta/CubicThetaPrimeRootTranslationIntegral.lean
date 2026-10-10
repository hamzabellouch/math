import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootOrbitOrthogonal

namespace OAI

/-! First-level Hilbert orthogonality, expressed as its literal
fundamental-domain integral for finite-cover transport. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaPrimeRoot_translation_integral_zero {p : Eisenstein}
    (hp : primaryPrime p) (x : Eisenstein) (hx : ¬p∣x)
    (F G : cubicThetaSmoothTests) :
    (∫ z in cubicThetaPrimeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  let r : Residues p := Ideal.Quotient.mk (modulus p) x
  have hr : r≠0 := by
    intro he
    exact hx (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
  let c : ℂ := ((Real.sqrt ((cubicThetaPrimeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)
  have hc : c≠0 := by
    change ((Real.sqrt ((cubicThetaPrimeRootCoverGroup hp).index:ℝ))⁻¹:ℂ)≠0
    exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (cubicThetaPrimeRootCoverDegree_pos hp)))
  have he := cubicThetaPrimeRootLift_translate_pair_zero hp r hr
    (cubicThetaGlobalMassClosure F) (cubicThetaGlobalMassClosure G)
  simp only [cubicThetaPrimeRootLiftL2_smooth,cubicThetaPrimeRootNormalizedRestriction,
    LinearMap.smul_apply,LinearMap.comp_apply,map_smul,cubicThetaPrimeRootResidueL2_finite] at he
  change inner ℂ (c • cubicThetaPrimeRootFiniteEmbedding hp (cubicThetaPrimeRootSmoothRestriction hp F))
    (c • cubicThetaPrimeRootFiniteEmbedding hp
      (cubicThetaPrimeRootFiniteResidue hp r (cubicThetaPrimeRootSmoothRestriction hp G)))=0 at he
  rw [inner_smul_left (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp),
    inner_smul_right (𝕜:=ℂ) (E:=cubicThetaPrimeRootAutomorphicL2 hp)] at he
  have hs : starRingEnd ℂ c≠0 := by simpa only [starRingEnd_apply] using star_ne_zero.mpr hc
  have hz := (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hs)).resolve_left hc
  rw [cubicThetaPrimeRootSectionPairing_L2,cubicThetaPrimeRootSectionPairing_unfold] at hz
  change (∫ z in cubicThetaPrimeRootCoverDomain hp,star (F.val.val z)*
    (cubicThetaPrimeRootResidueOperator hp r
      (cubicThetaPrimeRootSectionRestrict G.val)).val z ∂cubicThetaPointMeasure)=0 at hz
  rw [show r=Ideal.Quotient.mk (modulus p) x from rfl,cubicThetaPrimeRootResidueOperator_mk] at hz
  exact hz

end CubicFirstMoment

end

end OAI
