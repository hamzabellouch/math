import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootAverageBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierVanishing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalFourierAlgebra

namespace OAI

/-! The actual root average selects exactly the Fourier frequencies
divisible by the prime, on every positive-height horizontal slice. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeRootHorizontal {p : Eisenstein} (F : cubicThetaPrimeRootSections p)
    (v : ℝ) (hv : 0<v) : C(ℂ,ℂ) :=
  ⟨fun z => F.val (cubicThetaHorizontalPoint v hv z),
    F.val.continuous.comp (cubicThetaHorizontalPoint_continuous v hv)⟩

lemma cubicThetaPrimeRootHorizontal_periodic {p : Eisenstein}
    (F : cubicThetaPrimeRootSections p) (v : ℝ) (hv : 0<v) (w : Eisenstein) (z : ℂ) :
    cubicThetaPrimeRootHorizontal F v hv (z+3*(w:ℂ))=cubicThetaPrimeRootHorizontal F v hv z := by
  have he : cubicThetaHorizontalPoint v hv (z+3*(w:ℂ))=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w) • cubicThetaHorizontalPoint v hv z := by
    apply Subtype.ext
    change (z+3*(w:ℂ),v)=cubicThetaMobius
      (cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation w)) (z,v)
    rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation]
    push_cast
    rfl
  change F.val (cubicThetaHorizontalPoint v hv (z+3*(w:ℂ)))=_
  rw [he,cubicThetaPrimeRootSection_integral]
  rfl

lemma cubicThetaPrimeRootHorizontal_translate {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (x : Eisenstein) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicThetaPrimeRootHorizontal (cubicThetaPrimeRootSectionTranslate hp x F) v hv z=
      cubicThetaPrimeRootHorizontal F v hv (z+3*(x:ℂ)/(p:ℂ)) := by
  change F.val (cubicThetaPrimeRootElement hp x • cubicThetaHorizontalPoint v hv z)=
    F.val (cubicThetaHorizontalPoint v hv (z+3*(x:ℂ)/(p:ℂ)))
  congr 1
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeRootElement hp x) (z,v)=(z+3*(x:ℂ)/(p:ℂ),v)
  rw [cubicThetaPrimeRootElement_translation,cubicThetaMobius_translation]
  push_cast
  rfl

theorem cubicThetaPrimeRootAverage_fourier {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeRootSections p) (v : ℝ) (hv : 0<v) (h : Eisenstein) :
    cubicThetaHorizontalFourierCoefficient h
        (cubicThetaPrimeRootHorizontal (cubicThetaPrimeRootAverage hp F) v hv)=
      if p∣h then cubicThetaHorizontalFourierCoefficient h (cubicThetaPrimeRootHorizontal F v hv)
        else 0 := by
  classical
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let f := cubicThetaPrimeRootHorizontal F v hv
  have hfun : (cubicThetaPrimeRootHorizontal (cubicThetaPrimeRootAverage hp F) v hv : ℂ → ℂ)=
      fun z => (norm p:ℂ)⁻¹*∑ r : Residues p,f (z+3*(residueRepresentative p r:ℂ)/(p:ℂ)) := by
    funext z
    change (cubicThetaPrimeRootAverage hp F).val (cubicThetaHorizontalPoint v hv z)=_
    rw [cubicThetaPrimeRootAverage_value]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    exact cubicThetaPrimeRootHorizontal_translate hp F (residueRepresentative p r) v hv z
  have hphase (r : Residues p) :
      cubicThetaHorizontalCharacter h (3*(residueRepresentative p r:ℂ)/(p:ℂ))=
        residueFourierChar p hp.2.ne_zero (r*Ideal.Quotient.mk (modulus p) h) := by
    rw [cubicThetaHorizontalCharacter_fraction h p _ hp.2.ne_zero,map_mul,
      residueRepresentative_spec,mul_comm]
  have hcard : (Fintype.card (Residues p):ℂ)=(norm p:ℂ) := by
    rw [←Nat.card_eq_fintype_card,residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  have hzero : Ideal.Quotient.mk (modulus p) h=0 ↔ p∣h := by
    rw [Ideal.Quotient.eq_zero_iff_mem,modulus,Ideal.mem_span_singleton]
  rw [hfun,cubicThetaHorizontalFourier_const_mul,
    cubicThetaHorizontalFourier_sum Finset.univ h _ (by
      intro r _
      exact f.continuous.comp (continuous_id.add continuous_const))]
  simp_rw [cubicThetaHorizontalFourier_translate h f
    (cubicThetaPrimeRootHorizontal_periodic F v hv),hphase]
  rw [←Finset.sum_mul,AddChar.sum_mulShift _ (residueFourierChar_isPrimitive p hp.2.ne_zero),hzero]
  split_ifs <;> simp [hcard,Complex.ofReal_ne_zero.mpr
    (ne_of_gt (norm_pos_of_ne_zero hp.2.ne_zero))]
  rfl

end CubicFirstMoment

end

end OAI
