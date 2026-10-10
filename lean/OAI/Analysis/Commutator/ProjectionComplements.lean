import Mathlib
import OAI.Analysis.Commutator.ProjectionAddition

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma conjugate_projection {e u : H →L[ℂ] H} (he : IsStarProjection e)
    (hui : star u*u=1) : IsStarProjection (u*e*star u) := by
  constructor
  · change (u*e*star u)*(u*e*star u)=u*e*star u
    calc
      _=u*e*(star u*u)*e*star u := by noncomm_ring
      _=u*e*star u := by rw [hui,mul_one,mul_assoc u e e,he.isIdempotentElem.eq]
  · change star (u*e*star u)=u*e*star u
    simp only [star_mul,star_star,he.isSelfAdjoint.star_eq,mul_assoc]

lemma equivalent_conjugate {M : VonNeumannAlgebra H} {e u : H →L[ℂ] H}
    (heM : e∈M) (huM : u∈M) (he : IsStarProjection e) (hui : star u*u=1) :
    Equivalent M e (u*e*star u) := by
  have hi : star (u*e)*(u*e)=e := by
    rw [star_mul,he.isSelfAdjoint.star_eq,mul_assoc,←mul_assoc (star u),hui,one_mul,
      he.isIdempotentElem.eq]
  have hf : (u*e)*star (u*e)=u*e*star u := by
    rw [star_mul,he.isSelfAdjoint.star_eq,←mul_assoc,mul_assoc u e e,he.isIdempotentElem.eq]
  have ht : (u*e)*star (u*e)*(u*e)=u*e := by
    rw [mul_assoc,hi,mul_assoc,he.isIdempotentElem.eq]
  exact ⟨⟨u*e,M.mul_mem huM heM,ht,hi.le,hf.le⟩,hi,hf⟩

lemma subEquivalent_complement (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) (hef : SubEquivalent M e f) :
    SubEquivalent M (1-f) (1-e) := by
  obtain ⟨u,hu,hui,huf,hle⟩ := subEquivalent_unitary M hfac hfin heM he hef
  have hconj : star u*(u*e*star u)*u=e := by
    calc
      _=(star u*u)*e*(star u*u) := by noncomm_ring
      _=e := by rw [hui,one_mul,mul_one]
  have he_le : e ≤ star u*f*u := by
    simpa only [hconj] using star_left_conjugate_le_conjugate hle u
  have hcomp : star u*(1-f)*u≤1-e := by
    calc
      _=1-star u*f*u := by rw [mul_sub,sub_mul,mul_one,hui]
      _≤1-e := sub_le_sub_left he_le 1
  have hsu : star (star u)*star u=1 := by simpa only [star_star] using huf
  have hg : IsStarProjection (star u*(1-f)*u) := by
    simpa only [star_star] using (conjugate_projection (u := star u) hf.one_sub hsu)
  have hgM : star u*(1-f)*u∈M :=
    M.mul_mem (M.mul_mem (M.star_mem' hu) (M.sub_mem M.one_mem hfM)) hu
  have heq : Equivalent M (1-f) (star u*(1-f)*u) := by
    simpa only [star_star] using
      (equivalent_conjugate (M.sub_mem M.one_mem hfM) (M.star_mem' hu) hf.one_sub hsu)
  exact heq.subEquivalent.trans hf.one_sub hg (subEquivalent_of_le hgM hg hcomp)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
