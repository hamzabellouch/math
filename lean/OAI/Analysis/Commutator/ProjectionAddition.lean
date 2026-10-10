import Mathlib
import OAI.Analysis.Commutator.ProjectionEquivalence

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}

def orthogonalSum (v : Link M e f) (w : Link M e' f')
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0) (hvi : v.initial=e) : Link M (e+e') (f+f') := by
  let b : Link M (e+e') (f+f') :=
    ⟨v.val,v.mem,v.triple,v.source_le.trans (le_add_of_nonneg_right he'.nonneg),
      v.target_le.trans (le_add_of_nonneg_right hf'.nonneg)⟩
  have hbi : b.initial=e := hvi
  let c : Link M ((e+e')-b.initial) ((f+f')-b.final) :=
    ⟨w.val,w.mem,w.triple,by simpa only [hbi,add_sub_cancel_left] using w.source_le,
      w.target_le.trans (by
        apply le_sub_iff_add_le.mpr
        change f' + v.final ≤ f + f'
        have hv : v.final ≤ f := v.target_le
        calc
          f' + v.final = v.final + f' := add_comm _ _
          _ ≤ f+f' := add_le_add hv le_rfl)⟩
  exact b.extend (he.add he' hes) (hf.add hf' hfs) c

lemma orthogonalSum_initial (v : Link M e f) (w : Link M e' f')
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0) (hvi : v.initial=e) :
    (v.orthogonalSum w he hf he' hf' hes hfs hvi).initial=v.initial+w.initial := by
  apply Link.extend_initial
  · exact he.add he' hes
  · exact hf.add hf' hfs

lemma orthogonalSum_final (v : Link M e f) (w : Link M e' f')
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0) (hvi : v.initial=e) :
    (v.orthogonalSum w he hf he' hf' hes hfs hvi).final=v.final+w.final := by
  apply Link.extend_final
  · exact he.add he' hes
  · exact hf.add hf' hfs

end Link

lemma SubEquivalent.orthogonal_add {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0)
    (h : SubEquivalent M e f) (k : SubEquivalent M e' f') :
    SubEquivalent M (e+e') (f+f') := by
  obtain ⟨v,hv⟩ := h
  obtain ⟨w,hw⟩ := k
  exact ⟨v.orthogonalSum w he hf he' hf' hes hfs hv,
    (v.orthogonalSum_initial w he hf he' hf' hes hfs hv).trans (by rw [hv,hw])⟩

lemma Equivalent.orthogonal_add {M : VonNeumannAlgebra H} {e f e' f' : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (he' : IsStarProjection e') (hf' : IsStarProjection f')
    (hes : e*e'=0) (hfs : f*f'=0)
    (h : Equivalent M e f) (k : Equivalent M e' f') :
    Equivalent M (e+e') (f+f') := by
  obtain ⟨v,hvi,hvf⟩ := h
  obtain ⟨w,hwi,hwf⟩ := k
  exact ⟨v.orthogonalSum w he hf he' hf' hes hfs hvi,
    (v.orthogonalSum_initial w he hf he' hf' hes hfs hvi).trans (by rw [hvi,hwi]),
    (v.orthogonalSum_final w he hf he' hf' hes hfs hvi).trans (by rw [hvf,hwf])⟩

theorem subEquivalent_unitary (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (h : SubEquivalent M e f) :
    ∃ u∈M,star u*u=1 ∧ u*star u=1 ∧ u*e*star u≤f := by
  obtain ⟨v,hvi⟩ := h
  obtain ⟨u,hu,hui,huf,huv⟩ := finite_unitary_extension M hfac hfin
    heM (M.mul_mem v.mem (M.star_mem' v.mem)) he v.final_projection
    (⟨v.val,v.mem,v.triple,v.source_le,le_rfl⟩ : Link M e v.final) hvi rfl
  have heq : u*e*star u=v.final := by
    calc
      _=(u*e)*star (u*e) := by rw [star_mul,he.isSelfAdjoint.star_eq,←mul_assoc,
        mul_assoc u e e,he.isIdempotentElem.eq]
      _=v.final := by rw [huv]; rfl
  exact ⟨u,hu,hui,huf,heq ▸ v.target_le⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
