import Mathlib
import OAI.Analysis.Commutator.FiniteCancellation

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def SubEquivalent (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) : Prop :=
  ∃ v : Link M e f, v.initial=e

def Equivalent (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H) : Prop :=
  ∃ v : Link M e f, v.initial=e ∧ v.final=f

namespace Link

variable {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}

def adjoint (v : Link M e f) : Link M f e :=
  ⟨star v.val,M.star_mem' v.mem,by
    simpa only [star_mul,star_star,←mul_assoc] using congrArg star v.triple,
    by simpa only [star_star] using v.target_le,
    by simpa only [star_star] using v.source_le⟩

@[simp] lemma adjoint_initial (v : Link M e f) : v.adjoint.initial=v.final := by
  simp only [initial,final,adjoint,star_star]

@[simp] lemma adjoint_final (v : Link M e f) : v.adjoint.final=v.initial := by
  simp only [initial,final,adjoint,star_star]

def compFull (w : Link M f g) (v : Link M e f)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hvi : v.initial=e) (hwi : w.initial=f) : Link M e g := by
  have hi : star (w.val*v.val)*(w.val*v.val)=e := by
    rw [star_mul,mul_assoc,←mul_assoc (star w.val),←Link.initial,hwi,v.target_mul hf,←Link.initial,hvi]
  have ht : (w.val*v.val)*star (w.val*v.val)*(w.val*v.val)=w.val*v.val := by
    rw [mul_assoc,hi,mul_assoc,v.mul_source he]
  have hfin : IsStarProjection ((w.val*v.val)*star (w.val*v.val)) := by
    refine ⟨?_,IsSelfAdjoint.mul_star_self _⟩
    change ((w.val*v.val)*star (w.val*v.val))*((w.val*v.val)*star (w.val*v.val))=_
    rw [←mul_assoc,ht]
  have hle : (w.val*v.val)*star (w.val*v.val)≤w.final := by
    apply (hfin.le_iff_mul_eq_right w.final_projection).mpr
    change (w.val*star w.val)*((w.val*v.val)*star (w.val*v.val))=_
    rw [←mul_assoc,←mul_assoc,w.triple]
  exact ⟨w.val*v.val,M.mul_mem w.mem v.mem,ht,hi.le,hle.trans w.target_le⟩

@[simp] lemma compFull_initial (w : Link M f g) (v : Link M e f)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hvi : v.initial=e) (hwi : w.initial=f) :
    (w.compFull v he hf hvi hwi).initial=e := by
  change star (w.val*v.val)*(w.val*v.val)=e
  rw [star_mul,mul_assoc,←mul_assoc (star w.val),←Link.initial,hwi,v.target_mul hf,←Link.initial,hvi]

lemma compFull_final (w : Link M f g) (v : Link M e f)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hvi : v.initial=e) (hwi : w.initial=f) (hvf : v.final=f) :
    (w.compFull v he hf hvi hwi).final=w.final := by
  change (w.val*v.val)*star (w.val*v.val)=w.val*star w.val
  rw [star_mul,mul_assoc,←mul_assoc v.val,←Link.final,hvf,←mul_assoc,w.mul_source hf]

end Link

lemma subEquivalent_of_le {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hef : e≤f) : SubEquivalent M e f := by
  have hi : star e*e=e := by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  refine ⟨⟨e,heM,?_,by rw [hi],?_⟩,hi⟩
  · rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,he.isIdempotentElem.eq]
  · rwa [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]

lemma equivalent_refl {M : VonNeumannAlgebra H} {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) : Equivalent M e e := by
  
  have hi : star e*e=e := by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]
  exact ⟨⟨e,heM,by rw [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,he.isIdempotentElem.eq],
    hi.le,by simp only [he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq,le_refl]⟩,
    hi,by simp only [Link.final,he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq]⟩

lemma Equivalent.symm {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (h : Equivalent M e f) : Equivalent M f e := by
  obtain ⟨v,hi,hf⟩ := h
  exact ⟨v.adjoint,by simpa using hf,by simpa using hi⟩

lemma Equivalent.subEquivalent {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}
    (h : Equivalent M e f) : SubEquivalent M e f := by
  obtain ⟨v,hi,_⟩ := h
  exact ⟨v,hi⟩

lemma SubEquivalent.trans {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : SubEquivalent M e f) (k : SubEquivalent M f g) : SubEquivalent M e g := by
  obtain ⟨v,hv⟩ := h
  obtain ⟨w,hw⟩ := k
  exact ⟨w.compFull v he hf hv hw,w.compFull_initial v he hf hv hw⟩

lemma Equivalent.trans {M : VonNeumannAlgebra H} {e f g : H →L[ℂ] H}
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (h : Equivalent M e f) (k : Equivalent M f g) : Equivalent M e g := by
  obtain ⟨v,hvi,hvf⟩ := h
  obtain ⟨w,hwi,hwf⟩ := k
  exact ⟨w.compFull v he hf hvi hwi,w.compFull_initial v he hf hvi hwi,
    (w.compFull_final v he hf hvi hwi hvf).trans hwf⟩

lemma factor_subEquivalent_total (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) {e f : H →L[ℂ] H}
    (heM : e∈M) (hfM : f∈M) (he : IsStarProjection e) (hf : IsStarProjection f) :
    SubEquivalent M e f ∨ SubEquivalent M f e := by
  obtain ⟨v,hv⟩ := factor_comparison M hfac heM hfM he hf
  rcases hv with hv|hv
  · exact Or.inl ⟨v,hv⟩
  · exact Or.inr ⟨v.adjoint,by simpa using hv⟩

lemma finite_subEquivalent_antisymm_of_le {M : VonNeumannAlgebra H}
    (hfin : IsFiniteAlgebra M) {e f : H →L[ℂ] H}
    (hfM : f∈M) (hf : IsStarProjection f) (hef : e≤f)
    (hfe : SubEquivalent M f e) : e=f := by
  obtain ⟨v,hvi⟩ := hfe
  let w : Link M f f := ⟨v.val,v.mem,v.triple,v.source_le,v.target_le.trans hef⟩
  have hwf : w.final=f := finite_corner_cancel hfin hfM hf w hvi
  apply le_antisymm hef
  exact hwf ▸ v.target_le

end Kadison.PartialIsometryOrder

end

end
end

end OAI
