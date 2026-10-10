import Mathlib
import OAI.Analysis.Commutator.FiniteFactorUnitary

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_factor_unitary_subequivalence (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (e f : M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (hle : τ e≤τ f) : ∃ u : unitary M,(u:M)*e*star (u:M)≤f := by
  obtain ⟨v,hvi⟩ := finite_factor_comparison M hM τ hτ hfaith e.property f.property
    (he.map M.toStarSubalgebra.subtype) (hf.map M.toStarSubalgebra.subtype) hle
  let p : M := ⟨v.final,v.final_mem⟩
  have hp : IsStarProjection p := by
    constructor
    · apply Subtype.ext
      exact v.final_projection.isIdempotentElem.eq
    · apply Subtype.ext
      exact v.final_projection.isSelfAdjoint.star_eq
  have htrace : τ e=τ p := by
    have hi : (⟨v.initial,v.initial_mem⟩:M)=e := Subtype.ext hvi
    exact (congrArg τ hi).symm.trans (v.trace_initial_final τ hτ)
  obtain ⟨u,hu⟩ := finite_factor_unitary_equivalence M hM τ hτ hfaith e p he hp htrace
  exact ⟨u,hu.le.trans v.target_le⟩

end Kadison.PartialIsometryOrder

namespace Kadison.CornerTransport

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [CStarAlgebra B]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma conjugate_corner (e f : A) (he : IsStarProjection e) (hf : IsStarProjection f)
    (u : unitary A) (hle : (u:A)*f*star (u:A)≤e) (z : A) (hz : f*z*f=z) :
    e*((u:A)*z*star (u:A))*e=(u:A)*z*star (u:A) := by
  have hu : star (u:A)*(u:A)=1 := u.property.1
  have hp : IsStarProjection ((u:A)*f*star (u:A)) := by
    constructor
    · calc
        _=(u:A)*f*(star (u:A)*(u:A))*f*star (u:A) := by noncomm_ring
        _=(u:A)*f*star (u:A) := by rw [hu,mul_one,mul_assoc (u:A) f f,hf.isIdempotentElem.eq]
    · change star ((u:A)*f*star (u:A))=(u:A)*f*star (u:A)
      simp only [star_mul,star_star,hf.isSelfAdjoint.star_eq,mul_assoc]
  have hleft := (hp.le_iff_mul_eq_right he).mp hle
  have hef : e*(u:A)*f=(u:A)*f := by
    have h := congrArg (fun x : A => x*(u:A)) hleft
    simpa only [mul_assoc,hu,mul_one] using h
  have hfue : f*star (u:A)*e=f*star (u:A) := by
    simpa only [star_mul,he.isSelfAdjoint.star_eq,hf.isSelfAdjoint.star_eq,mul_assoc] using congrArg star hef
  calc
    _=e*((u:A)*(f*z*f)*star (u:A))*e := by rw [hz]
    _=(e*(u:A)*f)*z*(f*star (u:A)*e) := by noncomm_ring
    _=((u:A)*f)*z*(f*star (u:A)) := by rw [hef,hfue]
    _=(u:A)*(f*z*f)*star (u:A) := by noncomm_ring
    _=(u:A)*z*star (u:A) := by rw [hz]

omit [PartialOrder A] [StarOrderedRing A] in
lemma bound_under_unitary (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (T : K →L[ℂ] K)
    (u : unitary A) (hTu : T*ρ (u:A)=ρ (u:A)*T)
    (hTu' : T*ρ (star (u:A))=ρ (star (u:A))*T) (z : A) {c : ℝ}
    (h : ‖T*ρ ((u:A)*z*star (u:A))-ρ ((u:A)*z*star (u:A))*T‖≤c*‖(u:A)*z*star (u:A)‖) :
    ‖T*ρ z-ρ z*T‖≤c*‖z‖ := by
  have he : T*ρ ((u:A)*z*star (u:A))-ρ ((u:A)*z*star (u:A))*T=
      ρ (u:A)*(T*ρ z-ρ z*T)*ρ (star (u:A)) := by
    simp only [map_mul]
    calc
      _=(T*ρ (u:A))*ρ z*ρ (star (u:A))-ρ (u:A)*ρ z*(ρ (star (u:A))*T) := by noncomm_ring
      _=(ρ (u:A)*T)*ρ z*ρ (star (u:A))-ρ (u:A)*ρ z*(T*ρ (star (u:A))) := by rw [hTu,←hTu']
      _=_ := by noncomm_ring
  have hU := Unitary.map_mem ρ u.property
  have hU' := Unitary.map_mem ρ (Unitary.star_mem u.property)
  rw [he,CStarRing.norm_mul_mem_unitary _ hU',CStarRing.norm_mem_unitary_mul _ hU,
    CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem u.property),CStarRing.norm_mem_unitary_mul _ u.property] at h
  exact h

end Kadison.CornerTransport

end

end
end

end OAI
