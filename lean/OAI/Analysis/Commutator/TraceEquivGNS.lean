import Mathlib
import OAI.Analysis.Commutator.GNSVectorUnitary

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TraceEquivGNS

open TracialGNS

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
  (htrace : ∀ a,σ (e a)=τ a)

omit [StarOrderedRing A] in
include htrace in
lemma vector_trace (a : A) : τ a=inner ℂ (vacuum σ)
    ((σ.gnsStarAlgHom.comp e.toStarAlgHom) a (vacuum σ)) := by
  rw [←htrace a]
  change σ (e a)=inner ℂ (algebraVector σ 1) (σ.gnsStarAlgHom (e a) (vacuum σ))
  rw [left_vacuum,←algebraVector_apply,inner_algebraVector,star_one,one_mul]

omit [PartialOrder A] [StarOrderedRing A] in
lemma dense_orbit : DenseRange (fun a : A => (σ.gnsStarAlgHom.comp e.toStarAlgHom) a (vacuum σ)) := by
  apply (dense_cyclic_orbit σ).mono
  rintro y ⟨b,rfl⟩
  exact ⟨e.symm b,by simp⟩

def unitary : τ.GNS ≃ₗᵢ[ℂ] σ.GNS :=
  VectorGNS.equivalence τ (σ.gnsStarAlgHom.comp e.toStarAlgHom) (vacuum σ)
    (vector_trace e τ σ htrace) (dense_orbit e σ)

lemma unitary_algebraVector (a : A) :
    unitary e τ σ htrace (algebraVector τ a)=algebraVector σ (e a) := by
  rw [unitary,VectorGNS.equivalence_algebraVector]
  exact left_vacuum σ (e a)

include e htrace in
lemma vector_unitball_closed (hc : IsClosed {x : σ.GNS | ∃ b : B,‖b‖≤1 ∧ algebraVector σ b=x}) :
    IsClosed {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x} := by
  have he : {x : τ.GNS | ∃ a : A,‖a‖≤1 ∧ algebraVector τ a=x} =
      (unitary e τ σ htrace) ⁻¹' {x : σ.GNS | ∃ b : B,‖b‖≤1 ∧ algebraVector σ b=x} := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨e a,by simpa only [StarAlgEquiv.norm_map] using ha,(unitary_algebraVector e τ σ htrace a).symm⟩
    · rintro ⟨b,hb,hbx⟩
      refine ⟨e.symm b,by simpa only [StarAlgEquiv.norm_map] using hb,?_⟩
      apply (unitary e τ σ htrace).injective
      rw [unitary_algebraVector,e.apply_symm_apply,hbx]
  rw [he]
  exact hc.preimage (unitary e τ σ htrace).continuous

end Kadison.TraceEquivGNS

end

end
end

end OAI
