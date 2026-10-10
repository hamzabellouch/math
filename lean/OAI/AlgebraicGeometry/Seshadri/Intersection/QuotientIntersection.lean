import Mathlib

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.LocalComparison
noncomputable section
variable {K R B : Type*} [Field K] [CommRing R] [CommRing B]
  [Algebra K R] [Algebra K B]

def principalIntersectionEquiv (π : R →ₐ[K] B) (hπ : Function.Surjective π)
    (g : R) (hg : RingHom.ker π.toRingHom = Ideal.span {g}) (f : R) :
    (R ⧸ Ideal.span {f,g}) ≃ₐ[K] (B ⧸ Ideal.span {π f}) := by
  let q := (Ideal.Quotient.mkₐ K (Ideal.span {π f})).comp π
  have hk : RingHom.ker q.toRingHom = Ideal.span {f,g} := by
    have hq : RingHom.ker q.toRingHom = (Ideal.span {π f}).comap π.toRingHom := by
      ext x
      change Ideal.Quotient.mk (Ideal.span {π f}) (π x) = 0 ↔ _
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hq]
    have he : (Ideal.span {f}).map π.toRingHom = Ideal.span {π f} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    rw [← he, Ideal.comap_map_of_surjective π.toRingHom hπ]
    change Ideal.span {f} ⊔ RingHom.ker π.toRingHom = _
    rw [hg, ← Ideal.span_union]
    congr 1
  exact (Ideal.quotientEquivAlgOfEq K hk.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      ((Ideal.Quotient.mk_surjective).comp hπ))
end
end MaximalSeshadri.LocalComparison
end


end
end

end OAI
