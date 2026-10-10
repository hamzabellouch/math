import OAI.NumberTheory.PiExponent.Geometry.ReducedComponentStalk
import OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

def cutQuotientEquivOfSurjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) :
    A ⧸ (RingHom.ker f ⊔ Ideal.span {a}) ≃+* B ⧸ Ideal.span {f a} := by
  let g := (Ideal.Quotient.mk (Ideal.span {f a})).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hk : RingHom.ker g = RingHom.ker f ⊔ Ideal.span {a} := by
    have he : RingHom.ker g = (Ideal.span {f a}).comap f := by
      ext b
      change Ideal.Quotient.mk (Ideal.span {f a}) (f b) = 0 ↔ f b ∈ Ideal.span {f a}
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [he]
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective f hf]
    rw [← RingHom.ker_eq_comap_bot,sup_comm]
  exact (Ideal.quotEquivOfEq hk.symm).trans (g.quotientKerEquivOfSurjective hg)

theorem cut_length_eq_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) :
    Module.length A (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) =
      Module.length B (B ⧸ Ideal.span {f a}) := by
  have hA : Module.length A (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) =
      Module.length (A ⧸ (RingHom.ker f ⊔ Ideal.span {a}))
        (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) :=
    Module.length_eq_of_surjective
      (M := A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) Ideal.Quotient.mk_surjective
  have hB : Module.length B (B ⧸ Ideal.span {f a}) =
      Module.length (B ⧸ Ideal.span {f a}) (B ⧸ Ideal.span {f a}) :=
    Module.length_eq_of_surjective
      (M := B ⧸ Ideal.span {f a}) Ideal.Quotient.mk_surjective
  exact hA.trans ((SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (cutQuotientEquivOfSurjective f hf a)).trans hB.symm)

theorem reducedComponent_cut_length (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) (a : X.presheaf.stalk (reducedComponentι X C z)) :
    Module.length (X.presheaf.stalk (reducedComponentι X C z))
      ((X.presheaf.stalk (reducedComponentι X C z)) ⧸
        ((reducedComponentStalkPrime X C z).val ⊔ Ideal.span {a})) =
      Module.length ((reducedComponent X C).presheaf.stalk z)
        (((reducedComponent X C).presheaf.stalk z) ⧸
          Ideal.span {(reducedComponentι X C).stalkMap z a}) := by
  rw [← reducedComponentι_stalkMap_ker]
  exact cut_length_eq_of_surjective ((reducedComponentι X C).stalkMap z).hom
    ((reducedComponentι X C).stalkMap_surjective z) a

end
end PiExponent.CurveCycle

end OAI
