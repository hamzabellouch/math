import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerRegularCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InducedTranslationCochains
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ConjugationCochains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteFinsuppHom

namespace OAI

/-! # The induced translation is a shift with a cochain conjugation twist -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2
attribute [local instance 2000] Rep.instLinear
attribute [local instance 2100] Linear.homModule

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerInducedHomEquiv (A : Rep k q.ker) [Module.Finite k[q.ker] A.ρ.asModule] :
    (Rep.ind q.ker.subtype A ⟶ Rep.leftRegular k G) ≃ₗ[k]
      (ℤ →₀ (A ⟶ Rep.leftRegular k q.ker)) :=
  (Rep.indResHomEquiv q.ker.subtype A (Rep.leftRegular k G)).trans
    ((Linear.homCongr k (Iso.refl A) (integerRestrictedRegularIso k q t ht)).trans
      (finiteFinsuppHomEquiv k q.ker ℤ A (Rep.leftRegular k q.ker)).symm)

theorem integerInducedHomEquiv_pointwise (A : Rep k q.ker)
    [Module.Finite k[q.ker] A.ρ.asModule]
    (f : Rep.ind q.ker.subtype A ⟶ Rep.leftRegular k G) (a : A) :
    (finiteFinsuppHomEquiv k q.ker ℤ A (Rep.leftRegular k q.ker)
      (integerInducedHomEquiv k q t ht A f)).hom a =
        integerRegularLinearEquiv k q t ht
          ((Rep.indResHomEquiv q.ker.subtype A (Rep.leftRegular k G) f).hom a) := by
  simp only [integerInducedHomEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem integerInducedHomEquiv_apply (A : Rep k q.ker)
    [Module.Finite k[q.ker] A.ρ.asModule]
    (f : Rep.ind q.ker.subtype A ⟶ Rep.leftRegular k G) (a : A) (j : ℤ) :
    ((integerInducedHomEquiv k q t ht A f) j).hom a =
      integerRegularLinearEquiv k q t ht
        ((Rep.indResHomEquiv q.ker.subtype A (Rep.leftRegular k G) f).hom a) j := by
  rw [← finiteFinsuppHomEquiv_apply, integerInducedHomEquiv_pointwise]

theorem inverse_conjugation_eq :
    (MulAut.conjNormal (H := q.ker) t⁻¹).symm = MulAut.conjNormal (H := q.ker) t := by
  change (MulAut.conjNormal (H := q.ker) t⁻¹)⁻¹ = _
  rw [map_inv, inv_inv]

theorem integerInducedHomEquiv_translation
    (P : ProjectiveResolution (Rep.trivial k q.ker k)) (i : ℕ)
    [Module.Finite k[q.ker] (P.complex.X i).ρ.asModule]
    (f : Rep.ind q.ker.subtype (P.complex.X i) ⟶ Rep.leftRegular k G) :
    integerInducedHomEquiv k q t ht (P.complex.X i)
        ((inducedTranslation k q.ker t P).f i ≫ f) =
      Finsupp.mapRange.linearMap ((conjugationCochainEquiv k q.ker t P).hom.f i).hom
        (bilateralTranslation k (P.complex.X i ⟶ Rep.leftRegular k q.ker)
          (Multiplicative.ofAdd 1) (integerInducedHomEquiv k q t ht (P.complex.X i) f)) := by
  apply Finsupp.ext
  intro j
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  change ((integerInducedHomEquiv k q t ht (P.complex.X i)
      ((inducedTranslation k q.ker t P).f i ≫ f)) j).hom a = _
  rw [integerInducedHomEquiv_apply, inducedTranslation_frobenius,
    integerRegularLinearEquiv_lift_action]
  change kernelConjugationLinearEquiv k q t
      (integerRegularLinearEquiv k q t ht
        ((Rep.indResHomEquiv q.ker.subtype (P.complex.X i) (Rep.leftRegular k G) f).hom
          (((conjugationResolutionLift k q.ker t P).f i).hom a)) (-1 + j)) =
    ((((conjugationCochainEquiv k q.ker t P).hom.f i).hom
      ((integerInducedHomEquiv k q t ht (P.complex.X i) f) (-1 + j))).hom a)
  rw [conjugationCochainEquiv_apply, inverse_conjugation_eq]
  exact congrArg (kernelConjugationLinearEquiv k q t)
    (integerInducedHomEquiv_apply k q t ht (P.complex.X i) f
      (((conjugationResolutionLift k q.ker t P).f i).hom a) (-1 + j)).symm

end PolycyclicRecognition

end

end OAI
