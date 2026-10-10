import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntegerQuotientCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BilateralDifference
import Mathlib.RepresentationTheory.Rep.Res

namespace OAI

/-! # The regular module in coordinates adapted to a cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory Representation
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2

variable (k : Type) [CommRing k] {G : Type} [Group G]
  (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)

def integerRegularLinearEquiv : k[G] ≃ₗ[k] (ℤ →₀ k[q.ker]) :=
  (MonoidAlgebra.coeffLinearEquiv k).trans
    ((Finsupp.domLCongr (integerQuotientCoordinates q t ht)).trans
      ((Finsupp.curryLinearEquiv k).trans
        (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))

@[simp] theorem integerRegularLinearEquiv_single (g : G) (a : k) :
    integerRegularLinearEquiv k q t ht (MonoidAlgebra.single g a) =
      Finsupp.single (integerQuotientHeight q g)
        (MonoidAlgebra.single (integerQuotientPart q t ht g) a) := by
  simp [integerRegularLinearEquiv, Finsupp.curryLinearEquiv, integerQuotientCoordinates]

def integerRestrictedRegularEquiv :
    (Rep.res q.ker.subtype (Rep.leftRegular k G)).ρ.Equiv
      (Rep.finsupp ℤ (Rep.leftRegular k q.ker)).ρ :=
  Representation.Equiv.mk (integerRegularLinearEquiv k q t ht) fun n => by
    apply MonoidAlgebra.lhom_ext'
    intro g
    apply LinearMap.ext_ring
    change integerRegularLinearEquiv k q t ht
        (Representation.leftRegular k G (n : G) (MonoidAlgebra.single g 1)) =
      ((Representation.leftRegular k q.ker).finsupp ℤ) n
        (integerRegularLinearEquiv k q t ht (MonoidAlgebra.single g 1))
    simp only [Representation.ofMulAction_single, smul_eq_mul,
      integerRegularLinearEquiv_single, integerQuotientHeight_mul,
      integerQuotientHeight_kernel, zero_add, integerQuotientPart_kernel_mul,
      Representation.finsupp_single]

def integerRestrictedRegularIso :
    Rep.res q.ker.subtype (Rep.leftRegular k G) ≅ Rep.finsupp ℤ (Rep.leftRegular k q.ker) :=
  Rep.mkIso (integerRestrictedRegularEquiv k q t ht)

def kernelConjugationLinearEquiv : k[q.ker] ≃ₗ[k] k[q.ker] :=
  (MonoidAlgebra.domCongr k k (MulAut.conjNormal (H := q.ker) t)).toLinearEquiv

theorem integerRegularLinearEquiv_lift_action (x : k[G]) :
    integerRegularLinearEquiv k q t ht (Representation.leftRegular k G t x) =
      Finsupp.mapRange.linearMap (kernelConjugationLinearEquiv k q t).toLinearMap
        (bilateralTranslation k k[q.ker] (Multiplicative.ofAdd 1)
          (integerRegularLinearEquiv k q t ht x)) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g a =>
      have hh : integerQuotientHeight q t = 1 := by simp [integerQuotientHeight, ht]
      simp [integerQuotientPart_lift_mul, kernelConjugationLinearEquiv, hh]

end PolycyclicRecognition

end

end OAI
