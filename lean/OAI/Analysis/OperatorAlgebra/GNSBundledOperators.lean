import OAI.Analysis.OperatorAlgebra.TracialGNSIntertwiner

namespace OAI

/-! GNS operators with the same bundled Hilbert-space structures as the inclusion.
The underlying operators are the canonical left and right GNS actions. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsBundledLeft (f : A →ₚ[ℂ] ℂ) (a : A) : gnsHilbert f →L[ℂ] gnsHilbert f :=
  f.gnsStarAlgHom a

def gnsBundledRight (f : A →ₚ[ℂ] ℂ) (ht : ∀ a b, f (a * b) = f (b * a))
    (b : A) : gnsHilbert f →L[ℂ] gnsHilbert f :=
  NuclearTrace.rightGNS f ht (MulOpposite.op b)

lemma gnsBundledLeft_vector (f : A →ₚ[ℂ] ℂ) (a b : A) :
    gnsBundledLeft f a (gnsVector f b) = gnsVector f (a * b) :=
  gnsVector_left f a b

lemma gnsBundledRight_vector (f : A →ₚ[ℂ] ℂ)
    (ht : ∀ a b, f (a * b) = f (b * a)) (a b : A) :
    gnsBundledRight f ht b (gnsVector f a) = gnsVector f (a * b) :=
  gnsVector_right f ht a b

end WeakPureInfiniteness

end

end OAI
