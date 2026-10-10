import OAI.Analysis.Nuclearity.PureProductIdealDetection
import OAI.Analysis.PureInfiniteness.InnerHomCompression

namespace OAI

/-! A star homomorphism on a minimal tensor product is faithful if its
kernel contains no nonzero elementary tensor. Pure-state excision detects
an elementary tensor in every nonzero kernel. -/

noncomputable section
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} {D : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NonUnitalCStarAlgebra D] [PartialOrder A] [StarOrderedRing A]
  [PartialOrder B] [StarOrderedRing B]

private def tensorHomKernel (q : MinimalTensor A B →⋆ₙₐ[ℂ] D) :
    NonunitalClosedIdeal.Ideal (MinimalTensor A B) where
  module := (starHomContinuousLinear q).ker
  mul_left a b hb := by
    change q (a * b) = 0
    change q b = 0 at hb
    rw [map_mul, hb, mul_zero]
  mul_right a b ha := by
    change q (a * b) = 0
    change q a = 0 at ha
    rw [map_mul, ha, zero_mul]
  star_mem a ha := by
    change q (star a) = 0
    change q a = 0 at ha
    rw [map_star, ha, star_zero]
  closed := (starHomContinuousLinear q).isClosed_ker

/-- No assumption of nuclearity is needed for this zero-kernel assertion. -/
theorem minimalTensor_injective_of_elementary_kernel
    (q : MinimalTensor A B →⋆ₙₐ[ℂ] D)
    (hq : ∀ a b, q (minimalElementary a b) = 0 → minimalElementary a b = 0) :
    Function.Injective q := by
  let _ : PartialOrder D := CStarAlgebra.spectralOrder _
  let _ : StarOrderedRing D := CStarAlgebra.spectralOrderedRing _
  apply (injective_iff_map_eq_zero q).mpr
  intro x hx
  apply pureProduct_zero_on_ideal (tensorHomKernel q) _ x hx
  intro f g y hy
  apply pure_product_vanishes_on_kernel q f.state g.state f.unital g.unital f.pure g.pure
    (pureProductCoefficient f g) (pureProductCoefficient_norm f g)
    (pureProductCoefficient_elementary f g) _ y hy
  intro a b _ _ hab
  rw [hq a b hab, map_zero]

end WeakPureInfiniteness

end

end OAI
