import OAI.Analysis.Nuclearity.PureProductFunctional

namespace OAI

/-! Product pure states detect every nonzero ideal of a minimal tensor product.
This is the zero-ideal separation step; general ideal separation still needs
the nuclear factor-image kernel formula. -/

noncomputable section
open scoped TensorProduct InnerProductSpace ComplexOrder
open UniformSpace

namespace WeakPureInfiniteness

universe u
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

@[simp] theorem pureProductEvaluation_elementary_apply
    (a : A) (b : B) (f : PureStateData A) (g : PureStateData B) :
    minimalSpatialEvaluation pureProductRepresentation (minimalElementary a b)
      (pureProductVector f g) =
      ((pureGNSRepresentation A a (pureCyclicVector f) ⊗ₜ[ℂ]
        pureGNSRepresentation B b (pureCyclicVector g) :
        pureGNSHilbert A ⊗[ℂ] pureGNSHilbert B) :
        (pureProductRepresentation (A := A) (B := B)).space) := by
  change (TensorProduct.mapL (pureGNSRepresentation A a) (pureGNSRepresentation B b)).completion
    (((pureCyclicVector f ⊗ₜ[ℂ] pureCyclicVector g :
      pureGNSHilbert A ⊗[ℂ] pureGNSHilbert B)) : Completion _) = _
  rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]

theorem pureProduct_zero_on_ideal
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (hJ : ∀ (f : PureStateData A) (g : PureStateData B) (x : MinimalTensor A B),
      x ∈ J.module → pureProductCoefficient f g x = 0) :
    ∀ x ∈ J.module, x = 0 := by
  let π := minimalSpatialEvaluation (pureProductRepresentation (A := A) (B := B))
  have hbase (y : MinimalTensor A B) (hy : y ∈ J.module)
      (f : PureStateData A) (g : PureStateData B) : π y (pureProductVector f g) = 0 := by
    have hh := hJ f g (star y * y) (J.mul_left (star y) y hy)
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [pureProductCoefficient_apply, map_mul, map_star,
      mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] using hh
  intro x hx
  have hzero : π x = 0 := by
    apply pureProduct_cyclic_total
    intro f g a b
    have hh := hbase (x * minimalElementary a b)
      (J.mul_right x (minimalElementary a b) hx) f g
    rw [map_mul, mul_apply_eq_comp] at hh
    simpa only [π, pureProductEvaluation_elementary_apply] using hh
  apply pureProductEvaluation_isometry.injective
  simpa only [map_zero] using hzero

theorem exists_pureProduct_detecting_ideal
    (J : NonunitalClosedIdeal.Ideal (MinimalTensor A B))
    (x : MinimalTensor A B) (hx : x ∈ J.module) (hne : x ≠ 0) :
    ∃ (f : PureStateData A) (g : PureStateData B) (y : MinimalTensor A B),
      y ∈ J.module ∧ pureProductCoefficient f g y ≠ 0 := by
  classical
  by_contra h
  apply hne
  apply pureProduct_zero_on_ideal J _ x hx
  intro f g y hy
  by_contra hval
  exact h ⟨f, g, y, hy, hval⟩

end WeakPureInfiniteness

end

end OAI
