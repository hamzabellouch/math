import OAI.GroupTheory.PolycyclicRecognition.Geometry.InnerTwistJordanFactor

namespace OAI

/-! # Correcting an outer centralizer into a semisimple centralizer

When conjugation by B changes A only by an inner automorphism, B can itself
be corrected by an inner automorphism to centralize the semisimple part of A.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_centralizer_inner_correction (A S U B : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (u : L) (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap) :
    ∃ v : L, Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap)
      S.toLinearMap := by
  let T := B.symm.trans (S.trans B)
  let V := B.symm.trans (U.trans B)
  have hT : T.toLinearMap = B.toLinearEquiv.conjRingEquiv S.toLinearMap := rfl
  have hV : V.toLinearMap = B.toLinearEquiv.conjRingEquiv U.toLinearMap := rfl
  have hVnil : IsNilpotent (V.toLinearMap - 1) := by
    rw [hV]
    have hh := hU.map B.toLinearEquiv.conjRingEquiv
    simpa only [map_sub, map_one] using hh
  have hTV : Commute T.toLinearMap V.toLinearMap := by
    rw [hT, hV]
    exact hSU.map B.toLinearEquiv.conjRingEquiv.toMonoidHom
  have hprod : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      T.toLinearMap * V.toLinearMap := by
    rw [hu, hT, hV, ← map_mul, ← hA]
  obtain ⟨v, hv⟩ := inner_twist_semisimple_factor A S U T V hS hU hSU hA u
    (by rw [hT]; exact semisimple_conj B.toLinearEquiv S.toLinearMap hS) hVnil hTV hprod
  let e := (polynomialInnerLieEquiv v).toLinearEquiv
  have hpoint (x : L) : e (B (S (B.symm (e.symm x)))) = S x :=
    LinearMap.congr_fun hv x
  refine ⟨v, ?_⟩
  apply LinearMap.ext
  intro x
  have hh := hpoint (e (B x))
  rw [e.symm_apply_apply, B.symm_apply_apply] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
