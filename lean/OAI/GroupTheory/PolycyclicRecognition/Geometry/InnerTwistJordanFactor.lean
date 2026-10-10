import OAI.GroupTheory.PolycyclicRecognition.Geometry.JordanInnerTwist
import OAI.GroupTheory.PolycyclicRecognition.Geometry.MultiplicativeJordanUniqueness

namespace OAI

/-! # Semisimple factors in an inner coset

Changing a nilpotent-group automorphism by inner conjugation changes its
semisimple Jordan factor by inner conjugation. The conjugating element is
constructed by the global Lang transversal.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

omit [LieRing.IsNilpotent L] in
theorem inner_normal_form_semisimple_factor (A S T V W : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) (u v : L)
    (hW : IsNilpotent (W.toLinearMap - 1))
    (hSW : Commute S.toLinearMap W.toLinearMap)
    (hv : ∀ x : L, v * (u * A (v⁻¹ * x * v) * u⁻¹) * v⁻¹ = S (W x))
    (hT : Module.End.IsSemisimple T.toLinearMap)
    (hV : IsNilpotent (V.toLinearMap - 1))
    (hTV : Commute T.toLinearMap V.toLinearMap)
    (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      T.toLinearMap * V.toLinearMap) :
    (polynomialInnerLieEquiv v).toLinearEquiv.conjRingEquiv T.toLinearMap = S.toLinearMap := by
  let e := (polynomialInnerLieEquiv v).toLinearEquiv
  have he (x : L) : e x = v * x * v⁻¹ := polynomialInnerLieEquiv_apply v x
  have hei (x : L) : e.symm x = v⁻¹ * x * v := by
    apply e.injective
    rw [e.apply_symm_apply, he]
    group
  have hh : e.conjRingEquiv ((polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap) =
      S.toLinearMap * W.toLinearMap := by
    apply LinearMap.ext
    intro x
    change e (polynomialInnerLieEquiv u (A (e.symm x))) = S (W x)
    rw [he, hei, polynomialInnerLieEquiv_apply]
    exact hv x
  have hV' : IsNilpotent (e.conjRingEquiv V.toLinearMap - 1) := by
    have h := hV.map e.conjRingEquiv
    simpa only [map_sub, map_one] using h
  have hTV' : Commute (e.conjRingEquiv T.toLinearMap) (e.conjRingEquiv V.toLinearMap) :=
    hTV.map e.conjRingEquiv.toMonoidHom
  have hprod : e.conjRingEquiv T.toLinearMap * e.conjRingEquiv V.toLinearMap =
      S.toLinearMap * W.toLinearMap := by
    rw [← map_mul, ← hu]
    exact hh
  exact multiplicative_jordan_semisimple_unique _ _ _ _
    (semisimple_conj e T.toLinearMap hT) hV' hS hW hTV' hSW hprod

theorem inner_twist_semisimple_factor (A S U T V : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (u : L) (hT : Module.End.IsSemisimple T.toLinearMap)
    (hV : IsNilpotent (V.toLinearMap - 1))
    (hTV : Commute T.toLinearMap V.toLinearMap)
    (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      T.toLinearMap * V.toLinearMap) :
    ∃ v : L, (polynomialInnerLieEquiv v).toLinearEquiv.conjRingEquiv T.toLinearMap =
      S.toLinearMap := by
  obtain ⟨v, W, hW, hSW, hv⟩ := jordan_inner_twist_normal_form A S U hS hU hSU hA u
  exact ⟨v, inner_normal_form_semisimple_factor A S T V W hS u v hW hSW hv hT hV hTV hu⟩

end PolycyclicRecognition

end

end OAI
