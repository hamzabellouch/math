import OAI.GroupTheory.PolycyclicRecognition.Geometry.RelativeJordanInnerTwist
import OAI.GroupTheory.PolycyclicRecognition.Geometry.InnerTwistJordanFactor

namespace OAI

/-! # Semisimple centralizer corrections preserving a commuting family -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem semisimple_centralizer_inner_correction_fixed {ι : Type*}
    (A S U B : L ≃ₗ⁅ℝ⁆ L) (T : ι → L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : ∀ i, Commute (T i).toLinearMap S.toLinearMap)
    (hTU : ∀ i, Commute (T i).toLinearMap U.toLinearMap)
    (u : L) (htu : ∀ i, T i u = u)
    (hu : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      B.toLinearEquiv.conjRingEquiv A.toLinearMap) :
    ∃ v : L, (∀ i, T i v = v) ∧
      Commute ((polynomialInnerLieEquiv v).toLinearMap * B.toLinearMap) S.toLinearMap := by
  obtain ⟨v, W, hW, hSW, hTv, _, hv⟩ :=
    jordan_inner_twist_normal_form_fixed A S U T hS hU hSU hA hTS hTU u htu
  let J := B.symm.trans (S.trans B)
  let V := B.symm.trans (U.trans B)
  have hJ : J.toLinearMap = B.toLinearEquiv.conjRingEquiv S.toLinearMap := rfl
  have hV : V.toLinearMap = B.toLinearEquiv.conjRingEquiv U.toLinearMap := rfl
  have hVnil : IsNilpotent (V.toLinearMap - 1) := by
    rw [hV]
    have hh := hU.map B.toLinearEquiv.conjRingEquiv
    simpa only [map_sub, map_one] using hh
  have hJV : Commute J.toLinearMap V.toLinearMap := by
    rw [hJ, hV]
    exact hSU.map B.toLinearEquiv.conjRingEquiv.toMonoidHom
  have hprod : (polynomialInnerLieEquiv u).toLinearMap * A.toLinearMap =
      J.toLinearMap * V.toLinearMap := by
    rw [hu, hJ, hV, ← map_mul, ← hA]
  have hj := inner_normal_form_semisimple_factor A S J V W hS u v hW hSW hv
    (by rw [hJ]; exact semisimple_conj B.toLinearEquiv S.toLinearMap hS) hVnil hJV hprod
  let e := (polynomialInnerLieEquiv v).toLinearEquiv
  have hpoint (x : L) : e (B (S (B.symm (e.symm x)))) = S x := LinearMap.congr_fun hj x
  refine ⟨v, hTv, ?_⟩
  apply LinearMap.ext
  intro x
  have hh := hpoint (e (B x))
  rw [e.symm_apply_apply, B.symm_apply_apply] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
