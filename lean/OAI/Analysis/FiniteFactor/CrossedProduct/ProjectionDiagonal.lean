import OAI.Analysis.FiniteFactor.CrossedProduct.ScalarCenter
import OAI.Analysis.FiniteFactor.Fiber.ProjectionDiagonal
import OAI.Analysis.FiniteFactor.CrossedProduct.OrbitNormalization
import OAI.Analysis.FiniteFactor.CrossedProduct.VacuumSeparating

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Faithfulness turns a zero diagonal almost everywhere into the zero projection. -/
theorem sourceProjection_zero_of_diagonal_zero (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hz : sourceCentralCoefficient p =ᵐ[sourceBaseMeasure] fun _ => 0) : p = 0 := by
  apply (sourceVacuumFunctional_square_eq_zero_iff θ hp).mp
  rw [hproj.isSelfAdjoint.star_eq,hproj.isIdempotentElem,sourceVacuumFunctional_fieldIntegral θ hp]
  change (∫ x, sourceCentralCoefficient p x ∂sourceBaseMeasure) = 0
  rw [integral_congr_ae hz,integral_zero]

theorem sourceProjection_one_of_diagonal_one (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hz : sourceCentralCoefficient p =ᵐ[sourceBaseMeasure] fun _ => 1) : p = 1 := by
  have hsub := sub_mem (one_mem (sourceAlgebra θ)) hp
  have hh : sourceCentralCoefficient (1-p) =ᵐ[sourceBaseMeasure] fun _ => 0 := by
    filter_upwards [sourceOperatorField_sub θ (one_mem (sourceAlgebra θ)) hp,
      sourceOperatorField_one θ,hz] with x hs h1 hz
    unfold sourceCentralCoefficient at *
    rw [hs,h1]
    change (lp.single 2 0 (1 : ℂ) : SourceFiberHilbert) 0 - sourceOperatorField p x (lp.single 2 0 (1 : ℂ)) 0 = 0
    simp [hz,lp.single_apply]
  exact (sub_eq_zero.mp (sourceProjection_zero_of_diagonal_zero θ hsub hproj.one_sub hh)).symm

/-- The diagonal's zero event is backwards invariant and its one event forwards
invariant. Both implications follow from the original invariant operator. -/
theorem sourceProjection_diagonal_rotation_implications
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (sourceCentralCoefficient p (coordinateRotate θ 1 x) = 0 → sourceCentralCoefficient p x = 0) ∧
      (sourceCentralCoefficient p x = 1 → sourceCentralCoefficient p (coordinateRotate θ 1 x) = 1) := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hw := sourceOperatorField_sourceOperator_pow θ hθ 1
  simp only [pow_one,Nat.cast_one] at hw
  filter_upwards [sourceOperatorField_projection θ hp hproj,
    (coordinateRotate_preserving θ 1).quasiMeasurePreserving.ae (sourceOperatorField_projection θ hp hproj),
    sourceOperatorField_invariant θ hp (staged_sourceOperator_mem θ hθ) hinv,
    sourceOperatorField_covariance θ hp,hw] with x hpx hqx hi hc hw
  let P := sourceOperatorField p x
  let Q := sourceOperatorField p (coordinateRotate θ 1 x)
  let D := fiberShift (-1) * sourceOperatorField T x
  have hcov : fiberShift (-1)*P = Q*fiberShift (-1) :=
    fiber_covariance_operator P Q 1 (fun k m => hc 1 m k)
  have hrot : (1-Q)*D*P = 0 := fiber_rotated_invariant P Q _ 1 hcov hi
  have hd (v : SourceFiberHilbert) (k : ℤ) : D v k =
      (sourceCocycle θ sourceLogWeight 1 (coordinateRotate θ k x) : ℂ) * v k := by
    change sourceOperatorField T x v (k-(-1)) = _
    rw [hw]
    simp
  let a : ℂ := sourceCocycle θ sourceLogWeight 1 (coordinateRotate θ 0 x)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (sourceCocycle_pos θ sourceLogWeight 1 (coordinateRotate θ 0 x)).ne'
  apply fiberProjection_diagonal_implications P Q D hpx hqx hrot a ha (fun v => hd v 0)
  apply Subtype.ext
  funext k
  rw [hd]
  change _ = a * (lp.single 2 0 (1 : ℂ) : SourceFiberHilbert) k
  by_cases hk : k = 0
  · subst k; rfl
  · simp [lp.single_apply,Pi.single_eq_of_ne hk]

theorem sourceProjection_strict_diagonal
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      0 < (sourceCentralCoefficient p x).re ∧ (sourceCentralCoefficient p x).re < 1 ∧
      (sourceCentralCoefficient p x).im = 0 := by
  have he := coordinateRotate_ergodic θ hr
  have hm := sourceCentralCoefficient_measurable p
  have hi := sourceProjection_diagonal_rotation_implications θ hθ hp hproj hinv
  have hn0 : ∀ᵐ x ∂sourceBaseMeasure, sourceCentralCoefficient p x ≠ 0 := by
    have hh := he.ae_empty_or_univ_of_preimage_ae_le
      (s := {x | sourceCentralCoefficient p x = 0}) (measurableSet_eq_fun hm measurable_const).nullMeasurableSet
      (hi.mono fun x hx => hx.1)
    rcases hh with hh | hh
    · filter_upwards [hh] with x hx
      change (sourceCentralCoefficient p x = 0) = False at hx
      exact fun h => (Eq.mp hx h).elim
    · exfalso
      apply hp0 (sourceProjection_zero_of_diagonal_zero θ hp hproj ?_)
      filter_upwards [hh] with x hx
      exact Eq.mpr hx trivial
  have hn1 : ∀ᵐ x ∂sourceBaseMeasure, sourceCentralCoefficient p x ≠ 1 := by
    have hh := he.ae_empty_or_univ_of_ae_le_preimage
      (s := {x | sourceCentralCoefficient p x = 1}) (measurableSet_eq_fun hm measurable_const).nullMeasurableSet
      (hi.mono fun x hx => hx.2)
    rcases hh with hh | hh
    · filter_upwards [hh] with x hx
      change (sourceCentralCoefficient p x = 1) = False at hx
      exact fun h => (Eq.mp hx h).elim
    · exfalso
      apply hp1 (sourceProjection_one_of_diagonal_one θ hp hproj ?_)
      filter_upwards [hh] with x hx
      exact Eq.mpr hx trivial
  filter_upwards [sourceOperatorField_projection θ hp hproj,hn0,hn1] with x hx h0 h1
  have hb := fiberProjection_diagonal_bounds _ hx 0
  change 0 ≤ (sourceCentralCoefficient p x).re ∧ (sourceCentralCoefficient p x).re ≤ 1 ∧
    (sourceCentralCoefficient p x).im = 0 at hb
  refine ⟨lt_of_le_of_ne hb.1 ?_,lt_of_le_of_ne hb.2.1 ?_,hb.2.2⟩
  · intro hh
    apply h0
    apply Complex.ext
    · exact hh.symm
    · exact hb.2.2
  · intro hh
    apply h1
    apply Complex.ext
    · exact hh
    · exact hb.2.2

end
end FiniteFactor

end OAI
