import OAI.Analysis.IrrationalRotation.Model.ParameterCircleOperator
import OAI.Analysis.IrrationalRotation.Model.CompactTransfer
import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleCocycle
import OAI.Analysis.IrrationalRotation.Rotation.WeightedOrbitInvariance
import OAI.Analysis.IrrationalRotation.Rotation.RotationCenter
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Analysis.RepresentedFieldInvariance
import OAI.Analysis.IrrationalRotation.Rotation.UnrestrictedDiagonal

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Invariant233
namespace CircleParameterData

theorem weight_product_eq_floorCocycle (p : CircleParameterData) (θ : ℝ)
    (x : Circle)
    (hc : ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (n : ℕ) :
    (∏ j ∈ Finset.range n, (p.measurableWeight θ (Rotation.action θ (j : ℤ) x) : ℂ)) =
      (p.floorCocycle θ (n : ℤ) x : ℂ) := by
  induction n with
  | zero => simp [p.floorCocycle_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h := hc (n : ℤ) 1
    rw [Nat.cast_add, Nat.cast_one, h]
    change (p.floorCocycle θ n x : ℂ) *
      (p.floorCocycle θ 1 (CircleWeights.rotate θ n x) : ℂ) = _
    rw [Complex.ofReal_mul, mul_comm]

end CircleParameterData

namespace SequenceHilbert

theorem boundedDiagonal_eq_weighted (w : WeightedShift.Weight) :
    boundedDiagonal (fun k : ℤ => w k) = WeightedShift.diagonal w := by
  ext ξ k
  rw [boundedDiagonal_apply_of_bound (fun k : ℤ => w k) ‖w‖ (norm_nonneg _)
    (fun k => lp.norm_apply_le_norm (by simp) w k)]
  rfl

end SequenceHilbert

namespace CircleParameterLaws
open CircleParameterData Rotation WeightedShift
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

abbrev parameterOrbitWeight (x : Circle) : Weight :=
  Rotation.measurableOrbitWeight θ (fun z => (p.measurableWeight θ z : ℂ)) 1
    (p.measurableWeight_operator_bound θ hp) x

theorem measurableOperator_mem_algebra : p.measurableOperator θ hp ∈ Rotation.algebra θ :=
  Rotation.U_mul_measurableRepresentation_mem_algebra θ _ _ _ _ _

theorem measurableOperator_ae (ξ : Rotation.Hilbert) :
    p.measurableOperator θ hp ξ =ᵐ[circleMeasure]
      fun x => WeightedShift.operator (hp.parameterOrbitWeight x) (ξ x) := by
  filter_upwards [Rotation.U_mul_measurableRepresentation_coordinates_ae θ
    (fun z => (p.measurableWeight θ z : ℂ)) 1 (by norm_num)
    (Complex.measurable_ofReal.comp (p.measurableWeight_borel θ))
    (p.measurableWeight_operator_bound θ hp) ξ] with x hx
  exact lp.ext (funext hx)

theorem normalized_orbitProduct_eq_ratio {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    {x : Circle} (hx : x ∈ s) (n : ℕ) (v : ℤ) :
    ((p.floorCocycle θ (n : ℤ) x : ℂ)⁻¹ •
      WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n) v =
      ((p.floorCocycle θ v (Rotation.action θ (n : ℤ) x) /
        p.floorCocycle θ v x : ℝ) : ℂ) := by
  have hpord : WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n v =
      (p.floorCocycle θ (n : ℤ) (Rotation.action θ v x) : ℂ) := by
    rw [WeightedShift.orbitProduct_apply]
    have hprod := p.weight_product_eq_floorCocycle θ (Rotation.action θ v x)
      (hc _ ((hinv v x).mpr hx)) n
    convert hprod using 1
    apply Finset.prod_congr rfl
    intro j hj
    change (p.measurableWeight θ (Rotation.action θ (v + j) x) : ℂ) =
      (p.measurableWeight θ (Rotation.action θ (j : ℤ) (Rotation.action θ v x)) : ℂ)
    rw [Rotation.action_add, add_comm v]
  have hratio := CircleWeights.orbit_ratio_of_cocycle_identities θ
    p.coordFrequency p.coordCost x v (n : ℤ) (hc x hx v n) (hc x hx n v)
  change p.floorCocycle θ (n : ℤ) (Rotation.action θ v x) / p.floorCocycle θ (n : ℤ) x =
    p.floorCocycle θ v (Rotation.action θ (n : ℤ) x) / p.floorCocycle θ v x at hratio
  change (p.floorCocycle θ (n : ℤ) x : ℂ)⁻¹ *
    WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n v = _
  rw [hpord, ← hratio, Complex.ofReal_div]
  simp only [div_eq_mul_inv, mul_comm]

theorem positive_orbit_identity_of_fiber {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (P : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    {x : Circle} (hx : x ∈ s) (hP : IsIdempotentElem (P x))
    (hT : (1 - P x) * WeightedShift.operator (hp.parameterOrbitWeight x) * P x = 0)
    (n : ℕ)
    (hcov : P (Rotation.action θ (n : ℤ) x) =
      (WeightedShift.shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * P x *
        (WeightedShift.shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) :
    (1 - P (Rotation.action θ (n : ℤ) x)) *
      ratioDiagonal (p.floorCocycle θ) (x, Rotation.action θ (n : ℤ) x) * P x = 0 := by
  let w : Weight := (p.floorCocycle θ (n : ℤ) x : ℂ)⁻¹ •
    WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n
  have hd : ratioDiagonal (p.floorCocycle θ) (x, Rotation.action θ (n : ℤ) x) =
      WeightedShift.diagonal w := by
    unfold ratioDiagonal
    rw [SequenceHilbert.boundedDiagonal_congr
      (fun v => (hp.normalized_orbitProduct_eq_ratio hinv hc hx n v).symm)]
    exact SequenceHilbert.boundedDiagonal_eq_weighted w
  rw [hd, hcov]
  exact OrbitInvariance.weighted_shift_orbit_normalized
    (hp.parameterOrbitWeight x) hP hT n (p.floorCocycle θ (n : ℤ) x : ℂ)

end CircleParameterLaws
end Invariant233

namespace Invariant233.Rotation

theorem ae_field_conjugation_of_mem_algebra {θ : ℝ}
    {P : Hilbert →L[ℂ] Hilbert} (hP : P ∈ algebra θ)
    (F : Circle → Fiber →L[ℂ] Fiber)
    (hrep : ∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, F (action θ k x) =
      (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap * F x *
        (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap := by
  apply ae_all_iff.mpr
  intro k
  have hc := DirectIntegral.ae_covariance_of_represented_commute
    (default : HilbertBasis ℤ ℂ Fiber) P F
    (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap
    (action θ k) (action_measurePreserving θ k) hrep
    (algebra_commutes_shiftedPullback_int_independent θ k hP)
  have hS : (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
      (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap = 1 := by
    ext ξ i
    simp [WeightedShift.shift_apply]
  filter_upwards [hc] with x hx
  calc
    F (action θ k x) = 1 * F (action θ k x) := (one_mul _).symm
    _ = ((WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
        (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) *
          F (action θ k x) := by rw [hS]
    _ = (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
        ((WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap *
          F (action θ k x)) := mul_assoc _ _ _
    _ = (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
        (F x * (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) := by rw [hx]
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_projection_field {θ : ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hmem : P ∈ algebra θ) (hP : IsStarProjection P) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ᵐ x ∂circleMeasure, ∀ k : ℤ, F (action θ k x) =
        (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) := by
  classical
  obtain ⟨G, hnorm, hmeas, hrep, _, _, _, hproj⟩ :=
    L2Multiplication.scalar_multiplier_fields_complete
      (default : HilbertBasis ℤ ℂ Fiber) P (algebra_commutes_multiplier θ hmem)
  obtain ⟨N, hsub, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp (hproj hP))
  let F : Circle → Fiber →L[ℂ] Fiber := fun x => if x ∈ N then 0 else G x
  have hgood : ∀ x, x ∉ N → IsStarProjection (G x) := by
    intro x hx
    by_contra h
    exact hx (hsub h)
  have hnotN : ∀ᵐ x ∂circleMeasure, x ∉ N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNzero
  have heq : F =ᵐ[circleMeasure] G := by
    filter_upwards [hnotN] with x hx
    simp only [F, ite_eq_right hx]
  have hFrep : ∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x) := by
    intro ξ
    filter_upwards [hrep ξ, heq] with x hx hg
    rw [hg]
    exact hx
  refine ⟨F, ?_, ?_, ?_, hFrep,
    ae_field_conjugation_of_mem_algebra hmem F hFrep⟩
  · intro x
    by_cases hx : x ∈ N
    · simp only [F, ite_eq_left hx]
      exact IsStarProjection.zero _
    · simpa only [F, ite_eq_right hx] using hgood x hx
  · intro x
    by_cases hx : x ∈ N
    · simpa only [F, ite_eq_left hx, norm_zero] using norm_nonneg P
    · simpa only [F, ite_eq_right hx] using hnorm x
  · intro v
    have he : (fun x => F x v) = N.piecewise (fun _ => (0 : Fiber)) (fun x => G x v) := by
      funext x
      by_cases hx : x ∈ N <;> simp [F, hx, Set.piecewise]
    rw [he]
    exact stronglyMeasurable_const.piecewise hN (hmeas v)

end Invariant233.Rotation

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem exists_measurableOperator_positive_orbit_field
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ᵐ x ∂circleMeasure, ∀ k : ℤ, F (Rotation.action θ k x) =
        (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) ∧
      (∀ᵐ x ∂circleMeasure, ∀ n : ℕ,
        (1 - F (Rotation.action θ (n : ℤ) x)) *
          ratioDiagonal (p.floorCocycle θ) (x, Rotation.action θ (n : ℤ) x) * F x = 0) := by
  obtain ⟨F, hproj, hnorm, hmeas, hrep, hcov⟩ := Rotation.exists_projection_field hmem hP
  have hinv := DirectIntegral.ae_invariant_of_representations
    (default : HilbertBasis ℤ ℂ Rotation.Fiber) P (p.measurableOperator θ hp) F
    (fun x => WeightedShift.operator (hp.parameterOrbitWeight x)) hrep
    hp.measurableOperator_ae hT
  obtain ⟨s, _, hfull, hs, _, hc⟩ := hp.exists_parameter_cocycle_set
  refine ⟨F, hproj, hnorm, hmeas, hrep, hcov, ?_⟩
  filter_upwards [hinv, hcov, hfull] with x hix hcx hsx
  intro n
  exact hp.positive_orbit_identity_of_fiber hs hc F hsx (hproj x).isIdempotentElem
    hix n (hcx n)

end Invariant233.CircleParameterLaws

end

end OAI
