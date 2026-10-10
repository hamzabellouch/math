import OAI.Analysis.IrrationalRotation.Model.RotationProducts
import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Spectral.RotationQuasinilpotent
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.Rotation

theorem representation_injective (θ : ℝ) : Function.Injective (representation θ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (representation_eq_zero_iff θ (a - b)).mp
  change representationStarAlgHom θ (a - b) = 0
  rw [map_sub]
  change representation θ a - representation θ b = 0
  rw [hab, sub_self]

theorem representation_norm (θ : ℝ) (a : C(Circle, ℂ)) :
    ‖representation θ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (representationStarAlgHom θ)
    (representation_injective θ) a

theorem weighted_norm (θ : ℝ) (a : C(Circle, ℂ)) :
    ‖weighted θ a‖ = ‖a‖ := by
  rw [weighted, CStarRing.norm_mem_unitary_mul _ U_mem_unitary, representation_norm]

@[simp] theorem orbitProduct_apply (θ : ℝ) (a : C(Circle, ℂ)) (n : ℕ) (x : Circle) :
    orbitProduct θ a n x = ∏ j ∈ Finset.range n, a (x + j • (θ : Circle)) := by
  simp [orbitProduct]

theorem U_pow_eq_fieldShift (n : ℕ) :
    U ^ n = (WeightedShift.shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.compLpL
      2 circleMeasure := by
  induction n with
  | zero => simpa using (WeightedShift.fieldShift_zero (μ := circleMeasure)).symm
  | succ n ih =>
    rw [pow_succ, ih]
    simpa only [Nat.cast_add, Nat.cast_one, U] using
      (WeightedShift.fieldShift_add (μ := circleMeasure) (n : ℤ) 1).symm

theorem weighted_pow_eq (θ : ℝ) (a : C(Circle, ℂ)) (n : ℕ) :
    weighted θ a ^ n = U ^ n * representation θ (orbitProduct θ a n) := by
  rw [U_pow_eq_fieldShift]
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [
    InvariantProjection.FieldPowerBounds.ae_pow_apply (weighted θ a)
      (fun x => WeightedShift.operator (orbitWeight θ a x))
      (weighted_on_vector_ae θ a) n ξ,
    WeightedShift.fieldShift_ae (n : ℤ) (representation θ (orbitProduct θ a n) ξ),
    representation_ae θ (orbitProduct θ a n) ξ] with x hpow hshift hdiag
  change ((weighted θ a ^ n) ξ) x =
    ((WeightedShift.shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.compLpL
      2 circleMeasure (representation θ (orbitProduct θ a n) ξ)) x
  rw [hpow, hshift, hdiag]
  ext k
  simp only [WeightedShift.operator_pow_apply, WeightedShift.shift_apply,
    WeightedShift.diagonal_apply, orbitWeight_apply, orbitProduct_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [action, add_zsmul, natCast_zsmul, add_assoc]

theorem weighted_pow_norm (θ : ℝ) (a : C(Circle, ℂ)) (n : ℕ) :
    ‖weighted θ a ^ n‖ = ‖orbitProduct θ a n‖ := by
  rw [weighted_pow_eq, CStarRing.norm_mem_unitary_mul _ ((unitary _).pow_mem U_mem_unitary n),
    representation_norm]

theorem weightedReal_pow_norm_eq_iSup (θ : ℝ) (f : C(Circle, ℝ))
    (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    ‖weightedReal θ f ^ n‖ =
      ⨆ x : Circle, ∏ j ∈ Finset.range n, f (x + j • (θ : Circle)) := by
  rw [weightedReal, weighted_pow_norm, ContinuousMap.norm_eq_iSup_norm]
  congr 1
  funext x
  rw [orbitProduct_apply, norm_prod]
  apply Finset.prod_congr rfl
  intro j hj
  change ‖(f (x + j • (θ : Circle)) : ℂ)‖ = f (x + j • (θ : Circle))
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf _)]

end Invariant233.Rotation

end

end OAI
