import OAI.Analysis.IrrationalRotation.Product.ProductFields
import OAI.Analysis.IrrationalRotation.Product.ProductHilbert
import Mathlib.LinearAlgebra.Dimension.Finite

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.ProductModel

theorem shiftOperator_pow (n : ℕ) :
    shiftOperator ^ n =
      (WeightedShift.shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.compLpL
        2 baseMeasure := by
  induction n with
  | zero => simpa using (WeightedShift.fieldShift_zero (μ := baseMeasure)).symm
  | succ n ih =>
    rw [pow_succ, ih]
    change _ = (WeightedShift.shift ((n : ℤ) + 1)).toLinearIsometry.toContinuousLinearMap.compLpL
      2 baseMeasure
    exact (WeightedShift.fieldShift_add (n : ℤ) 1).symm

theorem shiftOperator_pow_traceVector (n : ℕ) :
    (shiftOperator ^ n) traceVector =
      Lp.const 2 baseMeasure (lp.single 2 (n : ℤ) (1 : ℂ)) := by
  rw [shiftOperator_pow]
  apply Lp.ext
  filter_upwards [WeightedShift.fieldShift_ae (n : ℤ) traceVector,
    Lp.coeFn_const 2 baseMeasure (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber),
    Lp.coeFn_const 2 baseMeasure (lp.single 2 (n : ℤ) (1 : ℂ) : Fiber)] with x hx h0 hn
  change ((WeightedShift.shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.compLpL
    2 baseMeasure traceVector) x = _
  rw [hx, hn]
  change WeightedShift.shift (n : ℤ) ((Lp.const 2 baseMeasure
    (lp.single 2 (0 : ℤ) (1 : ℂ))) x) = _
  rw [h0]
  ext k
  change (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber) (k - n) =
    (lp.single 2 (n : ℤ) (1 : ℂ) : Fiber) k
  simp [lp.single_apply, Pi.single_apply, sub_eq_zero]

theorem linearIndependent_shiftOperator_vacuum :
    LinearIndependent ℂ (fun n : ℕ => (shiftOperator ^ n) traceVector) := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  have hb : LinearIndependent ℂ (fun n : ℕ => b (n : ℤ)) :=
    b.orthonormal.linearIndependent.comp (fun n : ℕ => (n : ℤ)) (by
      intro m n h
      change (m : ℤ) = (n : ℤ) at h
      omega)
  have hb' : LinearIndependent ℂ (fun n : ℕ => Lp.const 2 baseMeasure (b (n : ℤ))) :=
    hb.map' (HilbertModelSize.constL2Isometry (E := Fiber) baseMeasure).toLinearMap
      (LinearMap.ker_eq_bot.mpr
        (HilbertModelSize.constL2Isometry (E := Fiber) baseMeasure).injective)
  have hsingle (n : ℕ) : b (n : ℤ) = (lp.single 2 (n : ℤ) (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single b (n : ℤ)).symm
  simpa only [shiftOperator_pow_traceVector, hsingle] using hb'

theorem linearIndependent_shiftOperator_powers :
    LinearIndependent ℂ (fun n : ℕ => shiftOperator ^ n) := by
  let ev : (Hilbert →L[ℂ] Hilbert) →ₗ[ℂ] Hilbert :=
    { toFun := fun T => T traceVector
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearIndependent.of_comp ev linearIndependent_shiftOperator_vacuum

theorem factor_not_finiteDimensional (θ : ℕ → ℝ) :
    ¬ FiniteDimensional ℂ (factor θ).toStarSubalgebra := by
  intro hfinite
  let := hfinite
  have hS : shiftOperator ∈ factor θ :=
    subset_vonNeumannGenerated _ (Or.inl (Set.mem_singleton _))
  let v : ℕ → (factor θ).toStarSubalgebra :=
    fun n => ⟨shiftOperator ^ n, pow_mem hS n⟩
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (factor θ).toStarSubalgebra.toSubalgebra.val.toLinearMap
      linearIndependent_shiftOperator_powers
  exact (Module.Finite.not_linearIndependent_of_infinite v) hv

end Invariant233.ProductModel

end

end OAI
