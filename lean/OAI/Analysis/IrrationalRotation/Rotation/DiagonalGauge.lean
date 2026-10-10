import OAI.Analysis.IrrationalRotation.Model.DiagonalGauge
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonalConvergence
import Mathlib.Topology.Sequences

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.DiagonalGauge

@[simp] theorem weight_apply (t : Circle) (k : ℤ) : weight t k = fourier k t := rfl

@[simp] theorem fiberOperator_apply (t : Circle) (v : Fiber) (k : ℤ) :
    fiberOperator t v k = fourier k t * v k := rfl

theorem norm_weight_le (t : Circle) : ‖weight t‖ ≤ 1 := by
  apply lp.norm_le_of_forall_le zero_le_one
  intro k
  exact (Circle.norm_coe _).le

theorem norm_fiberOperator_le (t : Circle) : ‖fiberOperator t‖ ≤ 1 := by
  unfold fiberOperator WeightedShift.diagonal
  exact (lp.norm_mapCLM_le 2 _ (norm_nonneg (weight t)) _).trans (norm_weight_le t)

theorem continuous_fiberOperator_apply (v : Fiber) :
    Continuous (fun t : Circle => fiberOperator t v) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact WeightedShift.diagonal_tendsto_apply
    (a := weight) (b := weight t) (l := 𝓝 t)
    (Eventually.of_forall norm_weight_le)
    (fun k => (fourier k).continuous.continuousAt) v

@[simp] theorem fiberOperator_zero : fiberOperator 0 = 1 := by
  ext v k
  simp [fiberOperator_apply]

theorem fiberOperator_add (s t : Circle) :
    fiberOperator (s + t) = fiberOperator s * fiberOperator t := by
  ext v k
  change fourier k (s + t) * v k = fourier k s * (fourier k t * v k)
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
  ring

@[simp] theorem fiberOperator_mul_neg (t : Circle) :
    fiberOperator t * fiberOperator (-t) = 1 := by
  rw [← fiberOperator_add, add_neg_cancel, fiberOperator_zero]

@[simp] theorem fiberOperator_neg_mul (t : Circle) :
    fiberOperator (-t) * fiberOperator t = 1 := by
  rw [← fiberOperator_add, neg_add_cancel, fiberOperator_zero]

theorem norm_fiberOperator_apply (t : Circle) (v : Fiber) :
    ‖fiberOperator t v‖ = ‖v‖ := by
  apply le_antisymm
  · simpa only [one_mul] using
      (fiberOperator t).le_of_opNorm_le (norm_fiberOperator_le t) v
  · have h := (fiberOperator (-t)).le_of_opNorm_le
      (norm_fiberOperator_le (-t)) (fiberOperator t v)
    have hcancel : fiberOperator (-t) (fiberOperator t v) = v :=
      congrArg (fun A : Fiber →L[ℂ] Fiber => A v) (fiberOperator_neg_mul t)
    simpa only [hcancel, one_mul] using h

def fiberEquiv (t : Circle) : Fiber ≃ₗᵢ[ℂ] Fiber where
  toFun := fiberOperator t
  invFun := fiberOperator (-t)
  left_inv v := congrArg (fun A : Fiber →L[ℂ] Fiber => A v) (fiberOperator_neg_mul t)
  right_inv v := congrArg (fun A : Fiber →L[ℂ] Fiber => A v) (fiberOperator_mul_neg t)
  map_add' := map_add _
  map_smul' := map_smul _
  norm_map' := norm_fiberOperator_apply t

theorem fiberOperator_mem_unitary (t : Circle) :
    fiberOperator t ∈ unitary (Fiber →L[ℂ] Fiber) :=
  (Unitary.linearIsometryEquiv.symm (fiberEquiv t)).property

@[simp] theorem fiberOperator_adjoint (t : Circle) :
    (fiberOperator t).adjoint = fiberOperator (-t) := by
  change star (fiberOperator t) = fiberOperator (-t)
  calc
    star (fiberOperator t) = star (fiberOperator t) *
        (fiberOperator t * fiberOperator (-t)) := by simp
    _ = (star (fiberOperator t) * fiberOperator t) * fiberOperator (-t) :=
      (mul_assoc _ _ _).symm
    _ = fiberOperator (-t) := by
      rw [Unitary.star_mul_self_of_mem (fiberOperator_mem_unitary t), one_mul]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem fieldOperator_ae (t : Circle) (v : Lp Fiber 2 μ) :
    fieldOperator μ t v =ᵐ[μ] fun x => fiberOperator t (v x) :=
  (fiberOperator t).coeFn_compLpL v

theorem norm_fieldOperator_le (t : Circle) : ‖fieldOperator μ t‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans (norm_fiberOperator_le t)

@[simp] theorem fieldOperator_zero : fieldOperator μ 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [fieldOperator_ae μ 0 v] with x hx
  simpa only [fiberOperator_zero, one_apply_eq_self] using hx

theorem fieldOperator_add (s t : Circle) :
    fieldOperator μ (s + t) = fieldOperator μ s * fieldOperator μ t := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [fieldOperator_ae μ (s + t) v,
    fieldOperator_ae μ s (fieldOperator μ t v), fieldOperator_ae μ t v]
    with x hsum hs ht
  change fieldOperator μ (s + t) v x = fieldOperator μ s (fieldOperator μ t v) x
  rw [hsum, hs, ht, fiberOperator_add]
  rfl

@[simp] theorem fieldOperator_mul_neg (t : Circle) :
    fieldOperator μ t * fieldOperator μ (-t) = 1 := by
  rw [← fieldOperator_add, add_neg_cancel, fieldOperator_zero]

@[simp] theorem fieldOperator_neg_mul (t : Circle) :
    fieldOperator μ (-t) * fieldOperator μ t = 1 := by
  rw [← fieldOperator_add, neg_add_cancel, fieldOperator_zero]

theorem norm_fieldOperator_apply (t : Circle) (v : Lp Fiber 2 μ) :
    ‖fieldOperator μ t v‖ = ‖v‖ := by
  apply le_antisymm
  · simpa only [one_mul] using
      (fieldOperator μ t).le_of_opNorm_le (norm_fieldOperator_le μ t) v
  · have h := (fieldOperator μ (-t)).le_of_opNorm_le
      (norm_fieldOperator_le μ (-t)) (fieldOperator μ t v)
    have hcancel : fieldOperator μ (-t) (fieldOperator μ t v) = v :=
      congrArg (fun A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ => A v)
        (fieldOperator_neg_mul μ t)
    simpa only [hcancel, one_mul] using h

def fieldEquiv (t : Circle) : Lp Fiber 2 μ ≃ₗᵢ[ℂ] Lp Fiber 2 μ where
  toFun := fieldOperator μ t
  invFun := fieldOperator μ (-t)
  left_inv v := congrArg (fun A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ => A v)
    (fieldOperator_neg_mul μ t)
  right_inv v := congrArg (fun A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ => A v)
    (fieldOperator_mul_neg μ t)
  map_add' := map_add _
  map_smul' := map_smul _
  norm_map' := norm_fieldOperator_apply μ t

theorem fieldOperator_mem_unitary (t : Circle) :
    fieldOperator μ t ∈ unitary (Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) :=
  (Unitary.linearIsometryEquiv.symm (fieldEquiv μ t)).property

@[simp] theorem fieldOperator_adjoint (t : Circle) :
    (fieldOperator μ t).adjoint = fieldOperator μ (-t) := by
  change star (fieldOperator μ t) = fieldOperator μ (-t)
  calc
    star (fieldOperator μ t) = star (fieldOperator μ t) *
        (fieldOperator μ t * fieldOperator μ (-t)) := by simp
    _ = (star (fieldOperator μ t) * fieldOperator μ t) * fieldOperator μ (-t) :=
      (mul_assoc _ _ _).symm
    _ = fieldOperator μ (-t) := by
      rw [Unitary.star_mul_self_of_mem (fieldOperator_mem_unitary μ t), one_mul]

variable [IsFiniteMeasure μ]

theorem continuous_fieldOperator_apply (v : Lp Fiber 2 μ) :
    Continuous (fun t : Circle => fieldOperator μ t v) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hut
  change Tendsto (fun n => fieldOperator μ (u n) v) atTop (𝓝 (fieldOperator μ t v))
  apply WeightedShift.lp_tendsto_of_ae_of_dominated (Lp.memLp v).norm
  · intro n
    filter_upwards [fieldOperator_ae μ (u n) v] with x hx
    rw [hx]
    simpa only [one_mul] using
      (fiberOperator (u n)).le_of_opNorm_le (norm_fiberOperator_le (u n)) (v x)
  · have hall : ∀ᵐ x ∂μ, ∀ n,
        fieldOperator μ (u n) v x = fiberOperator (u n) (v x) := by
      rw [ae_all_iff]
      intro n
      exact fieldOperator_ae μ (u n) v
    filter_upwards [hall, fieldOperator_ae μ t v] with x hx ht
    simp_rw [hx, ht]
    exact (continuous_fiberOperator_apply (v x)).tendsto t |>.comp hut

theorem continuous_conjugate_apply
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (v : Lp Fiber 2 μ) :
    Continuous (fun t : Circle => conjugate μ A t v) := by
  apply InvariantProjection.continuous_apply_of_strong_continuous_of_bounded
    (continuous_fieldOperator_apply μ) (norm_fieldOperator_le μ)
  exact A.continuous.comp ((continuous_fieldOperator_apply μ v).comp continuous_neg)

omit [IsFiniteMeasure μ] in

theorem norm_conjugate_le
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (t : Circle) :
    ‖conjugate μ A t‖ ≤ ‖A‖ := by
  unfold conjugate
  calc
    ‖fieldOperator μ t * A * fieldOperator μ (-t)‖ ≤
        (‖fieldOperator μ t‖ * ‖A‖) * ‖fieldOperator μ (-t)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖A‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (norm_fieldOperator_le μ t) (norm_nonneg _))
        (norm_fieldOperator_le μ (-t)) (norm_nonneg _) (by positivity)
    _ = ‖A‖ := by ring

omit [IsFiniteMeasure μ] in
@[simp] theorem conjugate_zero (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) :
    conjugate μ A 0 = A := by
  simp [conjugate]

end Invariant233.DiagonalGauge

end

end OAI
