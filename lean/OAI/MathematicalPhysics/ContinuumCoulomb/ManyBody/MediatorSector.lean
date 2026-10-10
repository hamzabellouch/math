import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorBlocks
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardFermionSpectrum

namespace OAI

/-! The singlet and excited mediator coordinates form the full spin space. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorLowInclusion_apply (n r : ℕ) (p : MediatorLowSpace n)
    (s : SourceSpinBasis n) (a : MediatorBasis r) :
    mediatorLowInclusion n r p (s, a) = if a = mediatorVacuum r then p s else 0 := by
  classical
  by_cases ha : a = mediatorVacuum r
  · subst a
    simpa only [ite_true, mediatorLowInclusion, mediatorLowIndex] using HubbardGlobal.coordinateInclusion_apply_image
      (mediatorLowIndex n r) (mediatorLowIndex_injective n r) p s
  · rw [ite_eq_right ha]
    apply HubbardGlobal.coordinateInclusion_apply_outside
    intro t ht
    exact ha (congrArg (fun x : MediatedSpinBasis n r => x.2) ht).symm

theorem mediatorHighInclusion_apply (n r : ℕ) (q : MediatorHighSpace n r)
    (s : SourceSpinBasis n) (a : MediatorHighBasis r) :
    mediatorHighInclusion n r q (s, a.val) = q (s, a) :=
  HubbardGlobal.coordinateInclusion_apply_image (mediatorHighIndex n r)
    (mediatorHighIndex_injective n r) q (s, a)

theorem mediatorHighInclusion_vacuum (n r : ℕ) (q : MediatorHighSpace n r)
    (s : SourceSpinBasis n) : mediatorHighInclusion n r q (s, mediatorVacuum r) = 0 := by
  apply HubbardGlobal.coordinateInclusion_apply_outside
  intro t ht
  exact t.2.property (congrArg (fun x : MediatedSpinBasis n r => x.2) ht)

@[simp] theorem mediatorLowRestriction_apply (n r : ℕ) (x : MediatorFullSpace n r)
    (s : SourceSpinBasis n) : mediatorLowRestriction n r x s = x (s, mediatorVacuum r) :=
  HubbardGlobal.coordinateRestriction_apply _ x s

@[simp] theorem mediatorHighRestriction_apply (n r : ℕ) (x : MediatorFullSpace n r)
    (s : SourceSpinBasis n × MediatorHighBasis r) :
    mediatorHighRestriction n r x s = x (s.1, s.2.val) :=
  HubbardGlobal.coordinateRestriction_apply _ x s

@[simp] theorem mediatorLowRestriction_inclusion (n r : ℕ) (p : MediatorLowSpace n) :
    mediatorLowRestriction n r (mediatorLowInclusion n r p) = p :=
  HubbardGlobal.coordinateRestriction_inclusion _ (mediatorLowIndex_injective n r) p

@[simp] theorem mediatorHighRestriction_inclusion (n r : ℕ) (q : MediatorHighSpace n r) :
    mediatorHighRestriction n r (mediatorHighInclusion n r q) = q :=
  HubbardGlobal.coordinateRestriction_inclusion _ (mediatorHighIndex_injective n r) q

@[simp] theorem mediatorLowRestriction_high (n r : ℕ) (q : MediatorHighSpace n r) :
    mediatorLowRestriction n r (mediatorHighInclusion n r q) = 0 := by
  ext s
  simp only [mediatorLowRestriction_apply, mediatorHighInclusion_vacuum, PiLp.zero_apply]

@[simp] theorem mediatorHighRestriction_low (n r : ℕ) (p : MediatorLowSpace n) :
    mediatorHighRestriction n r (mediatorLowInclusion n r p) = 0 := by
  ext s
  simp only [mediatorHighRestriction_apply, mediatorLowInclusion_apply,
    ite_eq_right s.2.property, PiLp.zero_apply]

/-- Every full spin state decomposes into its singlet and triplet sectors. -/
theorem mediator_full_decomposition (n r : ℕ) (x : MediatorFullSpace n r) :
    mediatorLowInclusion n r (mediatorLowRestriction n r x) +
      mediatorHighInclusion n r (mediatorHighRestriction n r x) = x := by
  classical
  ext ⟨s, a⟩
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp only [PiLp.add_apply, mediatorLowInclusion_apply, ite_true,
      mediatorLowRestriction_apply, mediatorHighInclusion_vacuum, add_zero]
  · rw [PiLp.add_apply, mediatorLowInclusion_apply, ite_eq_right ha, zero_add]
    exact (mediatorHighInclusion_apply n r _ s ⟨a, ha⟩).trans
      (mediatorHighRestriction_apply n r x (s, ⟨a, ha⟩))

theorem mediatorLow_real_inner (n r : ℕ) (p : MediatorLowSpace n) (x : MediatorFullSpace n r) :
    ⟪mediatorLowInclusion n r p, x⟫_ℝ = ⟪p, mediatorLowRestriction n r x⟫_ℝ :=
  HubbardGlobal.coordinateInclusion_real_inner _ p x

theorem mediatorHigh_real_inner (n r : ℕ) (q : MediatorHighSpace n r) (x : MediatorFullSpace n r) :
    ⟪mediatorHighInclusion n r q, x⟫_ℝ = ⟪q, mediatorHighRestriction n r x⟫_ℝ :=
  HubbardGlobal.coordinateInclusion_real_inner _ q x

theorem mediatorLowInclusion_norm_map (n r : ℕ) (p : MediatorLowSpace n) :
    ‖mediatorLowInclusion n r p‖ = ‖p‖ :=
  HubbardGlobal.coordinateInclusion_norm_map _ (mediatorLowIndex_injective n r) p

theorem mediatorHighInclusion_norm_map (n r : ℕ) (q : MediatorHighSpace n r) :
    ‖mediatorHighInclusion n r q‖ = ‖q‖ :=
  HubbardGlobal.coordinateInclusion_norm_map _ (mediatorHighIndex_injective n r) q

def assembleMediator (n r : ℕ) (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    MediatorFullSpace n r := mediatorLowInclusion n r p + mediatorHighInclusion n r q

theorem assembleMediator_norm_sq (n r : ℕ) (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    ‖assembleMediator n r p q‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  unfold assembleMediator
  rw [norm_add_sq_real, mediatorLow_real_inner, mediatorLowRestriction_high,
    inner_zero_right, mediatorLowInclusion_norm_map, mediatorHighInclusion_norm_map]
  ring

/-- The matrix vacuum compression agrees with the actual Hilbert-space block. -/
theorem mediatorLow_operator_compression (n r : ℕ)
    (M : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    (mediatorLowRestriction n r).comp
      ((spinMatrixOperator M).comp (mediatorLowInclusion n r)) =
        spinMatrixOperator (mediatorCompression n r M) := by
  classical
  ext p s
  simp only [ContinuousLinearMap.comp_apply, mediatorLowRestriction_apply,
    spinMatrixOperator_apply, Fintype.sum_prod_type, mediatorLowInclusion_apply,
    mul_ite, mul_zero]
  simp [mediatorCompression]
  rfl

@[simp] theorem spinMatrixOperator_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (x : EuclideanSpace ℂ ι) (i : ι) :
    spinMatrixOperator (Matrix.diagonal d) x i = d i * x i := by
  simp [spinMatrixOperator_apply, Matrix.diagonal_apply]

theorem liftedMediatorInverse_diagonal (n r : ℕ) (Delta : ℝ) :
    liftedMediatorInverse n r Delta =
      Matrix.diagonal (fun s : MediatedSpinBasis n r => mediatorInverseWeight r Delta s.2) := by
  unfold liftedMediatorInverse mediatorInverseMatrix
  rw [← Matrix.diagonal_one (n := SourceSpinBasis n), Matrix.diagonal_kronecker_diagonal]
  simp only [one_mul]

/-- The full inverse matrix is the actual diagonal high-sector inverse,
extended by zero on the singlet sector. -/
theorem mediatorInverse_highInclusion (n r : ℕ) (Delta : ℝ) (q : MediatorHighSpace n r) :
    spinMatrixOperator (liftedMediatorInverse n r Delta) (mediatorHighInclusion n r q) =
      mediatorHighInclusion n r (diagonalPenalty
        (fun s => (actualMediatorWeight n r Delta s)⁻¹) q) := by
  classical
  rw [liftedMediatorInverse_diagonal]
  ext ⟨s, a⟩
  rw [spinMatrixOperator_diagonal]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp only [mediatorHighInclusion_vacuum, mul_zero]
  · rw [mediatorHighInclusion_apply n r q s ⟨a, ha⟩,
      mediatorHighInclusion_apply n r _ s ⟨a, ha⟩]
    simp only [diagonalPenalty_apply, mediatorInverseWeight, ite_eq_right ha,
      actualMediatorWeight, RCLike.real_smul_eq_coe_mul]
    rfl

/-- The original Hamiltonian acts only on the original-spin coordinates. -/
theorem liftedSource_lowInclusion (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (p : MediatorLowSpace n) :
    spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))
        (mediatorLowInclusion n r p) = mediatorLowInclusion n r (spinMatrixOperator C p) := by
  classical
  ext ⟨s, a⟩
  simp only [spinMatrixOperator_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mediatorLowInclusion_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    mul_one]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp
  · simp [ha]

end ContinuumCoulomb

end

end OAI
