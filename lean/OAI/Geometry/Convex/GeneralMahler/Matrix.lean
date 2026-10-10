import OAI.Geometry.Convex.GeneralMahler.Cone
import OAI.Geometry.Convex.GeneralMahler.Growth

namespace OAI
/-! Matrix notation and ordered Euclidean operators used in §§02--06. -/

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace ENNReal NNReal
namespace GeneralMahler
variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev op : Mat n ≃⋆ₐ[ℝ] (Rn n →L[ℝ] Rn n) := Matrix.toEuclideanCLM

def opCLE : Mat n ≃L[ℝ] (Rn n →L[ℝ] Rn n) :=
  (op (n := n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

@[simp] lemma opCLE_apply (A : Mat n) : opCLE A = op A := rfl
@[simp] lemma opCLE_symm_apply (A : Rn n →L[ℝ] Rn n) : opCLE.symm A = op.symm A := rfl

theorem op_norm (A : Mat n) : ‖op A‖ = ‖A‖ := rfl

@[fun_prop] theorem continuous_op : Continuous (@op n) :=
  opCLE.continuous

@[fun_prop] theorem continuous_op_symm : Continuous (@op n).symm :=
  opCLE.symm.continuous

lemma poly_op_apply {X : Type*} [SeminormedAddCommGroup X] {A : X → Mat n} {f : X → Rn n}
    (ha : PolyBound A) (hf : PolyBound f) :
    PolyBound (fun x => op (A x) (f x)) :=
  PolyBound.of_prod_le ha hf (fun x => (op (A x)).le_opNorm _)

lemma op_inner_adjoint (A : Mat n) (x y : Rn n) :
    ⟪op A x,y⟫ = ⟪x,op (star A) y⟫ := by
  rw [map_star]
  exact (adjoint_inner_right ..).symm

lemma op_iff_hermitian {A : Mat n} :
    A.IsHermitian ↔ ∀ x y : Rn n, ⟪op A x,y⟫ = ⟪x,op A y⟫ := by
  change star A = A ↔ _
  constructor
  · intro h x y
    rw [op_inner_adjoint, h]
  · intro h
    apply op.injective
    ext y : 1
    apply ext_inner_left ℝ
    intro x
    exact (op_inner_adjoint A x y).symm.trans (h x y)

lemma op_posSemidef_iff {A : Mat n} :
    A.PosSemidef ↔ A.IsHermitian ∧ (∀ x, 0 ≤ ⟪x,op A x⟫) := by
  rw [posSemidef_iff_dotProduct_mulVec]
  apply and_congr_right; intro hh
  constructor
  · intro h x
    rw [inner_toEuclideanCLM]
    simpa using h (WithLp.ofLp x)
  · intro h x
    specialize h (WithLp.toLp 2 x)
    rw [inner_toEuclideanCLM] at h
    simpa using h

lemma op_posDef_iff {A : Mat n} :
    A.PosDef ↔ A.IsHermitian ∧ (∀ x ≠ (0:Rn n), 0 < ⟪x,op A x⟫) := by
  rw [posDef_iff_dotProduct_mulVec]
  apply and_congr_right; intro hh
  constructor
  · intro h x hx
    rw [inner_toEuclideanCLM]
    have hn : WithLp.ofLp x ≠ 0 := by simpa
    simpa using h hn
  · intro h x hx
    specialize h (WithLp.toLp 2 x) (by simpa using hx)
    rw [inner_toEuclideanCLM] at h
    simpa using h

lemma op_order_iff {A B : Mat n} (ha : A.IsHermitian) (hb : B.IsHermitian) :
    A ≤ B ↔ ∀ x : Rn n, ⟪x,op A x⟫ ≤ ⟪x,op B x⟫ := by
  rw [Matrix.le_iff,op_posSemidef_iff]
  simp only [hb.sub ha, true_and,_root_.map_sub, _root_.sub_apply,inner_sub_right,sub_nonneg]

lemma le_one_norm (A : Mat n) (hA : A.IsHermitian) (h : ‖A‖ ≤ 1) :
    A ≤ 1 := by
  refine (op_order_iff hA (isHermitian_one)).mpr (fun x => ?_)
  have he : ‖op A x‖ ≤ ‖x‖ :=
    ((op A).le_opNorm _).trans (by
      rw [op_norm]; exact mul_le_of_le_one_left (norm_nonneg _) h)
  rw [_root_.map_one]
  change ⟪x,op A x⟫ ≤ ⟪x,x⟫
  rw [real_inner_self_eq_norm_sq]
  have hf := real_inner_le_norm x (op A x)
  nlinarith [norm_nonneg x]

/-- Realized paper expressions via clm evaluations. -/
def opPair (x y : Rn n) : Mat n →L[ℝ] ℝ :=
  (innerSL ℝ x).comp ((ContinuousLinearMap.apply ℝ (Rn n) y).comp
    opCLE.toContinuousLinearMap)
@[simp] theorem opPair_apply (A : Mat n) (x y : Rn n) :
    opPair x y A = ⟪x,op A y⟫ := rfl

theorem op_inner_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (x y : Rn n) :
    ⟪x,op (∫ t, A t ∂μ) y⟫ = ∫ t, ⟪x,op (A t) y⟫ ∂μ :=
  ((opPair x y).integral_comp_comm ha).symm

theorem integral_opPair {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (x y : Rn n) :
    Integrable (fun t => ⟪x,op (A t) y⟫) μ :=
  by
    change Integrable (⇑(opPair x y) ∘ A) μ
    exact (opPair x y).integrable_comp ha

theorem hermitian_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (hh : ∀ᵐ x ∂μ, (A x).IsHermitian) :
    (∫ x, A x ∂μ).IsHermitian := by
  apply op_iff_hermitian.mpr
  intro x y
  rw [real_inner_comm, op_inner_integral ha,op_inner_integral ha]
  apply integral_congr_ae
  filter_upwards [hh] with i hi
  rw [real_inner_comm]
  exact op_iff_hermitian.mp hi x y

theorem psd_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → Mat n}
    (ha : Integrable A μ) (hh : ∀ᵐ x ∂μ, (A x).PosSemidef) :
    (∫ x, A x ∂μ).PosSemidef := by
  apply op_posSemidef_iff.mpr
  refine ⟨hermitian_integral ha (hh.mono fun x hx => hx.1), fun v => ?_⟩
  rw [op_inner_integral ha]
  apply integral_nonneg_of_ae
  exact hh.mono fun x hx => (op_posSemidef_iff.mp hx).2 v

/-- Normalized trace over coordinates. -/
def trN (A : Mat n) := trace A / (n:ℝ)

def trL : Mat n →L[ℝ] ℝ := ((n:ℝ)⁻¹ • (Matrix.traceLinearMap _ _ _)).toContinuousLinearMap
@[simp] theorem trL_apply (A : Mat n) : trL A = trN A := by simp [trL,trN,div_eq_inv_mul]

end GeneralMahler

end

end OAI
