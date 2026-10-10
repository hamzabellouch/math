import Mathlib
import OAI.Analysis.Conductivity.Variational.NormalStretch

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Matrix Set
open scoped Matrix.Norms.Elementwise

def matrixOperator (Q : Mat3) : Coord3 →L[ℝ] Coord3 :=
  (Matrix.toLin' Q).toContinuousLinearMap

@[simp] lemma matrixOperator_apply (Q : Mat3) (v : Coord3) :
    matrixOperator Q v = Q *ᵥ v := rfl

@[simp] lemma operatorMatrix_matrixOperator (Q : Mat3) :
    operatorMatrix (matrixOperator Q) = Q := by
  simp [operatorMatrix, matrixOperator]

def rotatedDirection (Q : Mat3) (i : Fin 3) : Coord3 := Q *ᵥ Pi.single i 1

def rotatedPhase (Q : Mat3) (i : Fin 3) : Coord3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (matrixOperator Qᵀ)

lemma rotated_normalization {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (i : Fin 3) :
    rotatedPhase Q i (rotatedDirection Q i) = 1 := by
  change (Qᵀ *ᵥ (Q *ᵥ Pi.single i 1)) i = 1
  rw [Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]
  simp

lemma rotatedDirection_apply (Q : Mat3) (i j : Fin 3) :
    rotatedDirection Q i j = Q j i := by
  simp [rotatedDirection]

lemma rotatedPhase_single (Q : Mat3) (i j : Fin 3) :
    rotatedPhase Q i (Pi.single j 1) = Q j i := by
  simp [rotatedPhase, matrixOperator, Matrix.toLin'_apply]

lemma normalStretch_decomposition (i : Fin 3) (t : ℝ) :
    normalStretch i (1+t) = 1 + t • Matrix.diagonal (Pi.single i 1) := by
  ext j k
  by_cases hj : j = i <;> by_cases hk : j = k <;>
    simp_all [normalStretch]

lemma rotated_diagonal_single (Q : Mat3) (i : Fin 3) (j k : Fin 3) :
    ((Q * Matrix.diagonal (Pi.single i 1) * Qᵀ) : Mat3) j k = Q j i * Q k i := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_diagonal, Pi.single_apply, mul_ite]

lemma splitJacobian_rotated {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    (i : Fin 3) (c z : ℝ) :
    splitJacobian (rotatedDirection Q i) (rotatedPhase Q i) c z =
      Q * normalStretch i (1+c*z) * Qᵀ := by
  rw [normalStretch_decomposition, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_one, hQ.2, Matrix.mul_smul, Matrix.smul_mul]
  ext j k
  simp only [splitJacobian, operatorMatrix, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, lineShiftGradientOperator_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    rotatedPhase_single, Matrix.add_apply,
    Matrix.smul_apply, rotated_diagonal_single]
  simp only [Matrix.one_apply]
  by_cases hjk : j = k <;> simp [hjk, rotatedDirection_apply] <;> ring

lemma det_orthogonal_conjugate {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (D : Mat3) :
    (Q * D * Qᵀ).det = D.det := by
  have he := congrArg Matrix.det hQ.2
  simp only [Matrix.det_mul, Matrix.det_one] at he
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Q.det * D.det * Qᵀ.det = D.det * (Q.det * Qᵀ.det) := by ring
    _ = D.det := by rw [he, mul_one]

lemma conjugated_push {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (D B : Mat3) :
    (Q * D * Qᵀ).det⁻¹ •
      ((Q * D * Qᵀ) * (Q * B * Qᵀ) * (Q * D * Qᵀ)ᵀ) =
      Q * (D.det⁻¹ • (D * B * Dᵀ)) * Qᵀ := by
  rw [det_orthogonal_conjugate hQ]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    Q * D * Qᵀ * (Q * B * Qᵀ) * (Q * (Dᵀ * Qᵀ)) =
      Q * D * (Qᵀ * Q) * B * (Qᵀ * Q) * Dᵀ * Qᵀ := by noncomm_ring
    _ = Q * (D * B * Dᵀ) * Qᵀ := by rw [hQ.1]; simp [Matrix.mul_assoc]

lemma rotated_increment_annihilates {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    (i : Fin 3) {P M : DiagonalTriple} (hn : P i = M i) :
    ∀ v, rotatedPhase Q i ((Q * Matrix.diagonal (P-M) * Qᵀ) *ᵥ v) = 0 := by
  intro v
  change (Qᵀ *ᵥ ((Q * Matrix.diagonal (P-M) * Qᵀ) *ᵥ v)) i = 0
  rw [Matrix.mulVec_mulVec]
  have he : Qᵀ * (Q * Matrix.diagonal (P-M) * Qᵀ) = Matrix.diagonal (P-M) * Qᵀ := by
    calc
      _ = (Qᵀ * Q) * Matrix.diagonal (P-M) * Qᵀ := by noncomm_ring
      _ = _ := by rw [hQ.1, Matrix.one_mul]
  rw [he, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec_diagonal, hn]

end ScalarConductivity
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

lemma exists_two_state_primitive {θ δ : ℝ} (hδ : 0 < δ) (hδθ : δ ≤ θ)
    (hw : θ + δ ≤ 1) :
    ∃ H : SmoothScalar ℝ,
      (∀ t, (smoothDirection 1 H).val t = periodicPulse θ δ t - θ) ∧
      Function.Periodic (smoothDirection 1 H).val 1 ∧
      (∫ t in (0 : ℝ)..1, (smoothDirection 1 H).val t) = 0 ∧
      (∃ b : ℝ, ∀ t, |H.val t| ≤ b) ∧
      (∀ t, -θ ≤ (smoothDirection 1 H).val t ∧
        (smoothDirection 1 H).val t ≤ 1 - θ) := by
  let h : SmoothScalar ℝ := ⟨fun t => periodicPulse θ δ t - θ,
    (periodicPulse_smooth (hδ.le.trans hδθ) hδ).sub contDiff_const⟩
  have hp : Function.Periodic h.val 1 := by
    intro t
    change periodicPulse θ δ (t + 1) - θ = periodicPulse θ δ t - θ
    rw [show periodicPulse θ δ (t + 1) = periodicPulse θ δ t from periodicPulse_periodic θ δ t]
  have hm : (∫ t in (0 : ℝ)..1, h.val t) = 0 := by
    change (∫ t in (0 : ℝ)..1, periodicPulse θ δ t - θ) = 0
    rw [intervalIntegral.integral_sub
      ((periodicPulse_smooth (hδ.le.trans hδθ) hδ).continuous.intervalIntegrable _ _)
      intervalIntegrable_const, periodicPulse_integral (hδ.le.trans hδθ) hδ hw]
    simp
  refine ⟨meanZeroPrimitive h, ?_, by simpa using hp, by simpa using hm,
    periodic_smoothScalar_bounded _ (meanZeroPrimitive_periodic h hp hm), ?_⟩
  · intro t; rw [smoothDirection_meanZeroPrimitive]
  · intro t
    rw [smoothDirection_meanZeroPrimitive]
    change -θ ≤ periodicPulse θ δ t - θ ∧ periodicPulse θ δ t - θ ≤ 1 - θ
    obtain ⟨hl, hu⟩ := periodicPulse_bounds hδ hδθ hw t
    constructor <;> linarith

lemma exists_transition_width {θ ε M : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ θ ∧ θ + δ ≤ 1 ∧ 3 * δ ≤ 1 ∧ 4 * δ * M < ε := by
  let b := min θ (min (1-θ) (min (1/3) (ε / (4 * (|M|+1)))))
  have hb : 0 < b := by
    dsimp only [b]
    exact lt_min hθ (lt_min (by linarith) (lt_min (by norm_num) (by positivity)))
  refine ⟨b/2, half_pos hb, ?_, ?_, ?_, ?_⟩
  · exact (half_le_self hb.le).trans (min_le_left _ _)
  · have h : b ≤ 1-θ := (min_le_right θ _).trans (min_le_left (1-θ) _)
    linarith
  · have h : b ≤ 1/3 := (min_le_right θ _).trans ((min_le_right (1-θ) _).trans
      (min_le_left (1/3) _))
    linarith
  · have h : b ≤ ε / (4 * (|M|+1)) := (min_le_right θ _).trans ((min_le_right (1-θ) _).trans
      (min_le_right (1/3) _))
    have hd : 0 < 4 * (|M|+1) := by positivity
    have he := (le_div_iff₀ hd).mp h
    have ha := le_abs_self M
    nlinarith [abs_nonneg M, mul_nonneg hb.le (sub_nonneg.mpr ha)]

end ScalarConductivity

end

end OAI
