import OAI.NumberTheory.PrimePackets.PacketAlgebra

namespace OAI

/-! # A concrete subadditive length on the real special linear group

The logarithmic matrix length is symmetric under inversion and controls
small matrix displacements. It is used to construct observables with
uniform control along right root translations.
-/

noncomputable section
open Matrix Set Filter
open scoped Matrix.Norms.Operator Topology
namespace DukePrimeDegree
open PrimeDegreePackets

def matrixLogLength {n : ℕ} (g : G n) : ℝ :=
  Real.log (1+‖g.val-1‖) + Real.log (1+‖(g⁻¹).val-1‖)

lemma matrixLogLength_nonneg {n : ℕ} (g : G n) : 0 ≤ matrixLogLength g := by
  exact add_nonneg (Real.log_nonneg (by linarith [norm_nonneg (g.val-1)]))
    (Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)]))

@[simp] lemma matrixLogLength_one (n : ℕ) : matrixLogLength (1:G n) = 0 := by
  simp [matrixLogLength]

@[simp] lemma matrixLogLength_inv {n : ℕ} (g : G n) : matrixLogLength g⁻¹ = matrixLogLength g := by
  simp only [matrixLogLength,inv_inv,add_comm]

private lemma log_norm_mul_sub_one_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Real.log (1+‖A*B-1‖) ≤ Real.log (1+‖A-1‖)+Real.log (1+‖B-1‖) := by
  have he : A*B-1 = (A-1)*(B-1)+(A-1)+(B-1) := by noncomm_ring
  have hn : ‖A*B-1‖ ≤ ‖A-1‖*‖B-1‖+‖A-1‖+‖B-1‖ := by
    rw [he]
    have h₁ := norm_add_le ((A-1)*(B-1)+(A-1)) (B-1)
    have h₂ := norm_add_le ((A-1)*(B-1)) (A-1)
    have h₃ := norm_mul_le (A-1) (B-1)
    linarith
  have H := Real.log_le_log (by positivity : 0 < 1+‖A*B-1‖)
    (show 1+‖A*B-1‖ ≤ (1+‖A-1‖)*(1+‖B-1‖) by nlinarith)
  rwa [Real.log_mul (by positivity) (by positivity)] at H

lemma matrixLogLength_mul_le {n : ℕ} (g h : G n) :
    matrixLogLength (g*h) ≤ matrixLogLength g+matrixLogLength h := by
  have h₁ := log_norm_mul_sub_one_le g.val h.val
  have h₂ := log_norm_mul_sub_one_le (h⁻¹).val (g⁻¹).val
  change Real.log (1+‖g.val*h.val-1‖)+Real.log (1+‖((g*h)⁻¹).val-1‖) ≤ _
  rw [_root_.mul_inv_rev]
  change Real.log (1+‖g.val*h.val-1‖)+Real.log (1+‖(h⁻¹).val*(g⁻¹).val-1‖) ≤ _
  unfold matrixLogLength
  linarith

lemma matrixLogLength_eq_zero_iff {n : ℕ} (g : G n) : matrixLogLength g=0 ↔ g=1 := by
  constructor
  · intro hz
    by_contra hg
    have hn : 0 < ‖g.val-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro hv
      exact hg (Subtype.ext hv)))
    have hp : 0 < Real.log (1+‖g.val-1‖) := Real.log_pos (by linarith)
    have hi : 0 ≤ Real.log (1+‖(g⁻¹).val-1‖) :=
      Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)])
    unfold matrixLogLength at hz
    linarith
  · rintro rfl
    exact matrixLogLength_one n

def matrixLogGroupNorm (n : ℕ) : GroupNorm (G n) where
  toFun := matrixLogLength
  map_one' := matrixLogLength_one n
  mul_le' := matrixLogLength_mul_le
  inv' := matrixLogLength_inv
  eq_one_of_map_eq_zero' := fun g h => (matrixLogLength_eq_zero_iff g).mp h

theorem continuous_matrixLogLength (n : ℕ) : Continuous (matrixLogLength : G n → ℝ) := by
  have hinv : Continuous (fun g : G n => (g⁻¹).val) := by
    change Continuous (fun g : G n => Matrix.adjugate g.val)
    exact continuous_subtype_val.matrix_adjugate
  unfold matrixLogLength
  apply Continuous.add
  · exact (continuous_const.add (continuous_subtype_val.sub continuous_const).norm).log
      (fun g => (show 0 < 1+‖g.val-1‖ by positivity).ne')
  · exact (continuous_const.add (hinv.sub continuous_const).norm).log
      (fun g => (show 0 < 1+‖(g⁻¹).val-1‖ by positivity).ne')

lemma matrixLogLength_le_displacements {n : ℕ} (g : G n) :
    matrixLogLength g ≤ ‖g.val-1‖+‖(g⁻¹).val-1‖ := by
  have h₁ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+‖g.val-1‖)
  have h₂ := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+‖(g⁻¹).val-1‖)
  unfold matrixLogLength
  linarith

lemma norm_sub_one_lt_of_matrixLogLength_lt {n : ℕ} (g : G n) {ε : ℝ} (hε : 0 < ε)
    (h : matrixLogLength g < Real.log (1+ε)) : ‖g.val-1‖ < ε := by
  have hi : 0 ≤ Real.log (1+‖(g⁻¹).val-1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)])
  have hlog : Real.log (1+‖g.val-1‖) < Real.log (1+ε) := by
    unfold matrixLogLength at h
    linarith
  by_contra hn
  have hle : 1+ε ≤ 1+‖g.val-1‖ := by linarith
  exact (not_lt_of_ge (Real.log_le_log (by linarith) hle)) hlog

lemma norm_sub_one_le_exp_matrixLogLength {n : ℕ} (g : G n) :
    ‖g.val-1‖ ≤ Real.exp (matrixLogLength g)-1 := by
  have hi : 0 ≤ Real.log (1+‖(g⁻¹).val-1‖) :=
    Real.log_nonneg (by linarith [norm_nonneg ((g⁻¹).val-1)])
  have he := Real.exp_le_exp.mpr (show Real.log (1+‖g.val-1‖) ≤ matrixLogLength g by
    unfold matrixLogLength
    linarith)
  rw [Real.exp_log (by positivity)] at he
  linarith

theorem tendsto_one_of_matrixLogLength_tendsto_zero {α : Type*} {l : Filter α}
    {n : ℕ} (g : α → G n) (h : Tendsto (fun a => matrixLogLength (g a)) l (𝓝 0)) :
    Tendsto g l (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hp : 0 < Real.log (1+ε) := Real.log_pos (by linarith)
  filter_upwards [h.eventually (gt_mem_nhds hp)] with a ha
  rw [dist_eq_norm]
  change ‖(g a).val-1‖ < ε
  exact norm_sub_one_lt_of_matrixLogLength_lt (g a) hε ha

end DukePrimeDegree

end

end OAI
