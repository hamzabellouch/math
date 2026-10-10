import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RealTrace

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

def normalizer (H : Fin N → Matrix (Fin d) (Fin d) ℂ) : ℝ := ∑ i, |realTrace (H i)|

def normalizedMatrix (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (i : Fin N) :
    Matrix (Fin d) (Fin d) ℂ := (normalizer H)⁻¹ • (traceSign (H i) • H i)

lemma normalizer_nonneg (H : Fin N → Matrix (Fin d) (Fin d) ℂ) : 0 ≤ normalizer H :=
  Finset.sum_nonneg fun index _ => abs_nonneg (realTrace (H index))

lemma normalizer_pos (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ i, (H i).IsHermitian) (hr : ∀ i, (H i).rank ≤ 1) (hn : ∃ i, H i ≠ 0) :
    0 < normalizer H := by
  obtain ⟨i,hi⟩ := hn
  apply Finset.sum_pos' (fun j _ => abs_nonneg (realTrace (H j)))
  exact ⟨i,Finset.mem_univ _,abs_pos.mpr (mt (realTrace_eq_zero_iff (H i) (hH i) (hr i)).mp hi)⟩

lemma normalizedMatrix_posSemidef (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ i, (H i).IsHermitian) (hr : ∀ i, (H i).rank ≤ 1) (i : Fin N) :
    (normalizedMatrix H i).PosSemidef := by
  change ((normalizer H)⁻¹ • (traceSign (H i) • H i)).PosSemidef
  change ((((normalizer H)⁻¹ : ℝ) : ℂ) • (traceSign (H i) • H i)).PosSemidef
  exact (traceSign_smul_posSemidef (H i) (hH i) (hr i)).smul
    (by exact_mod_cast inv_nonneg.mpr (normalizer_nonneg H))

lemma normalizedMatrix_rank (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hr : ∀ i, (H i).rank ≤ 1) (i : Fin N) : (normalizedMatrix H i).rank ≤ 1 := by
  simp only [normalizedMatrix,smul_smul]
  change (((normalizer H)⁻¹*traceSign (H i) : ℝ) • H i).rank ≤ 1
  let r : ℝ := (normalizer H)⁻¹*traceSign (H i)
  change (r • H i).rank ≤ 1
  have he : r • H i = (r • (1 : Matrix (Fin d) (Fin d) ℂ))*H i := by
    rw [Matrix.smul_mul,one_mul]
  rw [he]
  exact (Matrix.rank_mul_le_right _ _).trans (hr i)

lemma normalized_trace_sum (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (hD : normalizer H ≠ 0) :
    (∑ i,realTrace (normalizedMatrix H i)) = 1 := by
  simp only [normalizedMatrix,realTrace_smul,traceSign_mul_trace,← Finset.mul_sum]
  exact inv_mul_cancel₀ hD

lemma reconstruct_matrix (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (hD : normalizer H ≠ 0) (i : Fin N) :
    normalizer H • (traceSign (H i) • normalizedMatrix H i) = H i := by
  simp only [normalizedMatrix,smul_smul]
  have hh : normalizer H * (traceSign (H i) * ((normalizer H)⁻¹ * traceSign (H i))) = 1 := by
    calc
      _ = (normalizer H*(normalizer H)⁻¹)*(traceSign (H i)*traceSign (H i)) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hD,traceSign_sq,mul_one]
  rw [hh,one_smul]

lemma normalized_square (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (i : Fin N) :
    normalizedMatrix H i*normalizedMatrix H i = ((normalizer H)⁻¹)^2 • (H i*H i) := by
  simp only [normalizedMatrix,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  congr 1
  calc
    _ = ((normalizer H)⁻¹)^2*(traceSign (H i)*traceSign (H i)) := by ring
    _ = _ := by rw [traceSign_sq,mul_one]

lemma normalized_variance (H : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    (∑ i,normalizedMatrix H i*normalizedMatrix H i) =
      ((normalizer H)⁻¹)^2 • ∑ i,H i*H i := by
  simp only [normalized_square,Finset.smul_sum]

lemma reconstruct_signed_sum (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hD : normalizer H ≠ 0) (s : Fin N → ℝ) :
    (∑ i,(s i*traceSign (H i)) • H i) = normalizer H • ∑ i,s i • normalizedMatrix H i := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [normalizedMatrix,smul_smul]
  congr 1
  field_simp [hD]

lemma normalizedMatrix_eq_zero_iff (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hD : normalizer H ≠ 0) (i : Fin N) : normalizedMatrix H i = 0 ↔ H i = 0 := by
  constructor
  · intro hi
    rw [← reconstruct_matrix H hD i,hi,smul_zero,smul_zero]
  · intro hi
    simp [normalizedMatrix,hi]

end
end CurrentKS

end OAI
