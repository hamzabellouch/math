import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators NNReal
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open scoped Matrix.Norms.Operator in

theorem eigenvalue_abs_le_rowsum (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) (hrow : ∀ i, ∑ j, |A i j| ≤ a) (i : ι) :
    |hA.eigenvalues i| ≤ a := by
  have hnorm : ‖A‖ ≤ a := by
    rw [Matrix.linfty_opNorm_def]
    have hh : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ (⟨a, ha⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i _
      apply NNReal.coe_le_coe.mp
      change (↑(∑ j, ‖A i j‖₊) : ℝ) ≤ a
      simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hrow i
    exact_mod_cast hh
  exact (spectrum.norm_le_norm_of_mem (hA.eigenvalues_mem_spectrum_real i)).trans hnorm

omit [Nonempty ι] in

theorem hermitian_upper_posSemidef (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a : ℝ) (ha : ∀ i, hA.eigenvalues i ≤ a) : (a • 1 - A).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => a - hA.eigenvalues i)).PosSemidef := by
    exact Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (ha i))
  have heq : a • 1 - A =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => a - hA.eigenvalues i)) := by
    rw [← Matrix.diagonal_sub]
    change _ = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun _ => a) - Matrix.diagonal hA.eigenvalues)
    rw [map_sub]
    have hspec : A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal hA.eigenvalues) := hA.spectral_theorem
    rw [← hspec]
    congr 1
    have hdia : Matrix.diagonal (fun _ : ι => a) = a • (1 : Matrix ι ι ℝ) := by
      ext i j
      simp [Matrix.diagonal_apply, Matrix.one_apply]
    rw [hdia, map_smul, map_one]
  rw [heq, Unitary.conjStarAlgAut_apply]
  exact hd.mul_mul_conjTranspose_same _

theorem exists_leading_of_rowsums (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (a b : ℝ) (hb : 0 ≤ b)
    (hlower : ∀ i, a ≤ ∑ j, A i j) (hupper : ∀ i, ∑ j, |A i j| ≤ b) :
    ∃ i₀, a ≤ hA.eigenvalues i₀ ∧ |hA.eigenvalues i₀| ≤ b ∧
      ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues
    Finset.univ_nonempty
  have hm : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues i₀ := fun i => hi₀ i (Finset.mem_univ i)
  refine ⟨i₀, ?_, eigenvalue_abs_le_rowsum A hA b hb hupper i₀, hm⟩
  have hpos := (hermitian_upper_posSemidef A hA (hA.eigenvalues i₀) hm).dotProduct_mulVec_nonneg (fun _ => 1)
  have heval : (star (fun _ : ι => (1 : ℝ))) ⬝ᵥ
      ((hA.eigenvalues i₀ • 1 - A) *ᵥ fun _ => 1) =
      (Fintype.card ι : ℝ) * hA.eigenvalues i₀ - ∑ i, ∑ j, A i j := by
    simp [dotProduct, Finset.sum_sub_distrib, Matrix.mulVec, Matrix.one_apply]
  rw [heval] at hpos
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hl
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith

end SharpTerminalLeave

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix InnerProductSpace

end
end

end OAI
