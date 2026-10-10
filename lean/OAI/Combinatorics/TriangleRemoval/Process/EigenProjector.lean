import Mathlib

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

namespace SharpTerminalLeave

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_trace_pow (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (r : ℕ) :
    (A ^ r).trace = ∑ i, hA.eigenvalues i ^ r := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self,
    Matrix.one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem eigenvalue_tail_of_trace (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i₀ : ι) (r : ℕ) (hr : Even r) (hr0 : r ≠ 0) (a θ : ℝ)
    (ha : 0 ≤ a) (hθ : 0 ≤ θ) (hlead : a ≤ hA.eigenvalues i₀)
    (htrace : (A ^ r).trace ≤ a ^ r + θ ^ r) :
    ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ := by
  intro i hi
  have heig : ∀ j, 0 ≤ hA.eigenvalues j ^ r := fun j => hr.pow_nonneg _
  have hsum : hA.eigenvalues i₀ ^ r + hA.eigenvalues i ^ r ≤
      ∑ j, hA.eigenvalues j ^ r := by
    calc
      _ = ∑ j ∈ ({i₀, i} : Finset ι), hA.eigenvalues j ^ r := by
        simp [Ne.symm hi]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => heig j)
  have hpow : |hA.eigenvalues i| ^ r ≤ θ ^ r := by
    rw [hr.pow_abs]
    have hlead' := pow_le_pow_left₀ ha hlead r
    rw [hermitian_trace_pow A hA r] at htrace
    linarith
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) hθ hr0).mp hpow

noncomputable def eigenProjector (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (i : ι) :
    Matrix ι ι ℝ :=
  Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i (1 : ℝ)))

theorem eigenProjector_approximation (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (i₀ : ι) (θ : ℝ) (hθ : 0 ≤ θ)
    (htail : ∀ i, i ≠ i₀ → |hA.eigenvalues i| ≤ θ) :
    ‖A - hA.eigenvalues i₀ • eigenProjector A hA i₀‖ ≤ θ := by
  have heq : A - hA.eigenvalues i₀ • eigenProjector A hA i₀ =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => if i = i₀ then 0 else hA.eigenvalues i)) := by
    conv_lhs => lhs; rw [hA.spectral_theorem]
    rw [eigenProjector, ← map_smul, ← map_sub, ← Matrix.diagonal_smul,
      Matrix.diagonal_sub]
    congr 2
    ext i
    by_cases hi : i = i₀ <;> simp [hi]
  rw [heq, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hθ).mpr
  intro i
  by_cases hi : i = i₀
  · simp [hi, hθ]
  · simpa [hi] using htail i hi

end SharpTerminalLeave

open scoped BigOperators NNReal
open Matrix

end
end

end OAI
