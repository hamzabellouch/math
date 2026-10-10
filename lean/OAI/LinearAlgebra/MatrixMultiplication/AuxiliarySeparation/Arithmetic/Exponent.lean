import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankExponent
import OAI.LinearAlgebra.MatrixMultiplication.ComplexArithmetic.Growth
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compatibility
import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent

namespace OAI

/-!
# From exact tensor rank to arithmetic complexity

This file supplies the arithmetic conversion in Section 6.2.  It uses the
existing division-free straight-line programs over `ℂ`: loading inputs and
constants is free, and each scalar addition, subtraction, or multiplication
costs one.  Correctness means matrix multiplication on every pair of inputs.

The substantive tensor estimates are separate.  Here `omega` is an alias for
the existing arithmetic exponent, and the general bridge proves
`omega ≤ exactRankExponent`.  Thus any independently established upper bound
on the exact-rank exponent gives an arithmetic bound with every positive
exponent slack.  No particular numerical upper bound is assumed or asserted.
-/

noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation

/-- The arithmetic matrix multiplication exponent over the complex numbers,
in the repository's existing scalar-operation model. -/
abbrev omega : ℝ := MatrixMultiplication.Arithmetic.omega ℂ

/-- A uniform scalar-operation bound with arbitrary positive exponent slack. -/
abbrev ArithmeticBound (τ : ℝ) : Prop :=
  MatrixMultiplication.Arithmetic.AdmissibleExponent ℂ τ

/-- The existing arithmetic exponent is itself admissible; hence its infimum
has exactly the expected upper-bound interpretation. -/
theorem arithmeticBound_iff_omega_le {τ : ℝ} :
    ArithmeticBound τ ↔ omega ≤ τ :=
  MatrixMultiplication.Arithmetic.admissibleExponent_iff_omega_le

/-- Expanded form of the arithmetic statement, including its quantifier order
and the correctness and operation cost of the resulting programs. -/
theorem arithmeticComplexity_iff_omega_le {τ : ℝ} :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n,
          P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)) ↔ omega ≤ τ :=
  arithmeticBound_iff_omega_le

/-- A finite exact decomposition gives an arithmetic bound by block
substitution, including all the scalar operations in the linear combinations,
followed by padding to arbitrary positive sizes. -/
theorem arithmeticBound_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    ArithmeticBound τ :=
  (MatrixMultiplication.Arithmetic.complex_admissibleExponent_iff τ).mpr
    (MatrixMultiplication.Foundation.Arithmetic.admissibleExponent_of_rankAtMost hn hRank hτ hR)

theorem omega_le_of_rankAtMost {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R)
    {τ : ℝ} (hτ : 2 ≤ τ) (hR : (R : ℝ) ≤ (n : ℝ) ^ τ) :
    omega ≤ τ :=
  arithmeticBound_iff_omega_le.mp (arithmeticBound_of_rankAtMost hn hRank hτ hR)

/-- The quadratic rank lower bound pays for the quadratic block-combination
overhead, including the boundary case of rank exactly `n²`. -/
theorem omega_le_logb_rank {n R : ℕ} (hn : 2 ≤ n)
    (hRank : Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R) :
    omega ≤ Real.logb (n : ℝ) (R : ℝ) := by
  have hquad : n ^ 2 ≤ R := matrixMultiplication_rank_lower (by omega) hRank
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn0 : 0 < (n : ℝ) := zero_lt_one.trans hn1
  have hR0 : 0 < (R : ℝ) := by
    have : 0 < n ^ 2 := pow_pos (by omega : 0 < n) _
    exact_mod_cast (this.trans_le hquad)
  have hτ : 2 ≤ Real.logb (n : ℝ) (R : ℝ) := by
    apply (Real.le_logb_iff_rpow_le hn1 hR0).mpr
    simpa only [Real.rpow_two, Nat.cast_pow] using
      (Nat.cast_le.mpr hquad : ((n ^ 2 : ℕ) : ℝ) ≤ (R : ℝ))
  exact omega_le_of_rankAtMost hn hRank hτ
    (Real.rpow_logb hn0 (ne_of_gt hn1) hR0).symm.le

/-- Near-optimal finite blocks suffice: no finite decomposition is required
to attain the limiting exponent. -/
theorem arithmeticBound_of_arbitrarily_close_rankBounds {τ : ℝ} (hτ : 2 ≤ τ)
    (hRank : ∀ δ : ℝ, 0 < δ → ∃ n R : ℕ, 2 ≤ n ∧
      Tensor.RankAtMost (Tensor.matrixMultiplication n n n) R ∧
        (R : ℝ) ≤ (n : ℝ) ^ (τ + δ)) : ArithmeticBound τ := by
  apply arithmeticBound_iff_omega_le.mpr
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨n, R, hn, hRank, hR⟩ := hRank δ hδ
  exact omega_le_of_rankAtMost hn hRank (by linarith) hR

/-- The arithmetic exponent is bounded by each exact finite-block exponent. -/
theorem omega_le_exactMatrixRank_logb {n : ℕ} (hn : 2 ≤ n) :
    omega ≤ Real.logb (n : ℝ) (exactMatrixRank n : ℝ) :=
  omega_le_logb_rank hn (exactMatrixRank_spec n)

/-- General exact-rank-to-arithmetic bridge.  The proof uses a lower bound for
every finite-block exponent, so it does not require attainment of the infimum. -/
theorem omega_le_exactRankExponent : omega ≤ exactRankExponent := by
  apply le_csInf exactRankExponentSet_nonempty
  rintro τ ⟨n, hn, rfl⟩
  exact omega_le_exactMatrixRank_logb hn

theorem arithmeticBound_exactRankExponent : ArithmeticBound exactRankExponent :=
  arithmeticBound_iff_omega_le.mpr omega_le_exactRankExponent

/-- Any upper bound on the exact-rank exponent gives the same arithmetic
exponent bound, with arbitrary positive slack. -/
theorem arithmeticBound_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent ≤ τ) : ArithmeticBound τ :=
  arithmeticBound_iff_omega_le.mpr (omega_le_exactRankExponent.trans hτ)

/-- Explicit epsilon-complexity conclusion from an exact-rank exponent bound. -/
theorem arithmeticComplexity_of_exactRankExponent_le {τ : ℝ}
    (hτ : exactRankExponent ≤ τ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixMultiplication.Arithmetic.MatrixAlgorithm ℂ n n n,
        P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε) :=
  arithmeticBound_of_exactRankExponent_le hτ ε hε

end MatrixMultiplication.AuxiliarySeparation

end

end OAI
