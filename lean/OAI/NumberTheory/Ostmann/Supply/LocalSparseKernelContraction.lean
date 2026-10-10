import OAI.NumberTheory.Ostmann.Characters.SparseKernelLocalBlocks
import OAI.NumberTheory.Ostmann.Characters.SparseKernelUnitFactor
import OAI.NumberTheory.Ostmann.Characters.SparseKernelScalarRange
import OAI.NumberTheory.Ostmann.Characters.SparseScalarNorm

namespace OAI

/-! # The contracting local sparse block at `(u,v)=(1,1)` -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The finite local contraction in Lemma 5.2, with the actual sparse spectrum,
actual residue vectors, and the exact nonzero-residue normalizing factor. -/
theorem local_sparse_kernel_contraction {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    let T := Finset.univ \ S
    let U := sparseKernelUnitFactor p ((E.card : ℝ) / p)
    0 < U ∧
      ((U : ℝ) : ℂ) = ((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
        (1 + localSparseKernel E x) ^ 2 ∧
      ∀ (z : ℂ) (f : ZMod p → ℂ),
        ‖localSparseScalar S E * z + ∑ x, conj (localSparseSide T S E x) * f x‖ ^ 2 +
          residueVectorNorm (fun x => z * localSparseSide S T E x + localSparseLower S T E f x) ^ 2 ≤
            (U * (1 - (8 / 5) / p)) ^ 2 * (‖z‖ ^ 2 + residueVectorNorm f ^ 2) := by
  intro E T U
  have hp0 : (0 : ℝ) < p := by linarith
  have hpNat : 1 < p := by
    have hh : (1 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
    exact_mod_cast hh
  obtain ⟨hz, hn, hc, _hconst, he, herr⟩ := sparse_residue_projection S hS hSp ε hε (by linarith) hL1
  have hratio : (E.card : ℝ) / p ≤ ε := (div_le_iff₀ hp0).mpr hc
  have hratio0 : 0 ≤ (E.card : ℝ) / p := by positivity
  have hU := sparseKernelUnitFactor_lower p ((E.card : ℝ) / p) ε (by linarith)
    hratio0 hratio hε (by linarith)
  refine ⟨sparseKernelUnitFactor_positive p _ ε hp hratio0 hratio hε hεsmall, ?_, ?_⟩
  · exact sparseKernelUnitFactor_mean E hz hn hpNat
  · intro z f
    let a₁ := residueKernelScalar S (localSparseKernel E)
    let a₂ := residueKernelScalar S (localSparseSquare E)
    have ha0 := residueKernelScalar_sparse_lower S E hS hSp hz (17 / 20) (by norm_num)
    have ha1 := residueKernelScalar_sparse_re_le S E hS hSp hz (17 / 20) ε (by norm_num) he
    change a₁.re ≤ -(17 / 20 * (1 - ε ^ 2)) / p at ha1
    have ha2 := squareKernel_scalar_norm_le S E hS hSp hlo hhi (17 / 20) ε hε hc
    change ‖a₂‖ ≤ _ at ha2
    norm_num at ha2
    have har : a₁ = (a₁.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im, a₁, localSparseKernel] using residueKernelScalar_sparse_real S E hS hSp hz (17 / 20)
    have haeq : localSparseScalar S E = ((1 + 2 * a₁.re : ℝ) : ℂ) + a₂ := by
      change 1 + 2 * a₁ + a₂ = _
      rw [har]
      push_cast
      rfl
    have has := sparse_scalar_norm_bounds p ε a₁.re a₂ hp hε hεsmall ha0 (by
      convert ha1 using 1
      ring) ha2
    rw [← haeq] at has
    obtain ⟨hproj₁, hproj₂⟩ := residueProjection_side_norms S E hS hSp hz hlo hhi ε hε herr
    obtain ⟨hu₁, hu₂⟩ := balanced_uniform_norms S hS hSp hlo hhi
    have hrow := localSparseSide_norm_le T S E ε hε hc hproj₁ hu₁
    have hcol := localSparseSide_norm_le S T E ε hε hc hproj₂ hu₂
    have hST : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro x hx hxT
      exact (Finset.mem_sdiff.mp hxT).2 hx
    have hC := localSparseLower_norm_le S T E hST ε hε hεsmall hc
    have hblock := residue_block_energy (localSparseScalar S E)
      (localSparseSide T S E) (localSparseSide S T E) (localSparseLower S T E)
      ‖localSparseScalar S E‖ (9 / 10) (6 * ε / Real.sqrt (p : ℝ))
      (norm_nonneg _) (by norm_num) (by linarith [has.1]) le_rfl hrow hcol hC z f
    have hM := sparse_kernel_numeric_margin p ε ‖localSparseScalar S E‖ U hp hε hεsmall has.2 hU
    apply hblock.trans
    apply mul_le_mul_of_nonneg_right _ (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact pow_le_pow_left₀ (by positivity) hM 2

end Ostmann

end OAI
