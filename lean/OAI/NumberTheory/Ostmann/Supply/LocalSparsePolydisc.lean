import OAI.NumberTheory.Ostmann.Characters.SparsePolydiscBlocks

namespace OAI

/-! # Uniform complex-parameter bound for the local sparse block -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem local_sparse_polydisc {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hp : (100 : ℝ) ≤ p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : (p : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform S b‖ ≤ ε ^ 2) :
    let E := largeTransformSpectrum (normalizedResidueTransform S)
    let T := Finset.univ \ S
    ∀ u v : ℂ, ‖u‖ ≤ 103 / 100 → ‖v‖ ≤ 103 / 100 →
      ∀ (z : ℂ) (f : ZMod p → ℂ),
        ‖polydiscSparseScalar S E (u + v) (u * v) * z +
          ∑ x, conj (polydiscSparseSide T S E (conj (u + v)) (conj (u * v)) x) * f x‖ ^ 2 +
        residueVectorNorm (fun x => z * polydiscSparseSide S T E (u + v) (u * v) x +
          polydiscSparseLower S T E (u + v) (u * v) f x) ^ 2 ≤
        (1 + 3 / (p : ℝ)) ^ 2 * (‖z‖ ^ 2 + residueVectorNorm f ^ 2) := by
  intro E T u v hu hv z f
  have hp0 : (0 : ℝ) < p := by linarith
  have hc : ‖u + v‖ ≤ (103 / 50 : ℝ) := by linarith [norm_add_le u v]
  have hd : ‖u * v‖ ≤ (10609 / 10000 : ℝ) := by
    rw [norm_mul]
    have hh := mul_le_mul hu hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 103 / 100)
    norm_num at hh ⊢
    exact hh
  obtain ⟨hz, _hn, hcard, _hconst, he, herr⟩ :=
    sparse_residue_projection S hS hSp ε hε (by linarith) hL1
  have ha := residueKernelScalar_sparse_norm_le S E hS hSp hz (17 / 20) (by norm_num)
  have hb := squareKernel_scalar_norm_le S E hS hSp hlo hhi (17 / 20) ε hε hcard
  norm_num at hb
  have hs := polydisc_scalar_norm_bounds p ε
    (residueKernelScalar S (localSparseKernel E)) (residueKernelScalar S (localSparseSquare E))
    (u + v) (u * v) hp hε hεsmall ha hb hc hd
  change (19 / 20 : ℝ) ≤ ‖polydiscSparseScalar S E (u + v) (u * v)‖ ∧
    ‖polydiscSparseScalar S E (u + v) (u * v)‖ ≤ 1 + 2 / (p : ℝ) at hs
  obtain ⟨hproj₁, hproj₂⟩ := residueProjection_side_norms S E hS hSp hz hlo hhi ε hε herr
  obtain ⟨hu₁, hu₂⟩ := balanced_uniform_norms S hS hSp hlo hhi
  have hrow := polydiscSparseSide_norm_le T S E ε hε hcard (conj (u + v)) (conj (u * v))
    (by simpa only [Complex.norm_conj] using hc) (by simpa only [Complex.norm_conj] using hd) hproj₁ hu₁
  have hcol := polydiscSparseSide_norm_le S T E ε hε hcard (u + v) (u * v) hc hd hproj₂ hu₂
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxT
    exact (Finset.mem_sdiff.mp hxT).2 hx
  have hC := polydiscSparseLower_norm_le S T E hST ε hε hεsmall hcard (u + v) (u * v) hc hd
  have hblock := residue_block_energy (polydiscSparseScalar S E (u + v) (u * v))
    (polydiscSparseSide T S E (conj (u + v)) (conj (u * v)))
    (polydiscSparseSide S T E (u + v) (u * v)) (polydiscSparseLower S T E (u + v) (u * v))
    ‖polydiscSparseScalar S E (u + v) (u * v)‖ (9 / 10) (6 * ε / Real.sqrt (p : ℝ))
    (norm_nonneg _) (by norm_num) (by linarith [hs.1]) le_rfl hrow hcol hC z f
  have hside : 20 * (6 * ε / Real.sqrt (p : ℝ)) ^ 2 ≤ 1 / (p : ℝ) := by
    rw [div_pow, Real.sq_sqrt hp0.le]
    have heq : 20 * ((6 * ε) ^ 2 / (p : ℝ)) = (720 * ε ^ 2) / p := by ring
    rw [heq]
    apply (div_le_div_iff_of_pos_right hp0).mpr
    have hsq : ε ^ 2 ≤ ε := by nlinarith
    nlinarith
  have hM : ‖polydiscSparseScalar S E (u + v) (u * v)‖ +
      20 * (6 * ε / Real.sqrt (p : ℝ)) ^ 2 ≤ 1 + 3 / (p : ℝ) := by
    have heq : 2 / (p : ℝ) + 1 / p = 3 / p := by ring
    linarith [hs.2]
  apply hblock.trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hM 2)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

end Ostmann

end OAI
