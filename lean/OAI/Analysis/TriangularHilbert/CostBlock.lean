import OAI.Analysis.TriangularHilbert.WeightedGram

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hessianPair_self_of_projection {P Q K : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hPD : (P + Q).PosDef) : hessianPair P K K = hessianCost P K := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hKQ hQK hPD,
    hessianPair_eq_PD hPD, hessianPairPD_self,
    hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD]

lemma two_hessianPair_le_of_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hKQ : K * Q = 0) (hQK : Q * K = 0) (hLQ : L * Q = 0) (hQL : Q * L = 0)
    (hPD : (P + Q).PosDef) :
    2 * hessianPair P K L ≤ hessianCost P K + hessianCost P L := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hLQ hQL hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hLQ hQL hPD,
    hessianPair_eq_PD hPD]
  exact two_hessianPairPD_le hPD K L

lemma hessianPair_weightedGram_self (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k : ι → ℝ) :
    hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B k) =
      hessianCost (weightedGram B w) (weightedGram B k) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  exact hessianPair_self_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hPD

lemma two_hessianPair_weightedGram_le (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k l : ι → ℝ) :
    2 * hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B l) ≤
      hessianCost (weightedGram B w) (weightedGram B k) +
      hessianCost (weightedGram B w) (weightedGram B l) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  have hLQ := weightedGram_mul_eq_zero B Q l hBQ
  exact two_hessianPair_le_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hLQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B l) hQ.isHermitian hLQ) hPD

omit [DecidableEq ι] in
lemma traceReal_blockD (P : Three → Matrix ι ι ℂ) :
    traceReal (blockD P) = ∑ v, traceReal (P v) := by
  simp [traceReal, Matrix.trace, blockD, Fintype.sum_prod_type]

omit [DecidableEq ι] in
lemma hsReal_blockD (A B : Three → Matrix ι ι ℂ) :
    hsReal (blockD A) (blockD B) = ∑ v, hsReal (A v) (B v) := by
  simp only [hsReal, blockD_star, blockD_mul, traceReal_blockD]

lemma rootCost_blockD (A K : Three → Matrix ι ι ℂ)
    (hA : ∀ v, (A v).PosSemidef)
    (hsol : ∀ v, ∃ Y, sylv (A v) Y = K v) :
    rootCost (blockD A) (blockD K) = ∑ v, rootCost (A v) (K v) := by
  choose Y hY using hsol
  have hsol' : sylv (blockD A) (blockD Y) = blockD K := by
    rw [sylv_blockD]
    congr 1
    funext v
    exact hY v
  rw [rootCost_eq_of_solution (blockD_posSemidef A hA) hsol',
    hsReal_blockD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (rootCost_eq_of_solution (hA v) (hY v)).symm

lemma hessianCost_blockD (P K : Three → Matrix ι ι ℂ)
    (hP : ∀ v, (P v).PosSemidef)
    (hsol : ∀ v, ∃ Y, sylv (CFC.sqrt (P v)) Y = K v) :
    hessianCost (blockD P) (blockD K) = ∑ v, hessianCost (P v) (K v) := by
  change rootCost (CFC.sqrt (blockD P)) (blockD K) =
    ∑ v, rootCost (CFC.sqrt (P v)) (K v)
  rw [sqrt_blockD P hP]
  exact rootCost_blockD _ K
    (fun v => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (P v))) hsol

end
end TriangularHilbert.MatrixEnergy
end

end OAI
