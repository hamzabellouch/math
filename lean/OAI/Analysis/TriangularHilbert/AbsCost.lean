import OAI.Analysis.TriangularHilbert.PlaneDom

namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma two_abs_hessianPairPD_le {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) :
    2 * |hessianPairPD hP K L| ≤ hessianCost P K + hessianCost P L := by
  have hp := two_hessianPairPD_le hP K L
  have hn := two_hessianPairPD_le hP (-K) L
  have hneg : hessianPairPD hP (-K) L = -hessianPairPD hP K L := by
    simp [hessianPairPD, hsReal, traceReal]
  have hc : hessianCost P (-K) = hessianCost P K := by
    rw [← hessianPairPD_self hP, ← hessianPairPD_self hP]
    simp [hessianPairPD, hsReal, traceReal]
  rw [hneg, hc] at hn
  rcases le_total 0 (hessianPairPD hP K L) with hh | hh
  · rwa [abs_of_nonneg hh]
  · rw [abs_of_nonpos hh]
    exact hn

lemma two_abs_hessianPair_le_of_projection {P Q K L : Matrix ι ι ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) (hKQ : K * Q = 0) (hQK : Q * K = 0)
    (hLQ : L * Q = 0) (hQL : Q * L = 0) (hPD : (P + Q).PosDef) :
    2 * |hessianPair P K L| ≤ hessianCost P K + hessianCost P L := by
  rw [← hessianPair_add_projection hP hQ hQQ hPQ hQP hKQ hQK hLQ hQL hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hKQ hQK hPD,
    ← hessianCost_add_projection hP hQ hQQ hPQ hQP hLQ hQL hPD,
    hessianPair_eq_PD hPD]
  exact two_abs_hessianPairPD_le hPD K L

lemma two_abs_hessianPair_weightedGram_le (B : Matrix ι ι ℂ) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (k l : ι → ℝ) :
    2 * |hessianPair (weightedGram B w) (weightedGram B k) (weightedGram B l)| ≤
      hessianCost (weightedGram B w) (weightedGram B k) +
      hessianCost (weightedGram B w) (weightedGram B l) := by
  obtain ⟨Q, hQ, hQQ, hBQ, hPD⟩ := weightedGram_kernel_projection B hw
  have hP := weightedGram_posSemidef B (fun i => (hw i).le)
  have hPQ := weightedGram_mul_eq_zero B Q w hBQ
  have hKQ := weightedGram_mul_eq_zero B Q k hBQ
  have hLQ := weightedGram_mul_eq_zero B Q l hBQ
  exact two_abs_hessianPair_le_of_projection hP hQ hQQ hPQ
    (hermitian_mul_zero_flip hP.isHermitian hQ.isHermitian hPQ) hKQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B k) hQ.isHermitian hKQ) hLQ
    (hermitian_mul_zero_flip (weightedGram_isHermitian B l) hQ.isHermitian hLQ) hPD
end
end TriangularHilbert.MatrixEnergy
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
lemma two_abs_heatMixed_le (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) :
    2 * |heatMixed A h u p σ v w z| ≤ heatCost A h u p σ v w + heatCost A h u p σ v z := by
  simp only [heatMixed, heatCost, localGram, localFirst, fixedBase, ite_eq_right hw, ite_eq_right hz]
  exact two_abs_hessianPair_weightedGram_le _ (groupWeight_pos hh _ _ p hσ) _ _
end
end TriangularHilbert.Heat
end

end OAI
