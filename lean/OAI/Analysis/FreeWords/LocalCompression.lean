import Mathlib
import OAI.Analysis.FreeWords.CompressionMoment
import OAI.Analysis.FreeWords.MatrixQuantizationLarge

namespace OAI

noncomputable section

namespace KKMatrixQuantization

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

theorem local_small_compression
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M)
    (x : ι → ConcreteAlgebra M) (hx : ∀ i, τ.map (x i)=0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ConcreteAlgebra M, IsStarProjection q ∧ q ≠ 0 ∧
      (τ.map q).re < ε ∧
      ∑ i, (traceNorm τ (q*x i*q))^2 < ε*(τ.map q).re := by
  classical
  let A : ℝ := ∑ i,(traceNorm τ (x i))^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let k : ℝ := Fintype.card ι
  have hk : 0 ≤ k := Nat.cast_nonneg _
  let δ : ℝ := min 1 (ε/(4*(k+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδb : δ ≤ ε/(4*(k+1)) := min_le_right _ _
  have hδk : k*δ ≤ ε/4 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 4*(k+1))).mp hδb
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_gt (2+(2*A+1)/ε)
  obtain ⟨d,hd,ρ,hρ,hNd,hsmall⟩ := matrix_commutant_quantization_large M τ hF hD x hx N δ hδ
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hNdR : (N : ℝ) ≤ d := Nat.cast_le.mpr hNd
  have hdim : 2+(2*A+1)/ε < (d : ℝ) := hN.trans_le hNdR
  have hd2 : 2 ≤ d := by
    have hfrac : 0 ≤ (2*A+1)/ε := by positivity
    have : (2 : ℝ) < d := by linarith
    exact_mod_cast this.le
  have hdA : 2*A+1 < ε*(d : ℝ) := by
    have hh : (2*A+1)/ε < (d : ℝ) := by linarith
    have hmul := (div_lt_iff₀ hε).mp hh
    nlinarith
  have hB : (∑ i,(traceNorm τ (matrixAverage ρ (x i)))^2) ≤ ε/4 := by
    calc
      _ ≤ ∑ _ : ι,δ := by
        apply Finset.sum_le_sum
        intro i hi
        have hz := traceNorm_nonneg τ (matrixAverage ρ (x i))
        have hhi := hsmall i
        nlinarith
      _ = k*δ := by simp [k]
      _ ≤ ε/4 := hδk
  have hb : (A+(d : ℝ)*∑ i,(traceNorm τ (matrixAverage ρ (x i)))^2)/
       ((d : ℝ)*((d : ℝ)+1)) < ε/(d : ℝ) := by
    apply (div_lt_iff₀ (by positivity : 0 < (d : ℝ)*((d : ℝ)+1))).mpr
    have hm : ε/(d : ℝ)*((d : ℝ)*((d : ℝ)+1))=ε*((d : ℝ)+1) := by field_simp
    rw [hm]
    have hh := mul_le_mul_of_nonneg_left hB hdR.le
    nlinarith
  let z : Fin d := ⟨0,hd⟩
  obtain ⟨U,hU⟩ := exists_rankOne_small_compression τ ρ hd2 z x ε hb
  have htrace : (τ.map (rankOne ρ z U)).re=(d : ℝ)⁻¹ := by
    rw [rankOne_trace]
    rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,Complex.ofReal_re]
  refine ⟨rankOne ρ z U,rankOne_projection ρ z U,?_,?_,?_⟩
  · intro hq
    have ht := htrace
    rw [hq,map_zero,Complex.zero_re] at ht
    exact (inv_ne_zero hdR.ne').symm ht
  · rw [htrace,← one_div]
    apply (div_lt_iff₀ hdR).mpr
    nlinarith
  · rw [htrace]
    simpa only [div_eq_mul_inv] using hU

end

end KKMatrixQuantization
end

end OAI
