import OAI.InformationTheory.Entanglement.HilbertChannel

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open ContinuousLinearMap
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

lemma positive_opNorm_le_trace (b : HilbertBasis ι ℂ H) {A : H →L[ℂ] H}
    (hA : HasFinitePositiveTrace b A) : ‖A‖ ≤ hilbertTrace b A := by
  let S := CFC.sqrt A
  have hS : S.IsSymmetric := (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)).isSymmetric
  have hsum : Summable (fun i => ‖S (b i)‖^2) := by
    simpa only [S,← positive_diagonal_sqrt hA.1] using hA.2
  have ht : ∑' i, ‖S (b i)‖^2=hilbertTrace b A := by
    simp only [S,← positive_diagonal_sqrt hA.1,hilbertTrace]
  have hn : 0 ≤ hilbertTrace b A := by rw [← ht]; exact tsum_nonneg (fun i => sq_nonneg _)
  have hb (x : H) : ‖S x‖^2 ≤ hilbertTrace b A*‖x‖^2 := by
    rw [← (hilbert_parseval b (S x)).tsum_eq,← ht,← tsum_mul_right]
    apply Summable.tsum_le_tsum _ (hilbert_parseval b (S x)).summable (hsum.mul_right _)
    intro i
    have he : inner ℂ (b i) (S x)=inner ℂ (S (b i)) x := (hS _ _).symm
    rw [he]
    calc
      ‖inner ℂ (S (b i)) x‖^2 ≤ (‖S (b i)‖*‖x‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
      _ = ‖S (b i)‖^2*‖x‖^2 := mul_pow _ _ _
  have hSn : ‖S‖ ≤ Real.sqrt (hilbertTrace b A) := by
    apply S.opNorm_le_bound (Real.sqrt_nonneg _)
    intro x
    have h := hb x
    have he := Real.sq_sqrt hn
    have hx := norm_nonneg x
    have hs := Real.sqrt_nonneg (hilbertTrace b A)
    nlinarith [norm_nonneg (S x),mul_nonneg hs hx,
      mul_self_nonneg (‖S x‖-Real.sqrt (hilbertTrace b A)*‖x‖)]
  have he : S*S=A := CFC.sqrt_mul_sqrt_self A hA.1
  calc
    ‖A‖ = ‖S*S‖ := congrArg norm he.symm
    _ ≤ ‖S‖*‖S‖ := norm_mul_le S S
    _ ≤ hilbertTrace b A := by
      nlinarith [Real.sq_sqrt hn,norm_nonneg S,Real.sqrt_nonneg (hilbertTrace b A)]
lemma density_opNorm_le_one (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) :
    ‖(ρ.val : H →L[ℂ] H)‖ ≤ 1 := by
  have hp := (traceClass_positive_iff b _).mp ⟨ρ.val.property,ρ.property.1⟩
  have h := positive_opNorm_le_trace b hp
  rw [← traceClassTrace_re,ρ.property.2] at h
  simpa using h
lemma density_coefficient_bound (b : HilbertBasis ι ℂ H) (ρ : DensityOperator b) (x y : H) :
    ‖inner ℂ x ((ρ.val : H →L[ℂ] H) y)‖ ≤ ‖x‖*‖y‖ := by
  apply (norm_inner_le_norm x _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
  exact ((ρ.val : H →L[ℂ] H).le_opNorm y).trans
    (by nlinarith [density_opNorm_le_one b ρ,norm_nonneg y])

end SecretKey

end

end OAI
