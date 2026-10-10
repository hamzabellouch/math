import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeMellinEnvelope

namespace OAI

/-! Exact quotient support for divisor-restricted prime coefficients.
No independent-prime condition is asserted for the shortened coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeSliceSupport (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e : Eisenstein) : Finset Eisenstein :=
  (primaryElementBall (R^Fintype.card ι*(∏ i, X i)/norm f)).filter
    (fun n => f*n ∈ fullSquarefreePrimeSupport R W X e)

lemma fullPrimeSliceSupport_bounds (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (f e : Eisenstein) {n : Eisenstein} (hn : n ∈ fullPrimeSliceSupport R W X f e) :
    primary n ∧ Squarefree n ∧ IsCoprime f n ∧
      norm n ≤ R^Fintype.card ι*(∏ i, X i)/norm f := by
  have hm := Finset.mem_filter.mp hn
  have hp := mem_primaryElementBall.mp hm.1
  have hs := (fullSquarefreePrimeSupport_primary R W X e hm.2).2
  exact ⟨hp.1,hs.squarefree_of_dvd (dvd_mul_left _ _),
    (IsRelPrime.of_squarefree_mul hs).isCoprime,hp.2⟩

lemma fullPrimeSliceSupport_complete {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0)
    {f : Eisenstein} (hf : primary f) (e n : Eisenstein)
    (hn : f*n ∈ fullSquarefreePrimeSupport R W X e) :
    n ∈ fullPrimeSliceSupport R W X f e := by
  have hp := fullSquarefreePrimeSupport_primary R W X e hn
  have hb := (fullPrimeProduct_norm_bounds R W X hX hlo hhi (Finset.mem_filter.mp hn).1).2
  apply Finset.mem_filter.mpr
  refine ⟨mem_primaryElementBall.mpr ⟨primary_of_mul hf hp.1,?_⟩,hn⟩
  apply (le_div_iff₀ (norm_pos_of_ne_zero (primary_ne_zero hf))).mpr
  simpa only [norm_mul_eq,mul_comm] using hb

lemma fullPrime_divisor_sum_eq_slice {R : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0)
    {f : Eisenstein} (hf : primary f) (e : Eisenstein) (A : Eisenstein → ℂ) :
    (∑ b ∈ (fullSquarefreePrimeSupport R W X e).filter (fun b => f ∣ b), A b) =
      ∑ n ∈ fullPrimeSliceSupport R W X f e, A (f*n) := by
  symm
  apply Finset.sum_bij (fun n _ => f*n)
  · intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).2,dvd_mul_right _ _⟩
  · intro n _ m _ hnm
    exact mul_left_cancel₀ (primary_ne_zero hf) hnm
  · intro b hb
    obtain ⟨n,hn⟩ := (Finset.mem_filter.mp hb).2
    refine ⟨n,?_,hn.symm⟩
    apply fullPrimeSliceSupport_complete W X hX hlo hhi hf
    simpa only [← hn] using (Finset.mem_filter.mp hb).1
  · intro n _
    rfl

lemma fullPrimeCoefficient_norm_bound (R : ℝ) (W : ι → ℝ → ℂ) (X M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (b : Eisenstein) :
    ‖fullPrimeCoefficient R W X b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  by_cases hs : Squarefree b
  · simpa only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_left hs] using
      orderedConvolution_norm_bound (fullPrimeSupport R W X)
        (fun i n => W i (norm n/X i)) M
        (fun i p hp => fullPrimeSupport_prime R W X i p hp) hM
        (fun i p _ => hW i _) b
  · simp only [fullPrimeCoefficient,squarefreeConvolution,ite_eq_right hs,norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hM i))

lemma fullPrime_slice_energy {R : ℝ} (hR : 0 ≤ R)
    (W : ι → ℝ → ℂ) (X M : ι → ℝ) (hX : ∀ i, 0 ≤ X i)
    (hM : ∀ i, 0 ≤ M i) (hW : ∀ i x, ‖W i x‖ ≤ M i) (f e : Eisenstein) :
    (∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2) ≤
      18*(R^Fintype.card ι*(∏ i, X i)/norm f)*
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by
  have hc := primary_support_card_le (fullPrimeSliceSupport R W X f e)
    (div_nonneg (mul_nonneg (pow_nonneg hR _) (Finset.prod_nonneg (fun i _ => hX i)))
      (norm_nonneg f)) (fun n hn =>
        ⟨(fullPrimeSliceSupport_bounds R W X f e hn).1,
          (fullPrimeSliceSupport_bounds R W X f e hn).2.2.2⟩)
  calc
    _ ≤ ∑ _n ∈ fullPrimeSliceSupport R W X f e,
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 :=
      Finset.sum_le_sum (fun n _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
        (fullPrimeCoefficient_norm_bound R W X M hM hW (f*n)) 2)
    _ = ((fullPrimeSliceSupport R W X f e).card:ℝ)*
        (((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)

end CubicFirstMoment

end

end OAI
