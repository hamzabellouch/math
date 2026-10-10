import OAI.NumberTheory.JointDickman.Amplification.EndpointFullModel
import OAI.NumberTheory.JointDickman.Amplification.WeightedGeometricError

namespace OAI

/-! # Exact box-summed replacement in the full retained-arc model -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

noncomputable def geometricFullModelDifference (m B j Q : ℕ) [NeZero j]
    (a b T t : ℝ) (S : Finset ℤ) (d : ℤ → ℂ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ)) : ℂ :=
  (B : ℂ)*(∑ k ∈ S,
      (fullSmallMajorArcModel B j (Real.exp ((k : ℝ)*t)/T) Q
        (fun θ => endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) g) w₁ θ*
          endpointFourierSum B a b (Real.exp ((k : ℝ)*t)) (subsetSiteTest (auxiliaryPrimes B) h) w₂ (-θ))
        (fun ξ => d k*testFourierTransform w ξ) (fun q => (μ (q : ℕ) : ℂ)/((q : ℕ).totient : ℂ))-
      (d k/j)*sampledEndpointKernel m B j Q
        (geometricHistogramWindow m B t (Real.log a) (Real.log b) k)
        g h w₁ w₂ (Real.exp ((k : ℝ)*t)) (T/j) w))

theorem geometric_full_model_replacement {m B j Q : ℕ} [NeZero j]
    (hm : 0 < m) (hB : 0 < B) (hQ : Q ≤ B^12) (hcut : j*Q ≤ auxiliaryCutoff B)
    {a b T t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hT : 0 < T)
    (S : Finset ℤ) (d : ℤ → ℂ) (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (hs₁ : ∀ x, x ≤ a ∨ b < x → w₁ x = 0)
    (hs₂ : ∀ x, x ≤ a ∨ b < x → w₂ x = 0)
    (hl₁ : ∀ k ∈ S, ∀ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
      w₁ (n/Real.exp ((k : ℝ)*t)) ≠ 0 → Real.log n/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (hl₂ : ∀ k ∈ S, ∀ n ∈ primeSplitProductSupport (auxiliaryPrimes B),
      w₂ (n/Real.exp ((k : ℝ)*t)) ≠ 0 → Real.log n/B ∈ Set.Ioc (1/2 : ℝ) 3)
    (w : 𝓢(ℝ,ℝ)) :
    geometricFullModelDifference m B j Q a b T t S d g h w₁ w₂ w =
      retainedErrorSum B j Q (fun q => weightedGeometricDenominatorError m B j q
        a b t (T/j) S d g h w₁ w₂ w) := by
  unfold geometricFullModelDifference
  have hj : (j : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne j
  have hβ (k : ℤ) : Real.exp ((k : ℝ)*t)/((j : ℝ)*(Real.exp ((k : ℝ)*t)/T)) = T/j := by
    field_simp
  have hJ (k : ℤ) : histogramWindowCells (channelFineCount m B)
      (Real.log (a*Real.exp ((k : ℝ)*t))/B) (Real.log (b*Real.exp ((k : ℝ)*t))/B) =
      geometricHistogramWindow m B t (Real.log a) (Real.log b) k := by
    simp only [geometricHistogramWindow,Real.log_mul ha.ne' (Real.exp_ne_zero _),
      Real.log_mul (ha.trans_le hab).ne' (Real.exp_ne_zero _),Real.log_exp]
    congr 2 <;> ring
  have he (k : ℤ) (hk : k ∈ S) := endpoint_full_model_replacement hm hB hQ hcut ha hab
    (Real.exp_pos ((k : ℝ)*t)) (div_pos (Real.exp_pos ((k : ℝ)*t)) hT) g h hg hh w₁ w₂ hM₁ hM₂
    hw₁ hw₂ hs₁ hs₂ (hl₁ k hk) (hl₂ k hk) w (d k)
  simp only [hβ,hJ] at he
  rw [sum_congr rfl he]
  unfold retainedErrorSum weightedGeometricDenominatorError
  simp only [div_eq_mul_inv,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  apply sum_congr rfl
  intro k _
  ring

end JointDickman

end OAI
