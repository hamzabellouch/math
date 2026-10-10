import OAI.NumberTheory.JointDickman.Amplification.GeometricPeriodLaw
import OAI.NumberTheory.JointDickman.Probability.FiniteKernelOrthogonality

namespace OAI

/-! # Exact arithmetic meaning of the geometric-box period integral -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def geometricArithmeticSum (B j : ℕ) (a b l u T t : ℝ)
    (S : Finset ℤ) (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w : ℝ → ℝ) : ℝ :=
  B*∑ k ∈ S,
    ∑ c ∈ Ioc ⌊l*(Real.exp ((k : ℝ)*t)/T)⌋₊ ⌊u*(Real.exp ((k : ℝ)*t)/T)⌋₊,
    ∑ n₂ ∈ Ioc ⌊a*Real.exp ((k : ℝ)*t)⌋₊ ⌊b*Real.exp ((k : ℝ)*t)⌋₊,
    ∑ n₁ ∈ Ioc ⌊a*Real.exp ((k : ℝ)*t)⌋₊ ⌊b*Real.exp ((k : ℝ)*t)⌋₊,
      if n₁ = n₂+j*c then
        (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) n₁*
          w₁ (n₁/Real.exp ((k : ℝ)*t)))*
        (signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) n₂*
          w₂ (n₂/Real.exp ((k : ℝ)*t)))*
        (coefficientWeight B c*w (c/(Real.exp ((k : ℝ)*t)/T)))
      else 0

theorem geometricPeriodSum_eq_arithmeticSum (B j : ℕ) {a b l u T t : ℝ}
    (hT : 0 < T) (hl : 0 < l) (hlu : l ≤ u)
    (S : Finset ℤ) (g h : (auxiliaryPrimes B → Bool) → ℝ) (w₁ w₂ w : ℝ → ℝ)
    (hsupp : ∀ x, x ≤ l ∨ u < x → w x = 0) :
    geometricPeriodSum B j a b T t S g h w₁ w₂ w =
      (geometricArithmeticSum B j a b l u T t S g h w₁ w₂ w : ℂ) := by
  classical
  have hcoeff (X : ℝ) (hX : 0 < X) (θ : ℝ) :
      smoothCoefficientAdditiveSum B X θ w =
        finiteAdditiveSum (Ioc ⌊l*X⌋₊ ⌊u*X⌋₊)
          (fun c => (coefficientWeight B c*w (c/X) : ℝ)) θ := by
    unfold smoothCoefficientAdditiveSum finiteAdditiveSum
    rw [tsum_eq_Ioc_of_scaled_support hl.le hlu hX hsupp _
      (by intro n hn; simp [hn])]
    apply sum_congr rfl
    intro n _
    push_cast
    ring
  unfold geometricPeriodSum geometricArithmeticSum
  push_cast
  congr 1
  apply sum_congr rfl
  intro k _
  have hX : 0 < Real.exp ((k : ℝ)*t)/T := div_pos (Real.exp_pos _) hT
  simp only [geometricBoxIntegrand,endpointFourierSum]
  simp_rw [hcoeff _ hX]
  rw [finiteKernel_orthogonality]
  simp only [apply_ite,Complex.ofReal_mul,Complex.ofReal_zero]

end JointDickman

end OAI
