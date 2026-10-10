import OAI.NumberTheory.JointDickman.Amplification.FiniteAdditiveOrthogonality
import OAI.NumberTheory.JointDickman.Probability.SignedSplitProduct
import OAI.NumberTheory.JointDickman.Counting.CoefficientMoments

namespace OAI

/-! # First and second Fourier bounds for signed endpoint masses -/

namespace JointDickman
open Finset MeasureTheory

noncomputable def endpointFourierSum (B : ℕ) (a b X : ℝ)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ) (θ : ℝ) : ℂ :=
  finiteAdditiveSum (Ioc ⌊a*X⌋₊ ⌊b*X⌋₊)
    (fun n => (signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X) : ℝ)) θ

/-- Pointwise domination of each weighted endpoint coefficient. -/
theorem endpoint_weight_domination {B n : ℕ} {a X D M : ℝ}
    {γ : ℕ → ℝ} {w : ℝ → ℝ} (hB : 0 < B) (ha : 0 < a) (hX : 0 < X)
    (hD : 0 ≤ D) (_hM : 0 ≤ M) (hn : a*X < n)
    (hγ : |γ n| ≤ D*coefficientWeight B n/((B : ℝ)*n))
    (hw : |w (n/X)| ≤ M) :
    |γ n*w (n/X)| ≤ (D*M/((B : ℝ)*(a*X)))*coefficientWeight B n := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hn0 : (0 : ℝ) < n := (mul_pos ha hX).trans hn
  have hγ' : |γ n| ≤ D*coefficientWeight B n/((B : ℝ)*(a*X)) :=
    hγ.trans (div_le_div_of_nonneg_left (mul_nonneg hD (coefficientWeight_nonneg B n))
      (mul_pos hB0 (mul_pos ha hX))
      (mul_le_mul_of_nonneg_left hn.le hB0.le))
  rw [abs_mul]
  exact (mul_le_mul hγ' hw (abs_nonneg _)
    (div_nonneg (mul_nonneg hD (coefficientWeight_nonneg B n))
      (mul_pos hB0 (mul_pos ha hX)).le)).trans_eq (by ring)

/-- Finite-window form of both endpoint Fourier estimates. -/
theorem endpoint_fourier_bounds {B : ℕ} {a b X D M : ℝ}
    (hB : 0 < B) (ha : 0 < a) (hX : 0 < X) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (g : Finset ℕ → ℝ) (w : ℝ → ℝ)
    (hγ : ∀ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
      |signedSplitProductMass (auxiliaryPrimes B) g n| ≤
        D*coefficientWeight B n/((B : ℝ)*n))
    (hw : ∀ t, |w t| ≤ M) :
    (∀ θ, ‖endpointFourierSum B a b X g w θ‖ ≤
      (D*M/((B : ℝ)*(a*X)))*∑ n ∈ Ioc 0 ⌊b*X⌋₊, coefficientWeight B n) ∧
    (∫ θ in (0 : ℝ)..1, ‖endpointFourierSum B a b X g w θ‖^2) ≤
      (D*M/((B : ℝ)*(a*X)))^2*∑ n ∈ Ioc 0 ⌊b*X⌋₊, coefficientWeight B n^2 := by
  classical
  let F := D*M/((B : ℝ)*(a*X))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hdom (n : ℕ) (hn : n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊) :
      |signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X)| ≤ F*coefficientWeight B n := by
    exact endpoint_weight_domination hB ha hX hD hM
      ((Nat.floor_lt (mul_pos ha hX).le).mp (mem_Ioc.mp hn).1) (hγ n hn) (hw _)
  have hsub : Ioc ⌊a*X⌋₊ ⌊b*X⌋₊ ⊆ Ioc 0 ⌊b*X⌋₊ := by
    intro n hn
    simp only [mem_Ioc] at *
    omega
  constructor
  · intro θ
    calc
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
          ‖(signedSplitProductMass (auxiliaryPrimes B) g n*w (n/X) : ℝ) *
            additivePhase ((n : ℝ)*θ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, F*coefficientWeight B n := by
        apply sum_le_sum
        intro n hn
        simpa only [norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_mul] using hdom n hn
      _ ≤ ∑ n ∈ Ioc 0 ⌊b*X⌋₊, F*coefficientWeight B n :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg hF (coefficientWeight_nonneg B n))
      _ = _ := (mul_sum _ _ _).symm
  · unfold endpointFourierSum
    rw [finiteAdditiveSum_parseval]
    calc
      _ ≤ ∑ n ∈ Ioc ⌊a*X⌋₊ ⌊b*X⌋₊, F^2*coefficientWeight B n^2 := by
        apply sum_le_sum
        intro n hn
        rw [Complex.norm_real,Real.norm_eq_abs]
        have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF (coefficientWeight_nonneg B n))).mpr (hdom n hn)
        simpa only [mul_pow] using hh
      _ ≤ ∑ n ∈ Ioc 0 ⌊b*X⌋₊, F^2*coefficientWeight B n^2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = _ := (mul_sum _ _ _).symm

end JointDickman

end OAI
