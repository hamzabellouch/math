import OAI.NumberTheory.JointDickman.Counting.CountingErrorParameter
import OAI.NumberTheory.JointDickman.Counting.SlowPeriodicMean
import OAI.NumberTheory.JointDickman.Amplification.CandidateArithmeticPeriod

namespace OAI

/-! # From the periodic sampling error to the moving counting scale -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def countingArithmeticCutError (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ) (σ : ℝ) (u : ℕ) : ℝ :=
  kernelCutNorm (realizedSiteKernel (countingSiteError P m B L T H M τ C w c D σ)
    (blockPatternEquiv B M (arithmeticPrimePatterns B M u)))

theorem arithmeticSiteCutMean_period_bound {B M : ℕ}
    (K : Fin M → Fin M → (auxiliaryPrimes B).powerset → (auxiliaryPrimes B).powerset → ℝ)
    {E : ℝ} (hE : arithmeticSiteCutMean K ≤ E) :
    (∑ u ∈ range (auxiliarySquarePeriod B), kernelCutNorm
      (realizedSiteKernel K (blockPatternEquiv B M (arithmeticPrimePatterns B M u)))) ≤
        (auxiliarySquarePeriod B : ℝ)*E := by
  have hq : auxiliarySquarePeriod B = ∏ p ∈ auxiliaryPrimes B, p^2 := by
    simp only [auxiliarySquarePeriod,prod_pow]
  have hqr : (auxiliarySquarePeriod B : ℝ) = ∏ p ∈ auxiliaryPrimes B, (p : ℝ)^2 := by
    rw [hq]
    simp only [Nat.cast_prod,Nat.cast_pow]
  have hqp : (0 : ℝ) < auxiliarySquarePeriod B := by exact_mod_cast auxiliarySquarePeriod_pos B
  unfold arithmeticSiteCutMean arithmeticSquareMean at hE
  rw [← hq,← hqr] at hE
  exact (div_le_iff₀ hqp).mp hE |>.trans_eq (mul_comm _ _)

theorem blockPatternEquiv_arithmetic_modEq {B M u v : ℕ}
    (h : u ≡ v [MOD auxiliarySquarePeriod B]) :
    blockPatternEquiv B M (arithmeticPrimePatterns B M u) =
      blockPatternEquiv B M (arithmeticPrimePatterns B M v) := by
  funext i
  apply Subtype.ext
  simpa only [blockPatternEquiv_val,primePatternsSites_arithmetic] using
    congrFun (blockPrimeSites_modEq (M := M) h) i

theorem counting_slow_mean (P : MvPolynomial (Fin 4) ℝ)
    (m : (Fin 4 →₀ ℕ) → ℕ) (B L T H M : ℕ) (τ C w : ℝ)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (D : (Fin 4 →₀ ℕ) → ℕ)
    {A K E : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (hw : 0 < w) (hT : 0 < T) (hM : 0 < M)
    (hcap : ∀ x : Fin M → (auxiliaryPrimes B).powerset,
      kernelAbsoluteMass (latentCandidateKernel B L T H M τ C (fun i => (x i).val)
        (smoothCandidateCutoff B T)) ≤ A)
    (hkernel : ∀ (j : ℕ) (s t : ℝ), H < j → j < T → |s| ≤ 3 → |t| ≤ 3 → ∀ x y,
      |countingPrimeKernel P m B j c D T s x y-countingPrimeKernel P m B j c D T t x y| ≤ K*|s-t|)
    (hmean : ∀ σ : ℝ, |σ| ≤ 3 → arithmeticSiteCutMean
      (countingSiteError P m B L T H M τ C w c D σ) ≤ E)
    (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ σ : ℕ → ℝ, (∀ u, |σ u| ≤ 3) →
      (∀ b r, r < auxiliarySquarePeriod B →
        |σ (b*auxiliarySquarePeriod B+r)-σ (b*auxiliarySquarePeriod B)| ≤
          (auxiliarySquarePeriod B : ℝ)/((T : ℝ)*(N+1))) →
      (∑ u ∈ range (J*N), countingArithmeticCutError P m B L T H M τ C w c D (σ u) u)/(N : ℝ) <
        (J : ℝ)*E+ε := by
  let V := A/w+(M : ℝ)*(∑ j ∈ range (T+1),
    |independentRootMean B L τ C*(singularSeries j/(j : ℝ))| *K)
  have hV : 0 ≤ V := add_nonneg (div_nonneg hA hw.le) (mul_nonneg (Nat.cast_nonneg _)
    (sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hK)))
  apply slow_periodic_mean_bound (auxiliarySquarePeriod_pos B) hT
    (fun u s => countingArithmeticCutError P m B L T H M τ C w c D s u) hE hV
    (fun _ _ _ => kernelCutNorm_nonneg _) _ _ _ J hε
  · intro b r s
    unfold countingArithmeticCutError
    rw [blockPatternEquiv_arithmetic_modEq (show b*auxiliarySquarePeriod B+r ≡ r [MOD auxiliarySquarePeriod B] by
      unfold Nat.ModEq
      simp)]
  · intro s hs
    exact arithmeticSiteCutMean_period_bound _ (hmean s hs)
  · intro u s t hs ht
    exact countingError_parameter_bound P m B L T H M τ C w c D hA hK hw hM hcap hkernel
      s t hs ht _

end JointDickman

end OAI
