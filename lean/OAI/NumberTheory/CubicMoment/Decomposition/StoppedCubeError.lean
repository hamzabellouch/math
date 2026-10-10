import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeRoughness
import OAI.NumberTheory.CubicMoment.Estimates.CubeUniformError

namespace OAI

/-! The cube error only needs roughness where the actual coefficient is
nonzero. This avoids imposing roughness on the stopped row's ambient
finite support. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubePoissonContribution_weighted_error (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (S : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (A L P : ℝ), 0 < A → 0 < L → 0 ≤ P → A ≤ 27*L^2 →
      (∀ a ∈ S, L ≤ norm a) →
      ∀ (β : Eisenstein → ℂ) (u : ℝ),
      (∀ a ∈ S, ∀ b ∈ S, β a ≠ 0 → β b ≠ 0 →
        (∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p) ≤ P) →
      ‖cubePoissonContribution S β u W A-coprimeCubeMainTerm S β u W A‖ ≤
        (C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9)*(∑ a ∈ S, ‖β a‖)^2 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cubePoissonContribution_error W hW hW'
  refine ⟨C,K,hC,hK,?_⟩
  intro S hS A L P hA hL hP hAL hN β u hprime
  have hAN (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S) :
      A ≤ 27*norm (b*a) := by
    apply hAL.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul (hN b hb) (hN a ha) hL.le (hL.le.trans (hN b hb))
  let M := C*A/(27*L)+K*A^(2/3:ℝ)*L^(-(1/3:ℝ))*P/9
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hrow (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) (hb : b ∈ S)
      (haz : β a ≠ 0) (hbz : β b ≠ 0) :
      C*A/(27*Real.sqrt (norm (b*a))) +
        K*(A^(2/3:ℝ)*(norm (b*a))^(-(1/6:ℝ))/9)*
          ∑ p ∈ primaryPrimeFactors a ∪ primaryPrimeFactors b, 1/norm p ≤ M := by
    obtain ⟨hs,hr⟩ := cube_pair_norm_bounds hL (hN a ha) (hN b hb)
    apply add_le_add
    · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    · calc
        _ ≤ K*(A^(2/3:ℝ)*L^(-(1/3:ℝ))/9)*P := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) (by norm_num)) hK.le
          · exact hprime a ha b hb haz hbz
          · exact Finset.sum_nonneg (fun p _ => one_div_nonneg.mpr (norm_nonneg p))
          · positivity
        _ = _ := by ring
  apply (hbound S hS A hA hAN β u).trans
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, ‖β a‖*‖β b‖*M := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      split_ifs
      · by_cases haz : β a = 0
        · simp [haz]
        · by_cases hbz : β b = 0
          · simp [hbz]
          · exact mul_le_mul_of_nonneg_left (hrow a ha b hb haz hbz) (by positivity)
      · positivity
    _ = _ := by
      dsimp only [M]
      simp only [pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_cube_uniform_error (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ (X ξ δ b A u : ℝ),
      1 ≤ X → ξ ≤ 2/5 → 0 < δ → δ ≤ 1 → 2 ≤ b → b ≤ X →
      0 < A → A ≤ 27*(b/2)^2 →
      ∀ (W : ι → ℝ → ℂ) (e : Eisenstein) (j k h : ℕ) (Z Q : ℝ) (early : Bool),
      j ≤ h → 0 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      let S := stoppedIntervalSupport ι X (b/2) b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j k h Z Q early)
      ‖cubePoissonContribution S β u Φ A-coprimeCubeMainTerm S β u Φ A‖ ≤
        (C*A/(27*(b/2))+K*A^(2/3:ℝ)*(b/2)^(-(1/3:ℝ))/9*
          ((2*Real.log X/Real.log 2)/min (X^ξ) (geometricBinLower (1+δ) X h)))*
          (∑ a ∈ S, ‖β a‖)^2 := by
  obtain ⟨C,K,hC,hK,hbound⟩ := cubePoissonContribution_weighted_error Φ hΦ hΦ'
  refine ⟨C,K,hC,hK,?_⟩
  intro X ξ δ b A u hX hξz hδ hδone hb2 hbX hA hAb W e j k h Z Q early hj hR
  dsimp only
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hh := hbound (stoppedIntervalSupport ι X (b/2) b e)
    (fun a ha => ⟨(stoppedIntervalSupport_spec X (b/2) b e ha).1,
      (stoppedIntervalSupport_spec X (b/2) b e ha).2.1⟩) A (b/2)
    ((2*Real.log X/Real.log 2)/min (X^ξ) (geometricBinLower (1+δ) X h))
    hA (by linarith) (by positivity) hAb
    (fun a ha => (Finset.mem_filter.mp ha).2.2.2.1.le)
    (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
      (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
        j k h Z Q early)) u
    (fun a ha c hc haz hcz => stopped_pair_prime_reciprocal_log hX hξz hδ hδone hbX
      W j k h Z Q early hj e ha hc haz hcz hR)
  exact hh.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
