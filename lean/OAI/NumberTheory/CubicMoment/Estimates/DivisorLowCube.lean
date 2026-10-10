import OAI.NumberTheory.CubicMoment.Estimates.DivisorWeightedMean
import OAI.NumberTheory.CubicMoment.Estimates.SmallBLowCube

namespace OAI

/-! Cube frequencies in all coprimality rows, with logarithmic divisor cost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem divisor_cube_low_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → H ⊆ nonzeroCubeNormBall B →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨Ke,d,hKe,he⟩ := bounded_third_divisor_energy hpnt
  obtain ⟨D,hD,hlog⟩ := log_power_normalization_bound (4*(k+2)+d+k)
    (by norm_num : (0:ℝ) < 1)
  refine ⟨36*(C+1)*Ke*(5832*(D+1)),4*(k+2)+d+k,by positivity,?_⟩
  intro S H U β Z B T M u hZ hB hM hT hU hS hβ hH
  let N : ℝ := Z
  let L := 1+Real.log N
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have hexp : Real.exp 1 ≤ N := by
    have hh : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    dsimp [N]
    linarith
  have henergy := he S β N M hexp hM hS hβ
  have hcard : (H.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hH)).trans (nonzeroCubeNormBall_card hB)
  have hscale := low_height_small_core_log_scale hNp hL1 k d hT (hlog N hN1)
  have hv : 1 ≤ 5832*L^(4*(k+2)) := by
    have hh := one_le_pow₀ hL1 (n := 4*(k+2))
    linarith
  have hs : N*(1+N/T)*L^d ≤ 5832*(D+1)*N^2/L^k := by
    apply le_trans ?_ hscale
    have hh := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ N*(1+N/T)*L^d by positivity)
    convert hh using 1 <;> ring
  calc
    _ ≤ 2*C*(1+N/T)*(Ke*M^2*N*L^d)*(18*B^(1/3:ℝ)) :=
      (divisor_weighted_character_height hMV hC hTp S H U β Z hU hS u).trans
        (by gcongr)
    _ ≤ 2*(C+1)*(1+N/T)*(Ke*M^2*N*L^d)*(18*B^(1/3:ℝ)) := by gcongr; linarith
    _ = (36*(C+1)*Ke*M^2*B^(1/3:ℝ))*(N*(1+N/T)*L^d) := by ring
    _ ≤ (36*(C+1)*Ke*M^2*B^(1/3:ℝ))*(5832*(D+1)*N^2/L^k) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp [N,L]; ring

end CubicFirstMoment

end

end OAI
