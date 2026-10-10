import OAI.NumberTheory.CubicMoment.Estimates.SmallBLowLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.HeightCubeMass

namespace OAI

/-! The cube frequencies satisfy the same logarithmic height saving by
ordinary mean values with the actual squarefree norm-fiber moment. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem bounded_cube_height_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ) (ℓ : ℤ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → H ⊆ nonzeroCubeNormBall B →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,d,hK,hmean⟩ := bounded_squarefree_character_height hpnt hMV hC
  obtain ⟨D,hD,hlog⟩ := log_power_normalization_bound (4*(k+2)+d+k)
    (by norm_num : (0:ℝ) < 1)
  refine ⟨18*K*(5832*(D+1)),4*(k+2)+d+k,by positivity,?_⟩
  intro S H β Z B T M u ℓ hZ hB hM hT hS hβ hH
  let N : ℝ := Z
  let L := 1+Real.log N
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have hexp : Real.exp 1 ≤ (Z:ℝ) := by
    have he : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    linarith
  have hm := hmean S H β Z T M u ℓ hexp hTp hM hS hβ
  have hcard : (H.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hH)).trans (nonzeroCubeNormBall_card hB)
  have hscale := low_height_small_core_log_scale hNp hL1 k d hT (hlog N hN1)
  have hv : 1 ≤ 5832*L^(4*(k+2)) := by
    have hh := one_le_pow₀ hL1 (n := 4*(k+2))
    linarith
  have hs : N*(1+N/T)*L^d ≤ 5832*(D+1)*N^2/L^k := by
    apply le_trans ?_ hscale
    have hnonneg : 0 ≤ N*(1+N/T)*L^d := by positivity
    have hh := mul_le_mul_of_nonneg_left hv hnonneg
    convert hh using 1 <;> ring
  calc
    _ ≤ K*M^2*(1+N/T)*N*L^d*(18*B^(1/3:ℝ)) :=
      hm.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = (18*K*M^2*B^(1/3:ℝ))*(N*(1+N/T)*L^d) := by ring
    _ ≤ (18*K*M^2*B^(1/3:ℝ))*(5832*(D+1)*N^2/L^k) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp [N,L]; ring

end CubicFirstMoment

end

end OAI
