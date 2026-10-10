import OAI.NumberTheory.CubicMoment.Estimates.SmallBLowHeightBlocks
import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogScale

namespace OAI

/-! Arbitrary logarithmic savings in the noncube height moment once the
height exceeds an explicitly chosen logarithmic power. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_noncube_bounded_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ) (ℓ : ℤ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,d,hK,hbound⟩ := smallB_noncube_bounded_blocks hpnt hMV hC hHuxley
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨H₁,hH₁,hlog₁⟩ := log_power_normalization_bound (4*(k+2)+d+k)
    (by norm_num : (0:ℝ) < 1)
  obtain ⟨H₂,hH₂,hlog₂⟩ := log_power_normalization_bound (k+2)
    (by norm_num : (0:ℝ) < 1/20000)
  let Q := 5832*(H₁+1)+18*CI*(1+H₂)
  refine ⟨K*Q,4*(k+2)+d+k,by dsimp [Q]; positivity,?_⟩
  intro S H β Z B T M u ℓ hZ hB hM hT hS hβ hsize hH
  let N : ℝ := Z
  let L := 1+Real.log N
  let V := 5832*L^(4*(k+2))
  let E := ∑ b ∈ S, ‖β b‖^2
  let I := (largeCoreDyadicIndices V B).card
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have hV : 0 < V := by dsimp [V]; positivity
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have henergy : E ≤ 18*N*M^2 := by
    have hc := primary_support_card_le S hNp.le
      (fun b hb => ⟨(hS b hb).1,(hS b hb).2.2⟩)
    calc
      E ≤ ∑ b ∈ S, M^2 := Finset.sum_le_sum (fun b hb => pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ b hb) 2)
      _ = (S.card:ℝ)*M^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg M)
  have hBN : B ≤ N^2 := by
    calc
      B ≤ 8*B := by linarith
      _ ≤ N^(3/4:ℝ) := hsize
      _ ≤ N^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = _ := Real.rpow_two N
  have hI : (I:ℝ) ≤ CI*L^2 := hcount V B N hB hN1 hBN
  have hsmall := low_height_small_core_log_scale hNp hL1 k d hT (hlog₁ N hN1)
  have hA : M^2*N*(1+N/T)*V*L^d ≤
      (5832*(H₁+1))*M^2*N^2/L^k := by
    have hh := mul_le_mul_of_nonneg_left hsmall (sq_nonneg M)
    convert hh using 1 <;> ring
  have hmid : (I:ℝ)*(N*(V/5832)^(-(1/4:ℝ)))*E ≤
      (18*CI)*M^2*N^2/L^k := by
    have hv : (V/5832)^(-(1/4:ℝ)) = 1/L^(k+2) := logarithmic_core_cutoff hLp k
    rw [hv]
    calc
      _ ≤ (CI*L^2)*(N*(1/L^(k+2)))*(18*N*M^2) := by gcongr
      _ = _ := by rw [pow_add]; field_simp
  have hnlog : N^(2-1/20000:ℝ)*L^2 ≤ H₂*N^2/L^k := by
    have hh := rpow_log_saving hNp hLp k 2 (p := 2) (s := 1/20000) (hlog₂ N hN1)
    simpa only [Real.rpow_two] using hh
  have hNmul : N^(1-1/20000:ℝ)*N = N^(2-1/20000:ℝ) := by
    nth_rw 2 [←Real.rpow_one N]
    rw [←Real.rpow_add hNp]
    congr 1
    norm_num
  have hlarge : (I:ℝ)*N^(1-1/20000:ℝ)*E ≤
      (18*CI*H₂)*M^2*N^2/L^k := by
    calc
      _ ≤ (CI*L^2)*N^(1-1/20000:ℝ)*(18*N*M^2) := by gcongr
      _ = (18*CI*M^2)*(N^(2-1/20000:ℝ)*L^2) := by rw [←hNmul]; ring
      _ ≤ (18*CI*M^2)*(H₂*N^2/L^k) := mul_le_mul_of_nonneg_left hnlog (by positivity)
      _ = _ := by ring
  have hbracket : M^2*N*(1+N/T)*V*L^d+
      (I:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E ≤ Q*M^2*N^2/L^k := by
    have hh := add_le_add hA (add_le_add hmid hlarge)
    dsimp [Q]
    convert hh using 1 <;> ring
  have hb := hbound S H β Z B V T M u ℓ hZ (zero_le_one.trans hB) hV hTp hM hS hβ hsize hH
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hbracket
    (show 0 ≤ K*B^(1/3:ℝ) by positivity)
  convert hh using 1; ring

end CubicFirstMoment

end

end OAI
