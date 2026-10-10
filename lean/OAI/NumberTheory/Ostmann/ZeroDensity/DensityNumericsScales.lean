import OAI.NumberTheory.Ostmann.ZeroDensity.DensityNumericsBasic
import OAI.NumberTheory.Ostmann.ZeroDensity.DetectorLength
import OAI.NumberTheory.Ostmann.ZeroDensity.DyadicDetector

namespace OAI

noncomputable section
namespace Ostmann.ZeroDensity

theorem density_nat_scales {Q H : ℕ} (hQ : 1 ≤ Q) (hH : 1 ≤ H) :
    let B := Q^2*H
    let N := detectorLength Q H B
    let J := detectorBlockCount N
    1 ≤ B ∧ 1 ≤ N ∧ N ≤ 256*B^5 ∧
      ∀ j < J, B ≤ 2^j*B ∧ 2^j*B ≤ 512*B^5 := by
  dsimp only
  let B := Q^2*H
  let N := detectorLength Q H B
  have hB : 1 ≤ B := by
    have : 0 < B := by dsimp [B]; positivity
    omega
  have hN : 1 ≤ N := hB.trans (detectorLength_ge hQ hH hB)
  have hBN : B*N ≤ 256*B^5 := detector_support_length_le hQ
  have hNN : N ≤ B*N := by simpa using Nat.mul_le_mul_right N hB
  refine ⟨hB,hN,hNN.trans hBN,?_⟩
  intro j hj
  have hpow : 1 ≤ 2^j := by
    have : 0 < (2:ℕ)^j := by positivity
    omega
  refine ⟨by simpa using Nat.mul_le_mul_right B hpow,?_⟩
  calc
    2^j*B ≤ 2^(detectorBlockCount N)*B := by gcongr
    _ ≤ (2*N)*B := Nat.mul_le_mul_right B (detectorBlockCount_pow_le hN)
    _ = 2*(B*N) := by ring
    _ ≤ 2*(256*B^5) := Nat.mul_le_mul_left 2 hBN
    _ = _ := by ring

theorem density_log_scales {Q H : ℕ} (hQ : 1 ≤ Q) (hH : 1 ≤ H) :
    let B : ℝ := (Q^2*H : ℕ)
    let L : ℝ := 1+Real.log (Q*H : ℕ)
    1 ≤ L ∧ 0 ≤ 1+Real.log (Q:ℝ) ∧ 1+Real.log (Q:ℝ) ≤ L ∧
      Real.log B ≤ 2*Real.log (Q*H : ℕ) ∧
      ∀ U : ℝ, B ≤ U → U ≤ 512*B^5 →
        0 ≤ 1+Real.log (2*U) ∧ 1+Real.log (2*U) ≤ 2048*L := by
  dsimp only
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast hH
  have hQp : (0:ℝ) < Q := by linarith
  have hHp : (0:ℝ) < H := by linarith
  have hqlog : 0 ≤ Real.log (Q:ℝ) := Real.log_nonneg hQr
  have hhlog : 0 ≤ Real.log (H:ℝ) := Real.log_nonneg hHr
  have hlog : Real.log (Q*H : ℕ) = Real.log (Q:ℝ)+Real.log (H:ℝ) := by
    push_cast
    exact Real.log_mul (ne_of_gt hQp) (ne_of_gt hHp)
  have hBlog : Real.log (Q^2*H : ℕ) = 2*Real.log (Q:ℝ)+Real.log (H:ℝ) := by
    push_cast
    rw [Real.log_mul (by positivity) (ne_of_gt hHp), Real.log_pow]
    norm_num
  have hB : (1:ℝ) ≤ (Q^2*H : ℕ) := by
    exact_mod_cast (density_nat_scales hQ hH).1
  refine ⟨by rw [hlog]; linarith, by linarith, by rw [hlog]; linarith,
    by rw [hBlog,hlog]; linarith, ?_⟩
  intro U hBU hU
  have hUp : 0 < U := by linarith
  have h2U : 1 ≤ 2*U := by linarith
  refine ⟨by linarith [Real.log_nonneg h2U],?_⟩
  have hlarge : 2*U ≤ 1024*((Q^2*H : ℕ):ℝ)^5 := by linarith
  have hlogU := Real.log_le_log (by positivity : (0:ℝ)<2*U) hlarge
  rw [Real.log_mul (x := 1024) (y := ((Q^2*H : ℕ):ℝ)^5) (by norm_num) (by positivity), Real.log_pow] at hlogU
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1024)
  simp only [hBlog,hlog] at hlogU ⊢
  norm_num only [Nat.cast_ofNat] at hlogU
  norm_num only [show (1024:ℝ)-1=1023 by norm_num] at hc
  linarith

theorem density_block_count_bound {Q H : ℕ} (hQ : 1 ≤ Q) (hH : 1 ≤ H) :
    (detectorBlockCount (detectorLength Q H (Q^2*H)) : ℝ) ≤
      (265/Real.log 2+1)*(1+Real.log (Q*H : ℕ)) := by
  let N := detectorLength Q H (Q^2*H)
  have hsc := density_nat_scales hQ hH
  have hN : (0:ℝ)<N := by exact_mod_cast hsc.2.1
  have hNup : (N:ℝ) ≤ 256*((Q^2*H : ℕ):ℝ)^5 := by exact_mod_cast hsc.2.2.1
  have hlogN := Real.log_le_log hN hNup
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlogN
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<256)
  have hB := (density_log_scales hQ hH).2.2.2.1
  have hL := (density_log_scales hQ hH).1
  have hbound : Real.log (N:ℝ) ≤ 265*(1+Real.log (Q*H : ℕ)) := by
    norm_num only [Nat.cast_ofNat] at hlogN
    norm_num only [show (256:ℝ)-1=255 by norm_num] at hc
    linarith
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  calc
    (detectorBlockCount N:ℝ) ≤ Real.log N/Real.log 2+1 := detectorBlockCount_le_log N
    _ ≤ (265*(1+Real.log (Q*H : ℕ)))/Real.log 2+(1+Real.log (Q*H : ℕ)) := by
      exact add_le_add (div_le_div_of_nonneg_right hbound hlog2.le) hL
    _ = _ := by ring

end Ostmann.ZeroDensity

end

end OAI
