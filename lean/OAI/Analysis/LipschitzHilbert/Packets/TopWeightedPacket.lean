import OAI.Analysis.LipschitzHilbert.Fourier.VerticalWeight

namespace OAI

/-! Both factors of a fixed top polynomial can be absorbed into the
original packet orders, uniformly in the horizontal reference line. -/

noncomputable section
open scoped BigOperators
open FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

def topWeightedWave (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) : SchwartzMap ℝ ℂ :=
  polynomialLocalization a r q ((polynomialWeight b R q y : ℂ) • f)

theorem topWeightedWave_apply (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) (x : ℝ) :
    topWeightedWave f a r b R y q x =
      (polynomialWeight a r q x * polynomialWeight b R q y : ℝ) * f x := by
  rw [topWeightedWave, polynomialLocalization_apply, smul_apply, smul_eq_mul]
  push_cast
  ring

theorem topWeightedWave_bound (f : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖topWeightedWave f a r b R y q x‖ ≤
      (16^q*(16^q*C))*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have hv (z : ℝ) : ‖((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      (16^q*C*lineEnvelope t W n y)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_wave f y t b W R (C*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg hC (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hf z)
    convert h using 1
    ring
  have h := polynomialLocalization_packet_bound
    ((polynomialWeight b R q y : ℂ) • f) a r s l
    (16^q*C*lineEnvelope t W n y) q m hl hr hlr hs
    (mul_nonneg (mul_nonneg (by positivity) hC) (lineEnvelope_nonneg _ _ _ _)) hv x
  convert h using 1
  · rfl
  · ring

theorem topWeightedWave_derivative_bound (f : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖deriv f x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖deriv (topWeightedWave f a r b R y q) x‖ ≤
      ((16^q*(1+2*(q:ℝ))*(16^q*C))/l)*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have hv (z : ℝ) : ‖((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      (16^q*C*lineEnvelope t W n y)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_wave f y t b W R (C*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg hC (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hf z)
    convert h using 1
    ring
  have hd (z : ℝ) : ‖deriv ((polynomialWeight b R q y : ℂ) • f) z‖ ≤
      ((16^q*C*lineEnvelope t W n y)/l)*lineEnvelope s l (m+2*q) z := by
    have h := vertical_weighted_derivative f y t b W R ((C/l)*lineEnvelope s l (m+2*q) z)
      q n hW hR hWR ht (mul_nonneg (div_nonneg hC hl.le) (lineEnvelope_nonneg _ _ _ _)) z
      (by simpa only [mul_assoc] using hdf z)
    convert h using 1
    ring
  have h := polynomialLocalization_derivative_bound
    ((polynomialWeight b R q y : ℂ) • f) a r s l
    (16^q*C*lineEnvelope t W n y) q m hl hr hlr hs
    (mul_nonneg (mul_nonneg (by positivity) hC) (lineEnvelope_nonneg _ _ _ _)) hv hd x
  convert h using 1
  · rfl
  · ring

theorem packetSynthesis_topWeighted {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) :
    packetSynthesis c (fun i => topWeightedWave (f i) a r b R y q) =
      topWeightedWave (packetSynthesis c f) a r b R y q := by
  ext x
  rw [packetSynthesis_apply, topWeightedWave_apply, packetSynthesis_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [topWeightedWave_apply]
  ring

theorem partialBandSum_topWeighted {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (a r b R y : ℝ) (q n : ℕ) (x : ℝ) :
    partialBandSum (fun j => topWeightedWave (f j) a r b R y q) n x =
      (polynomialWeight a r q x * polynomialWeight b R q y : ℝ) * partialBandSum f n x := by
  unfold partialBandSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [topWeightedWave_apply]
  · simp only [mul_zero]

theorem hilbertPartialBandSum_topWeighted {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q n : ℕ) (x : ℝ) :
    hilbertPartialBandSum (fun j k => topWeightedWave (f j k) a r b R y q) n x =
      (polynomialWeight a r q x * polynomialWeight b R q y) • hilbertPartialBandSum f n x := by
  ext k
  change partialBandSum (fun j => topWeightedWave (f j k) a r b R y q) n x =
    (polynomialWeight a r q x * polynomialWeight b R q y) • partialBandSum (fun j => f j k) n x
  rw [partialBandSum_topWeighted, Complex.real_smul]

theorem topWeightedWave_low (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (topWeightedWave f a r b R y q) ξ = 0 := by
  apply polynomialLocalization_low a r q _ lo hi ?_ ?_ ξ hξ
  · intro z hz
    rw [fourier_smul, smul_apply, hlow z hz, smul_zero]
  · intro z hz
    rw [fourier_smul, smul_apply, hhigh z hz, smul_zero]

theorem topWeightedWave_high (f : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (topWeightedWave f a r b R y q) ξ = 0 := by
  apply polynomialLocalization_high a r q _ lo hi ?_ ?_ ξ hξ
  · intro z hz
    rw [fourier_smul, smul_apply, hlow z hz, smul_zero]
  · intro z hz
    rw [fourier_smul, smul_apply, hhigh z hz, smul_zero]

end LipschitzHilbert

end

end OAI
