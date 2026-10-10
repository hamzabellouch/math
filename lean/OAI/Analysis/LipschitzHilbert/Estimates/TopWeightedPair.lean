import OAI.Analysis.LipschitzHilbert.Estimates.TopCovariantContinuity

namespace OAI

/-! One common packet constant for the weighted wave and its constructed
scaled covariant derivative. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert

def topPairConstant (C : ℝ) (q : ℕ) : ℝ :=
  (8*(q:ℝ)+1)*(16^q*(1+2*(q:ℝ))*(16^q*C))

theorem topPairConstant_pos (C : ℝ) (q : ℕ) (hC : 0 < C) :
    0 < topPairConstant C q := by unfold topPairConstant; positivity

theorem topPairConstant_bounds (C : ℝ) (q : ℕ) (hC : 0 ≤ C) :
    16^q*(16^q*C) ≤ topPairConstant C q ∧
    16^q*(1+2*(q:ℝ))*(16^q*C) ≤ topPairConstant C q ∧
    (8*(q:ℝ)+1)*(16^q*(16^q*C)) ≤ topPairConstant C q := by
  have h1 : (1:ℝ) ≤ 1+2*(q:ℝ) := by nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have h8 : (1:ℝ) ≤ 8*(q:ℝ)+1 := by nlinarith [show (0:ℝ) ≤ q from Nat.cast_nonneg q]
  have hbase : 0 ≤ 16^q*(16^q*C) := by positivity
  have hder : 0 ≤ 16^q*(1+2*(q:ℝ))*(16^q*C) := by positivity
  have hb : 16^q*(16^q*C) ≤ 16^q*(1+2*(q:ℝ))*(16^q*C) := by
    convert le_mul_of_one_le_left hbase h1 using 1
    ring
  have hd : 16^q*(1+2*(q:ℝ))*(16^q*C) ≤ topPairConstant C q :=
    le_mul_of_one_le_left hder h8
  refine ⟨hb.trans hd, hd, ?_⟩
  exact mul_le_mul_of_nonneg_left hb (by positivity)

def topWeightedPair (f : Fin 2 → SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (i : Fin 2) : SchwartzMap ℝ ℂ :=
  if i=0 then topWeightedWave (f 0) a r b R y q
  else topCovariantWave (f 0) (f 1) a r b R y q

theorem topWeightedPair_bound (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ i x, ‖f i x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (i : Fin 2) (x : ℝ) :
    ‖topWeightedPair f a r b R y q i x‖ ≤
      topPairConstant C q*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hconst := topPairConstant_bounds C q hC
  have henv : 0 ≤ lineEnvelope s l m x*lineEnvelope t W n y :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  fin_cases i
  · simpa [topWeightedPair] using
      (topWeightedWave_bound (f 0) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC (hf 0) x).trans
        (mul_le_mul_of_nonneg_right hconst.1 henv)
  · simpa [topWeightedPair] using
      (topCovariantWave_bound (f 0) (f 1) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hf 1) x).trans (mul_le_mul_of_nonneg_right hconst.2.2 henv)

theorem topWeightedPair_derivative_bound (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ i x, ‖f i x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hdf : ∀ i x, ‖deriv (f i) x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (i : Fin 2) (x : ℝ) :
    ‖deriv (topWeightedPair f a r b R y q i) x‖ ≤
      (topPairConstant C q/l)*(lineEnvelope s l m x*lineEnvelope t W n y) := by
  have hconst := topPairConstant_bounds C q hC
  have henv : 0 ≤ lineEnvelope s l m x*lineEnvelope t W n y :=
    mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  fin_cases i
  · simpa [topWeightedPair] using
      (topWeightedWave_derivative_bound (f 0) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hdf 0) x).trans
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hconst.2.1 hl.le) henv)
  · simpa [topWeightedPair, topPairConstant] using
      topCovariantWave_derivative_bound (f 0) (f 1) a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC
        (hf 0) (hf 1) (hdf 0) (hdf 1) x

theorem topWeightedPair_low (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y : ℝ) (q : ℕ) (lo hi : ℝ)
    (hlow : ∀ i ξ, |ξ| < lo → 𝓕 (f i) ξ = 0)
    (hhigh : ∀ i ξ, hi < |ξ| → 𝓕 (f i) ξ = 0)
    (i : Fin 2) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (topWeightedPair f a r b R y q i) ξ = 0 := by
  fin_cases i
  · simpa [topWeightedPair] using
      topWeightedWave_low (f 0) a r b R y q lo hi (hlow 0) (hhigh 0) ξ hξ
  · simpa [topWeightedPair] using
      topCovariantWave_low (f 0) (f 1) a r b R y q lo hi
        (hlow 0) (hhigh 0) (hlow 1) (hhigh 1) ξ hξ

theorem topWeightedPair_high (f : Fin 2 → SchwartzMap ℝ ℂ)
    (a r b R y : ℝ) (q : ℕ) (lo hi : ℝ)
    (hlow : ∀ i ξ, |ξ| < lo → 𝓕 (f i) ξ = 0)
    (hhigh : ∀ i ξ, hi < |ξ| → 𝓕 (f i) ξ = 0)
    (i : Fin 2) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (topWeightedPair f a r b R y q i) ξ = 0 := by
  fin_cases i
  · simpa [topWeightedPair] using
      topWeightedWave_high (f 0) a r b R y q lo hi (hlow 0) (hhigh 0) ξ hξ
  · simpa [topWeightedPair] using
      topCovariantWave_high (f 0) (f 1) a r b R y q lo hi
        (hlow 0) (hhigh 0) (hlow 1) (hhigh 1) ξ hξ

end LipschitzHilbert

end

end OAI
