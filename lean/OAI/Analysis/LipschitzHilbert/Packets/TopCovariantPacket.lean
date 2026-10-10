import OAI.Analysis.LipschitzHilbert.Packets.TopWeightedPacket

namespace OAI

/-! The scaled covariant derivative of a top-weighted packet is another
Schwartz packet. Its extra scalar factor is bounded by 8q independently
of the top size and the vertical carrier frequency. -/

noncomputable section
open FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert

def topCovariantFactor (b R y : ℝ) (q : ℕ) : ℝ :=
  4*R*deriv (polynomialWeight b R q) y/polynomialWeight b R q y

theorem topCovariantFactor_bound (b R y : ℝ) (q : ℕ) (hR : 0 < R) :
    |topCovariantFactor b R y q| ≤ 8*(q:ℝ) := by
  have hY : 0 < polynomialWeight b R q y :=
    zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _)
  unfold topCovariantFactor
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4),
    abs_of_pos hR, abs_of_pos hY]
  apply (div_le_iff₀ hY).mpr
  calc
    _ ≤ 4*R*((2*(q:ℝ)/R)*polynomialWeight b R q y) :=
      mul_le_mul_of_nonneg_left (polynomialWeight_derivative b R y q hR) (by positivity)
    _ = _ := by field_simp; ring

def topCovariantWave (f df : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ) :
    SchwartzMap ℝ ℂ :=
  (topCovariantFactor b R y q:ℂ) • topWeightedWave f a r b R y q +
    topWeightedWave df a r b R y q

theorem topCovariantWave_bound (f df : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖df x‖ ≤ C*(lineEnvelope s l (m+2*q) x * lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖topCovariantWave f df a r b R y q x‖ ≤
      ((8*(q:ℝ)+1)*(16^q*(16^q*C)))*(lineEnvelope s l m x * lineEnvelope t W n y) := by
  have h1 := topWeightedWave_bound f a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC hf x
  have h2 := topWeightedWave_bound df a r b R y s l t W C q m n hl hr hW hR hlr hWR hs ht hC hdf x
  change ‖(topCovariantFactor b R y q:ℂ)*topWeightedWave f a r b R y q x +
    topWeightedWave df a r b R y q x‖ ≤ _
  calc
    _ ≤ ‖(topCovariantFactor b R y q:ℂ)*topWeightedWave f a r b R y q x‖ +
        ‖topWeightedWave df a r b R y q x‖ := norm_add_le _ _
    _ = |topCovariantFactor b R y q| *‖topWeightedWave f a r b R y q x‖ +
        ‖topWeightedWave df a r b R y q x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (8*(q:ℝ))*((16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y)) +
        (16^q*(16^q*C))*(lineEnvelope s l m x*lineEnvelope t W n y) :=
      add_le_add (mul_le_mul (topCovariantFactor_bound b R y q hR) h1 (norm_nonneg _)
        (by positivity)) h2
    _ = _ := by ring

theorem topCovariantWave_derivative_bound (f df : SchwartzMap ℝ ℂ)
    (a r b R y s l t W C : ℝ) (q m n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hW : 0 < W) (hR : 0 < R)
    (hlr : l ≤ r) (hWR : W ≤ R) (hs : |s-a| ≤ r) (ht : |t-b| ≤ R) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hdf : ∀ x, ‖df x‖ ≤ C*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hfx : ∀ x, ‖deriv f x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (hdfx : ∀ x, ‖deriv df x‖ ≤ (C/l)*(lineEnvelope s l (m+2*q) x*lineEnvelope t W (n+2*q) y))
    (x : ℝ) :
    ‖deriv (topCovariantWave f df a r b R y q) x‖ ≤
      (((8*(q:ℝ)+1)*(16^q*(1+2*(q:ℝ))*(16^q*C)))/l)*
        (lineEnvelope s l m x*lineEnvelope t W n y) := by
  have h1 := topWeightedWave_derivative_bound f a r b R y s l t W C q m n
    hl hr hW hR hlr hWR hs ht hC hf hfx x
  have h2 := topWeightedWave_derivative_bound df a r b R y s l t W C q m n
    hl hr hW hR hlr hWR hs ht hC hdf hdfx x
  have hd := (((topWeightedWave f a r b R y q).differentiable x).hasDerivAt.const_mul
    (topCovariantFactor b R y q:ℂ)).add
      ((topWeightedWave df a r b R y q).differentiable x).hasDerivAt
  change HasDerivAt (topCovariantWave f df a r b R y q) _ x at hd
  rw [hd.deriv]
  calc
    _ ≤ ‖(topCovariantFactor b R y q:ℂ)*deriv (topWeightedWave f a r b R y q) x‖ +
        ‖deriv (topWeightedWave df a r b R y q) x‖ := norm_add_le _ _
    _ = |topCovariantFactor b R y q| * ‖deriv (topWeightedWave f a r b R y q) x‖ +
        ‖deriv (topWeightedWave df a r b R y q) x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (8*(q:ℝ))*(((16^q*(1+2*(q:ℝ))*(16^q*C))/l)*
        (lineEnvelope s l m x*lineEnvelope t W n y)) +
        ((16^q*(1+2*(q:ℝ))*(16^q*C))/l)*(lineEnvelope s l m x*lineEnvelope t W n y) :=
      add_le_add (mul_le_mul (topCovariantFactor_bound b R y q hR) h1 (norm_nonneg _)
        (by positivity)) h2
    _ = _ := by ring

theorem topWeightedWave_covariant (f df : ℝ → SchwartzMap ℝ ℂ)
    (a r b R y frequency x : ℝ) (q : ℕ)
    (hf : DifferentiableAt ℝ (fun t => f t x) y)
    (hdf : (4*R:ℂ)*(deriv (fun t => f t x) y-(frequency:ℂ)*Complex.I*f y x) = df y x) :
    (4*R:ℂ)*(deriv (fun t => topWeightedWave (f t) a r b R t q x) y -
      (frequency:ℂ)*Complex.I*topWeightedWave (f y) a r b R y q x) =
        topCovariantWave (f y) (df y) a r b R y q x := by
  have hY : polynomialWeight b R q y ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (polynomialWeight_one_le _ _ _ _))
  have hc : topCovariantFactor b R y q*polynomialWeight b R q y =
      4*R*deriv (polynomialWeight b R q) y := by
    exact div_mul_cancel₀ _ hY
  have hcC := congrArg (fun t : ℝ => (t:ℂ)) hc
  push_cast at hcC
  have hv := ((((polynomialWeight_differentiable b R q) y).hasDerivAt.ofReal_comp).mul
    hf.hasDerivAt).const_mul (polynomialWeight a r q x:ℂ)
  have heq : (fun t => (polynomialWeight a r q x:ℂ)*((polynomialWeight b R q t:ℂ)*f t x)) =
      (fun t => topWeightedWave (f t) a r b R t q x) := by
    funext t
    rw [topWeightedWave_apply]
    push_cast
    ring
  change HasDerivAt (fun t => (polynomialWeight a r q x:ℂ)*
    ((polynomialWeight b R q t:ℂ)*f t x)) _ y at hv
  rw [heq] at hv
  rw [hv.deriv]
  change _ = (topCovariantFactor b R y q:ℂ)*topWeightedWave (f y) a r b R y q x +
    topWeightedWave (df y) a r b R y q x
  simp only [topWeightedWave_apply]
  rw [← hdf]
  push_cast
  linear_combination -(polynomialWeight a r q x:ℂ)*(f y x)*hcC

theorem topCovariantWave_low (f df : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hflo : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hfhi : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0)
    (hdlo : ∀ ξ, |ξ| < lo → 𝓕 df ξ = 0)
    (hdhi : ∀ ξ, hi < |ξ| → 𝓕 df ξ = 0) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (topCovariantWave f df a r b R y q) ξ = 0 := by
  have hadd : (𝓕 (topCovariantWave f df a r b R y q) : SchwartzMap ℝ ℂ) =
      (topCovariantFactor b R y q:ℂ) • 𝓕 (topWeightedWave f a r b R y q) +
        𝓕 (topWeightedWave df a r b R y q) := by
    exact (fourier_add _ _).trans (congrArg (fun h : SchwartzMap ℝ ℂ =>
      h + 𝓕 (topWeightedWave df a r b R y q)) (fourier_smul _ _))
  rw [hadd]
  change (topCovariantFactor b R y q:ℂ)*𝓕 (topWeightedWave f a r b R y q) ξ +
    𝓕 (topWeightedWave df a r b R y q) ξ = 0
  rw [topWeightedWave_low f a r b R y q lo hi hflo hfhi ξ hξ,
    topWeightedWave_low df a r b R y q lo hi hdlo hdhi ξ hξ]
  simp

theorem topCovariantWave_high (f df : SchwartzMap ℝ ℂ) (a r b R y : ℝ) (q : ℕ)
    (lo hi : ℝ) (hflo : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hfhi : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0)
    (hdlo : ∀ ξ, |ξ| < lo → 𝓕 df ξ = 0)
    (hdhi : ∀ ξ, hi < |ξ| → 𝓕 df ξ = 0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (topCovariantWave f df a r b R y q) ξ = 0 := by
  have hadd : (𝓕 (topCovariantWave f df a r b R y q) : SchwartzMap ℝ ℂ) =
      (topCovariantFactor b R y q:ℂ) • 𝓕 (topWeightedWave f a r b R y q) +
        𝓕 (topWeightedWave df a r b R y q) := by
    exact (fourier_add _ _).trans (congrArg (fun h : SchwartzMap ℝ ℂ =>
      h + 𝓕 (topWeightedWave df a r b R y q)) (fourier_smul _ _))
  rw [hadd]
  change (topCovariantFactor b R y q:ℂ)*𝓕 (topWeightedWave f a r b R y q) ξ +
    𝓕 (topWeightedWave df a r b R y q) ξ = 0
  rw [topWeightedWave_high f a r b R y q lo hi hflo hfhi ξ hξ,
    topWeightedWave_high df a r b R y q lo hi hdlo hdhi ξ hξ]
  simp

end LipschitzHilbert

end

end OAI
