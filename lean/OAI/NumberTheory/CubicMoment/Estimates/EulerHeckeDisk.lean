import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerFactorBounds
import OAI.NumberTheory.CubicMoment.Estimates.HeckeNormalizedDisk

namespace OAI

/-! Finite Euler deletion retains a polynomial bound on the normalized
Hecke disk. No functional equation for the imprimitive function is asserted. -/
noncomputable section
namespace CubicFirstMoment

lemma primeIdealRestriction_zero (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : χ 0=1) : primeIdealRestriction S χ 0=1 := by
  simp [primeIdealRestriction,hχ]

lemma euler_hecke_majorant {N A k : ℝ} {ε : ℂ}
    (hN : 1 ≤ N) (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) :
    N^3*heckeZeroFreeMajorant A k ε ≤ heckeZeroFreeMajorant (2*N*(1+A)) k 1 := by
  have hN0 : 0 ≤ N := by linarith
  have hH : 1 ≤ (k+7)^4 := one_le_pow₀ (by linarith)
  have hP : 1 ≤ (1+A)^4 := one_le_pow₀ (by linarith)
  have hNP : N^3 ≤ N^4 := pow_le_pow_right₀ hN (by norm_num : (3:ℕ)≤4)
  have hAP : A^4 ≤ (1+A)^4 := pow_le_pow_left₀ hA.le (by linarith) 4
  let Z := N^4*(1+A)^4*(k+7)^4
  have h1 : N^3 ≤ Z := by
    calc
      _ ≤ N^4 := hNP
      _ ≤ N^4*(1+A)^4 := le_mul_of_one_le_right (by positivity) hP
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hH
  have h2 : N^3*‖ε‖*A^4*(k+7)^4 ≤ Z := by
    calc
      _ ≤ N^4*1*(1+A)^4*(k+7)^4 := by gcongr
      _ = _ := by dsimp [Z]; ring
  have h3 : N^3*(1+‖ε‖*A^4*(k+7)^4) ≤ 1+(2*N*(1+A))^4*(k+7)^4 := by
    have hZ : 0 ≤ Z := by dsimp [Z]; positivity
    have he : (2*N*(1+A))^4*(k+7)^4=16*Z := by dsimp [Z]; ring
    rw [he]
    nlinarith only [h1,h2,hZ]
  unfold heckeZeroFreeMajorant
  rw [norm_one]
  have hh := mul_le_mul_of_nonneg_right h3 idealZetaTwo_pos.le
  nlinarith only [hh]

lemma euler_corrected_right_series (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {s : ℂ} (hss : 1 < s.re) :
    idealEulerFactor S χ s*L s=normDirichletSeries (primeIdealRestriction S χ) idealExponentNorm s := by
  rw [hs s hss,idealDirichlet_euler_exclusion S χ hχ hadd hss]

theorem euler_corrected_normalized_disk
    (S : Finset EisensteinIdealPrime) (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (hdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} (hε : ‖ε‖ ≤ 1)
    {L Ldual : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) (t : ℝ) :
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖normalizedHeckeDisk (fun s => idealEulerFactor S χ s*L s) t z‖ ≤
        normalizedHeckeDiskBound (2*idealExponentNorm (primeSetExponent S)*(1+A)) k 1 t := by
  intro z hz
  let N := idealExponentNorm (primeSetExponent S)
  have hN : 1 ≤ N := idealExponentNorm_ge_one _
  have hright (s : ℂ) (hss : 1 < s.re) := euler_corrected_right_series S χ hχ hadd hs hss
  have hc : (2+(t:ℂ)*Complex.I).re=2 := by simp
  have hinv : ‖(idealEulerFactor S χ (2+(t:ℂ)*Complex.I)*L (2+(t:ℂ)*Complex.I))⁻¹‖ ≤ idealZetaTwo := by
    rw [hright _ (by rw [hc]; norm_num)]
    exact idealDirichlet_reciprocal_bound _ (primeIdealRestriction_norm_le S χ hχ)
      (primeIdealRestriction_zero S χ hχ0) (primeIdealRestriction_add S χ hadd) hc.ge
  have hr : -(3/2:ℝ) ≤ (2+(t:ℂ)*Complex.I+3*z).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm z)).1
    have he : (2+(t:ℂ)*Complex.I+3*z).re=2+3*z.re := by simp
    rw [he]
    linarith
  have hi : |(2+(t:ℂ)*Complex.I+3*z).im| ≤ |t|+3 := by
    have hh := abs_add_le t (3*z.im)
    have him := Complex.abs_im_le_norm z
    have he : (2+(t:ℂ)*Complex.I+3*z).im=t+3*z.im := by simp
    rw [he]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at hh
    linarith
  have hl := shifted_hecke_uniform_strip hχ hdual hA hk hL hs hds hFE hcomp _ hr
  have hp : (1+|(2+(t:ℂ)*Complex.I+3*z).im|)^4 ≤ (4+|t|)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hcorr := idealEulerFactor_norm_bound S χ hχ hr
  have hm := euler_hecke_majorant hN hA hk hε
  have hnum : ‖idealEulerFactor S χ (2+(t:ℂ)*Complex.I+3*z)*L (2+(t:ℂ)*Complex.I+3*z)‖ ≤
      heckeZeroFreeMajorant (2*N*(1+A)) k 1*(4+|t|)^4 := by
    rw [norm_mul]
    calc
      _ ≤ N^3*(heckeZeroFreeMajorant A k ε*(4+|t|)^4) :=
        mul_le_mul hcorr (hl.trans (mul_le_mul_of_nonneg_left hp (heckeZeroFreeMajorant_pos A k ε).le))
          (_root_.norm_nonneg _) (by positivity)
      _ = (N^3*heckeZeroFreeMajorant A k ε)*(4+|t|)^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (by positivity)
  rw [normalizedHeckeDisk,div_eq_mul_inv,norm_mul]
  exact (mul_le_mul hnum hinv (_root_.norm_nonneg _)
    (mul_nonneg (heckeZeroFreeMajorant_pos _ _ _).le (by positivity))).trans (by
    unfold normalizedHeckeDiskBound
    nlinarith)

end CubicFirstMoment

end

end OAI
