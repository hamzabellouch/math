import OAI.NumberTheory.Ostmann.Supply.FourierKernel

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

@[simp] theorem phase_zero : phase 0 = 0 := by simp [phase]

theorem phase_norm_le (z : ℂ) : ‖phase z‖ ≤ 1 := by
  by_cases hz : z=0
  · simp [hz]
  · simp [phase, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem phase_conj (z : ℂ) : phase (conj z) = conj (phase z) := by
  simp only [phase, map_div₀, Complex.conj_ofReal, Complex.norm_conj]

theorem conj_mul_phase (z : ℂ) : conj z * phase z = (‖z‖ : ℂ) := by
  by_cases hz : z=0
  · simp [hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [phase, ← mul_div_assoc, Complex.conj_mul']
    field_simp

variable {p : ℕ} [NeZero p]

def giantTest (S : Finset (ZMod p)) : EuclideanSpace ℂ (ZMod p) :=
  Supply.fourierEquiv.symm (WithLp.toLp 2 (fun v => phase (Supply.additiveTransform S v)))

theorem giantTest_fourier (S : Finset (ZMod p)) (v : ZMod p) :
    Supply.unitaryDFT (giantTest S) v = phase (Supply.additiveTransform S v) := by
  rw [← Supply.fourierEquiv_apply]
  exact congrArg (fun f : EuclideanSpace ℂ (ZMod p) => f v)
    (Supply.fourierEquiv.apply_symm_apply _)

theorem giant_phase_neg (S : Finset (ZMod p)) (v : ZMod p) :
    phase (Supply.additiveTransform S (-v)) = conj (phase (Supply.additiveTransform S v)) := by
  rw [Supply.additiveTransform_neg, phase_conj]

theorem giantTest_conj (S : Finset (ZMod p)) (x : ZMod p) :
    conj (giantTest S x) = giantTest S x := by
  rw [giantTest, Supply.fourierEquiv_symm_apply, Supply.unitaryDFT,
    map_div₀, Complex.conj_ofReal, Supply.conj_dft, neg_neg]
  have heq : (fun v => conj (phase (Supply.additiveTransform S v))) =
      (fun v => phase (Supply.additiveTransform S (-v))) := by
    funext v
    exact (giant_phase_neg S v).symm
  change ZMod.dft (fun v => conj (phase (Supply.additiveTransform S v))) x /
      (Real.sqrt p : ℂ) = _
  rw [heq]
  exact congrArg (fun z : ℂ => z / (Real.sqrt p : ℂ))
    (congrFun (ZMod.dft_comp_neg (fun v => phase (Supply.additiveTransform S v))) x)

theorem giantTest_real (S : Finset (ZMod p)) (x : ZMod p) :
    (giantTest S x).im = 0 := by
  have h := congrArg Complex.im (giantTest_conj S x)
  simp only [Complex.conj_im] at h
  linarith

theorem giantTest_sum_zero (S : Finset (ZMod p)) : ∑ x, giantTest S x = 0 := by
  have h := giantTest_fourier S 0
  rw [Supply.additiveTransform_zero, phase_zero] at h
  rw [Supply.unitaryDFT, ZMod.dft_apply_zero] at h
  have hp : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos p : (0 : ℝ)<p)).ne'
  exact (div_eq_zero_iff.mp h).resolve_right hp

theorem giantTest_sum_sq_le (S : Finset (ZMod p)) :
    (∑ x, ‖giantTest S x‖^2) ≤ p := by
  rw [← Supply.unitaryDFT_parseval (giantTest S)]
  simp_rw [giantTest_fourier]
  calc
    (∑ v, ‖phase (Supply.additiveTransform S v)‖^2) ≤ ∑ _ : ZMod p, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa only [one_pow] using
        pow_le_pow_left₀ (norm_nonneg _) (phase_norm_le (Supply.additiveTransform S v)) 2
    _ = p := by simp [ZMod.card]

theorem giantTest_pairing (S : Finset (ZMod p)) :
    (∑ x, (Supply.normalizedIndicator S x : ℂ) * giantTest S x) =
      ∑ v, (‖Supply.additiveTransform S v‖ : ℂ) := by
  let f : EuclideanSpace ℂ (ZMod p) :=
    WithLp.toLp 2 (fun x => (Supply.normalizedIndicator S x : ℂ))
  have h := Supply.fourierEquiv_inner f (giantTest S)
  simp only [PiLp.inner_apply, RCLike.inner_apply] at h
  have hf (v : ZMod p) : Supply.fourierEquiv f v = Supply.additiveTransform S v := rfl
  simp only [hf, Supply.fourierEquiv_apply, giantTest_fourier] at h
  simp only [f, Complex.conj_ofReal] at h
  have hphase (z : ℂ) : phase z * conj z = (‖z‖ : ℂ) := by
    rw [mul_comm]
    exact conj_mul_phase z
  simp only [hphase] at h
  simpa only [mul_comm] using h.symm

end Ostmann.Construction

end

end OAI
