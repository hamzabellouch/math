import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur
import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem envelope_synthesis_square {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ι → ℂ) (f : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, w i ≤ D)
    (henv : ∀ i, ‖f i‖ ≤ C * w i) :
    ‖∑ i, c i • f i‖ ^ 2 ≤ D * C ^ 2 * ∑ i, ‖c i‖ ^ 2 * w i := by
  have hterm (i : ι) : ‖c i • f i‖ ^ 2 / w i ≤ C ^ 2 * (‖c i‖ ^ 2 * w i) := by
    rw [norm_smul, mul_pow]
    apply (div_le_iff₀ (hw i)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (henv i) 2
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖c i‖)
    nlinarith
  calc
    _ ≤ (∑ i, w i) * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      weighted_sum_norm_square _ w hw
    _ ≤ D * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      mul_le_mul_of_nonneg_right hover (Finset.sum_nonneg (fun i _ =>
        div_nonneg (sq_nonneg _) (hw i).le))
    _ ≤ D * ∑ i, C ^ 2 * (‖c i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hD
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

def packetSynthesis {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  ∑ i, c i • f i

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

theorem polynomial_packetSynthesis_energy {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (s rho : ι → ℝ)
    (a l r C D : ℝ) (q : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hrho : ∀ i, 0 < rho i)
    (hcenter : ∀ i, |s i - a| ≤ r) (hD : 0 ≤ D)
    (hover : ∀ x, ∑ i, rho i * lineEnvelope (s i) l (1 + 2 * q) x ≤ D)
    (henv : ∀ i x, ‖f i x‖ ≤ C * (rho i * lineEnvelope (s i) l (1 + 2 * q) x)) :
    (∫ x, ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2) ≤
      D * C ^ 2 * 16 ^ q * (Real.pi * l) * ∑ i, ‖c i‖ ^ 2 * rho i := by
  have hE (i : ι) (x : ℝ) : 0 < rho i * lineEnvelope (s i) l (1 + 2 * q) x := by
    unfold lineEnvelope
    exact mul_pos (hrho i) (inv_pos.mpr (pow_pos (by positivity) _))
  have hpoint (x : ℝ) : ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2 ≤
      D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x := by
    have hsyn := envelope_synthesis_square c (fun i => f i x)
      (fun i => rho i * lineEnvelope (s i) l (1 + 2 * q) x)
      (fun i => hE i x) hD (hover x) (fun i => henv i x)
    have hn : ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2 =
        polynomialWeight a r q x ^ 2 * ‖∑ i, c i • f i x‖ ^ 2 := by
      rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans zero_le_one (polynomialWeight_one_le a r q x)),
        mul_pow, packetSynthesis_apply]
      simp only [smul_eq_mul]
    rw [hn]
    calc
      _ ≤ polynomialWeight a r q x ^ 2 * (D * C ^ 2 *
          ∑ i, ‖c i‖ ^ 2 * (rho i * lineEnvelope (s i) l (1 + 2 * q) x)) :=
        mul_le_mul_of_nonneg_left hsyn (sq_nonneg _)
      _ = D * C ^ 2 * ∑ i, (‖c i‖ ^ 2 * rho i) *
          (polynomialWeight a r q x ^ 2 * lineEnvelope (s i) l (1 + 2 * q) x) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (sq_nonneg C))
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left
          (polynomialWeight_sq_mul_envelope x (s i) a l r q 1 hl hr hlr (hcenter i))
          (mul_nonneg (sq_nonneg ‖c i‖) (hrho i).le)
        convert h using 1
        ring
  have hi (i : ι) : Integrable
      (fun x => (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x) :=
    (integrable_lineEnvelope_one (s i) l hl).const_mul _
  calc
    _ ≤ ∫ x, D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x :=
      integral_mono (((polynomialLocalization a r q (packetSynthesis c f)).memLp 2 volume).integrable_norm_pow
        (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
      simp_rw [integral_const_mul, integral_lineEnvelope_one _ l hl]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring

theorem packetSynthesis_fourier {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (packetSynthesis c f) ξ = ∑ i, c i * 𝓕 (f i) ξ := by
  have heq : (𝓕 (packetSynthesis c f) : SchwartzMap ℝ ℂ) = ∑ i, c i • 𝓕 (f i) := by
    rw [packetSynthesis, fourier_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact fourier_smul (c i) (f i)
  rw [heq]
  simp only [sum_apply, smul_apply, smul_eq_mul]

theorem packetSynthesis_fourier_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ)
    (hf : ∀ i, 𝓕 (f i) ξ = 0) : 𝓕 (packetSynthesis c f) ξ = 0 := by
  rw [packetSynthesis_fourier]
  simp only [hf, mul_zero, Finset.sum_const_zero]

end LipschitzHilbert

end

end OAI
