import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.FourierMeanZeroTests

namespace OAI

/-!
# Fourier jets and Schwartz moments

Iterated directional Fourier derivatives correspond to polynomially weighted
Schwartz functions. Evaluating these derivatives at zero expresses Fourier jets
as integrable moments with the appropriate Fourier normalization factor.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform

def fourierDerivativeFactor : ℂ := -(2 * Real.pi * Complex.I)

def fourierMomentSchwartz {d : ℕ} :
    {n : ℕ} → (Fin n → Ambient d) → 𝓢(Ambient d, ℂ) → 𝓢(Ambient d, ℂ)
  | 0, _, g => g
  | n + 1, m, g => fourierDerivativeFactor •
      smulLeftCLM ℂ (inner ℝ · (m 0)) (fourierMomentSchwartz (n := n) (Fin.tail m) g)

theorem fourierMomentSchwartz_apply {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) (x : Ambient d) :
    fourierMomentSchwartz m g x = fourierDerivativeFactor ^ n *
      (∏ i, (inner ℝ x (m i) : ℂ)) * g x := by
  induction n with
  | zero => simp [fourierMomentSchwartz]
  | succ n ih =>
    have hm : (inner ℝ · (m 0)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (m 0)).hasTemperateGrowth
    simp only [fourierMomentSchwartz, smul_apply]
    erw [smulLeftCLM_apply_apply hm, ih]
    erw [Complex.real_smul]
    rw [smul_eq_mul, Fin.prod_univ_succ, pow_succ]
    simp only [Fin.tail_def]
    ring

theorem iteratedLineDeriv_fourier_moment {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) :
    ∂^{m} (𝓕 g) = 𝓕 (fourierMomentSchwartz m g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, ih, lineDerivOp_fourier_eq]
    rfl

theorem fourier_jet_at_zero_eq_moment {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) :
    iteratedFDeriv ℝ n (𝓕 g : 𝓢(Ambient d, ℂ)) 0 m =
      ∫ x, fourierDerivativeFactor ^ n * (∏ i, (inner ℝ x (m i) : ℂ)) * g x := by
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedLineDeriv_fourier_moment, schwartz_fourier_at_zero]
  simp_rw [fourierMomentSchwartz_apply]

theorem fourier_jet_moment_integrable {d n : ℕ} (m : Fin n → Ambient d)
    (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun x => fourierDerivativeFactor ^ n *
      (∏ i, (inner ℝ x (m i) : ℂ)) * g x) := by
  exact (fourierMomentSchwartz m g).integrable.congr
    (Filter.Eventually.of_forall (fourierMomentSchwartz_apply m g))

end

end RieszRectifiability

end OAI
