import Mathlib
import OAI.Analysis.WeakInfiniteness.MatrixCutToolkit

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectralRamp_positiveCut_plateau (a : A) (ha : IsSelfAdjoint a)
    {α : ℝ} (hα : 0 < α) :
    cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) a)*positiveCut (7*α/8) a =
      positiveCut (7*α/8) a := by
  have h0 : max (0-α/2) 0 = 0 := max_eq_right (by linarith)
  have h1 : max (0-7*α/8) 0 = 0 := max_eq_right (by linarith)
  rw [positiveCut, ← cfcₙ_comp (spectralRamp (α/8)) (fun s : ℝ => max (s-α/2) 0) a
    (continuous_spectralRamp _).continuousOn (spectralRamp_eq_zero (by positivity) (by positivity))
    (by fun_prop) h0 ha]
  rw [positiveCut, ← cfcₙ_mul (spectralRamp (α/8) ∘ (fun s : ℝ => max (s-α/2) 0)) (fun s : ℝ => max (s-7*α/8) 0) a ((continuous_spectralRamp _).comp (by fun_prop)).continuousOn (by
    change spectralRamp (α/8) (max (0-α/2) 0)=0
    rw [h0]
    exact spectralRamp_eq_zero (by positivity) (by positivity))
    (by fun_prop) h1]
  congr 1
  funext s
  change spectralRamp (α/8) (max (s-α/2) 0)*max (s-7*α/8) 0 = max (s-7*α/8) 0
  by_cases hs : s ≤ 7*α/8
  · rw [max_eq_right (by linarith : s-7*α/8 ≤ 0), mul_zero]
  · rw [spectralRamp_eq_one (by positivity) (by have := le_max_left (s-α/2) 0; linarith), one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positiveCut_ne_zero_of_lt_norm {b : H →L[ℂ] H} (hb : 0 ≤ b)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδb : δ < ‖b‖) : positiveCut δ b ≠ 0 := by
  have : Nontrivial (H →L[ℂ] H) := ⟨⟨b, 0, by intro h; rw [h, norm_zero] at hδb; linarith⟩⟩
  have hm := CStarAlgebra.norm_mem_spectrum_of_nonneg b hb
  have hle := norm_apply_le_norm_cfcₙ (fun s : ℝ => max (s-δ) 0) b
    (spectrum_subset_quasispectrum ℝ b hm) (by fun_prop) (max_eq_right (by linarith)) hb.isSelfAdjoint
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), max_eq_left (by linarith)] at hle
  intro hz
  change positiveCut δ b = 0 at hz
  change ‖b‖-δ ≤ ‖positiveCut δ b‖ at hle
  rw [hz, norm_zero] at hle
  linarith

lemma exists_plateau_vector {b : H →L[ℂ] H} (hb : 0 ≤ b)
    {α : ℝ} (hα : 0 < α) (hαb : α ≤ ‖b‖) :
    ∃ ξ : H, ‖ξ‖ = 1 ∧ cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) b) ξ = ξ := by
  let z := positiveCut (7*α/8) b
  have hz : z ≠ 0 := positiveCut_ne_zero_of_lt_norm hb (by positivity) (by linarith)
  obtain ⟨v, hv⟩ : ∃ v : H, z v ≠ 0 := by
    by_contra! h
    apply hz
    ext v
    exact h v
  let ξ := (‖z v‖⁻¹ : ℂ) • z v
  refine ⟨ξ, ?_, ?_⟩
  · dsimp only [ξ]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · have he := congrArg (fun T : H →L[ℂ] H => T v)
      (spectralRamp_positiveCut_plateau b hb.isSelfAdjoint hα)
    change cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) b) (z v) = z v at he
    dsimp only [ξ]
    rw [map_smul, he]

end

end WeakPureInfiniteness
end

end OAI
