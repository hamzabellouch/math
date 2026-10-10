import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.Bessel

namespace OAI

noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
namespace TamingCompatibility.EuclideanGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
open TemperedDistribution

lemma multiplier_add {g h : E → ℂ} (hg : g.HasTemperateGrowth)
    (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g + h) u =
      fourierMultiplierCLM F g u + fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh,
    add_apply, FourierTransform.fourierInv_add]

lemma bessel_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u = u +
      fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have hs : (fun x : E => (((1 + ‖x‖^2) ^ (2 / 2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    ext x
    simp
  rw [besselPotential, hs, multiplier_add (by fun_prop) (by fun_prop)]
  simp

def helmholtz (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  u - ((2 * Real.pi)^2)⁻¹ • (Δ u)

lemma bessel_two_eq_helmholtz (u : 𝓢'(E,F)) :
    besselPotential E F 2 u = helmholtz u := by
  rw [bessel_two, helmholtz, laplacian_eq_fourierMultiplierCLM, smul_smul]
  have hc : (2 * Real.pi)^2 ≠ 0 := by positivity
  rw [mul_neg, inv_mul_cancel₀ hc]
  simp [Complex.ofReal_pow]

theorem helmholtz_green (f : 𝓢'(E,F)) :
    helmholtz (besselPotential E F (-2) f) = f := by
  rw [← bessel_two_eq_helmholtz, besselPotential_besselPotential_apply]
  norm_num

theorem green_helmholtz (f : 𝓢'(E,F)) :
    besselPotential E F (-2) (helmholtz f) = f := by
  rw [← bessel_two_eq_helmholtz, besselPotential_besselPotential_apply]
  norm_num

variable [CompleteSpace F]

theorem memSobolev_helmholtz_iff (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E,F)) :
    MemSobolev s p (helmholtz u) ↔ MemSobolev (s + 2) p u := by
  rw [← bessel_two_eq_helmholtz, memSobolev_besselPotential_iff, add_comm s 2]

theorem green_regularity {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : 𝓢'(E,F)}
    (hf : MemSobolev s p f) : MemSobolev (s + 2) p (besselPotential E F (-2) f) := by
  rw [memSobolev_besselPotential_iff]
  convert hf using 1
  ring

end TamingCompatibility.EuclideanGreen

namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev basisIndex (E : Type*) [AddCommGroup E] [Module ℝ E] := Fin (Module.finrank ℝ E)

def recover (s : ℝ) (u : H E F s) (du : basisIndex E → H E F s) : H E F (s+1) :=
  reindex (s-1) (s+1) (inclusion (show s-1 ≤ s by linarith) u -
    ((2*Real.pi)^2)⁻¹ • ∑ i, derivative s (stdOrthonormalBasis ℝ E i) (du i))

lemma recover_distribution (s : ℝ) (u : H E F s) (du : basisIndex E → H E F s) :
    toDistribution E F (s+1) (recover s u du) = besselPotential E F (-2)
      (toDistribution E F s u - ((2*Real.pi)^2)⁻¹ •
        ∑ i, ∂_{stdOrthonormalBasis ℝ E i} (toDistribution E F s (du i))) := by
  rw [recover, toDistribution_reindex]
  have he : s-1-(s+1) = -2 := by ring
  rw [he, map_sub, ContinuousLinearMap.map_smul_of_tower, map_sum, toDistribution_inclusion]
  simp only [toDistribution_derivative]

lemma recover_gradient (s : ℝ) (u : H E F (s+1)) :
    recover s (inclusion (show s ≤ s+1 by linarith) u)
      (fun i => derivative (s+1) (stdOrthonormalBasis ℝ E i) u) = u := by
  apply toDistribution_injective (s+1)
  rw [recover_distribution, toDistribution_inclusion]
  have hd (i : basisIndex E) :
      toDistribution E F s (derivative (s+1) (stdOrthonormalBasis ℝ E i) u) =
        ∂_{stdOrthonormalBasis ℝ E i} (toDistribution E F (s+1) u) := by
    have h := toDistribution_derivative (s+1) (stdOrthonormalBasis ℝ E i) u
    have he : s+1-1 = s := by ring
    rw [he] at h
    exact h
  simp only [hd]
  rw [← TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  change besselPotential E F (-2) (EuclideanGreen.helmholtz (toDistribution E F (s+1) u)) = _
  exact EuclideanGreen.green_helmholtz _

lemma recover_norm_le (s : ℝ) (u : H E F s) (du : basisIndex E → H E F s) :
    ‖recover s u du‖ ≤ ‖u‖ + |((2*Real.pi)^2)⁻¹| *
      ∑ i, ‖derivative (F := F) s (stdOrthonormalBasis ℝ E i)‖ * ‖du i‖ := by
  rw [recover, (reindex (s-1) (s+1)).norm_map]
  apply (norm_sub_le _ _).trans
  apply add_le_add (inclusion_norm_le _ u)
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
    ContinuousLinearMap.le_opNorm _ _))

theorem norm_le_gradient (s : ℝ) (u : H E F (s+1)) :
    ‖u‖ ≤ ‖inclusion (show s ≤ s+1 by linarith) u‖ + |((2*Real.pi)^2)⁻¹| *
      ∑ i, ‖derivative (F := F) s (stdOrthonormalBasis ℝ E i)‖ *
        ‖derivative (s+1) (stdOrthonormalBasis ℝ E i) u‖ := by
  have h := recover_norm_le s (inclusion (show s ≤ s+1 by linarith) u)
    (fun i => derivative (s+1) (stdOrthonormalBasis ℝ E i) u)
  rw [recover_gradient] at h
  exact h

end TamingCompatibility.HilbertSobolev
end

end OAI
