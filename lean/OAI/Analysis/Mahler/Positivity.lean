import OAI.Analysis.Mahler.Hessian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef

namespace OAI

open Complex
open scoped BigOperators ComplexOrder
local notation "conj" => starRingEnd ℂ
namespace Mahler
variable {ι : Type*} [Fintype ι]

lemma finite_cauchy_schwarz (a b : ι → ℂ) :
    normSq (∑ j, conj (a j) * b j) ≤
      (∑ j, normSq (a j)) * (∑ j, normSq (b j)) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.norm_sq_eq,
    mul_pow, Complex.normSq_eq_norm_sq, mul_comm] using hs

noncomputable def pairing (a b : ι → ℂ) : ℂ := ∑ j, conj (a j) * b j
noncomputable def sizeSq (a : ι → ℂ) : ℝ := ∑ j, normSq (a j)
noncomputable def logKernel (a b c : ι → ℂ) : ℂ :=
  ((sizeSq a : ℂ) * pairing b c - pairing a c * pairing b a) / (sizeSq a : ℂ)^2

lemma pairing_conj (a b : ι → ℂ) : conj (pairing a b) = pairing b a := by
  simp [pairing, map_sum, map_mul, mul_comm]
lemma pairing_self (a : ι → ℂ) : pairing a a = (sizeSq a : ℂ) := by
  simp [pairing, sizeSq, Complex.normSq_eq_conj_mul_self]
lemma logKernel_conj (a b c : ι → ℂ) : conj (logKernel a b c) = logKernel a c b := by
  simp only [logKernel, map_div₀, map_sub, map_mul, map_pow, pairing_conj, conj_ofReal]
  ring

lemma logKernel_diagonal (a b : ι → ℂ) :
    logKernel a b b = (((sizeSq a * sizeSq b - normSq (pairing a b)) /
      sizeSq a ^ 2 : ℝ) : ℂ) := by
  rw [logKernel, pairing_self]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, pairing_conj]
  ring

lemma logKernel_nonneg (a b : ι → ℂ) : 0 ≤ logKernel a b b := by
  rw [logKernel_diagonal, Complex.nonneg_iff]
  simp only [ofReal_re, ofReal_im, and_true]
  exact div_nonneg (sub_nonneg.mpr (finite_cauchy_schwarz a b)) (sq_nonneg _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

lemma mixed_logTau_kernel {f : ι → E → ℂ} {x v w : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    dbar (fun y => dz (logTau f) y v) x w =
      logKernel (fun j => f j x) (fun j => fderiv ℂ (f j) x w)
        (fun j => fderiv ℂ (f j) x v) := by
  exact mixed_logTau hf ht

/-- Nonnegativity of the actual Levi form, proved using Cauchy-Schwarz. -/
theorem levi_logTau_nonneg {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) (ht : 0 < tau f x) :
    0 ≤ dbar (fun y => dz (logTau f) y v) x v := by
  rw [mixed_logTau_kernel hf ht]
  exact logKernel_nonneg _ _

/-- The actual Levi form of tau is a sum of squared moduli. -/
theorem levi_energy_nonneg {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, AnalyticAt ℂ (f j) x) :
    0 ≤ dbar (fun y => dz (energy f) y v) x v := by
  rw [mixed_energy hf]
  change 0 ≤ pairing (fun j => fderiv ℂ (f j) x v) _
  rw [pairing_self, Complex.nonneg_iff]
  simp only [ofReal_re, ofReal_im, and_true]
  exact Finset.sum_nonneg (fun j _ => normSq_nonneg _)

end Mahler

end OAI
