import OAI.Analysis.KadisonKastler.SupportBounds
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

namespace OAI

/-!
# Finite phase randomization

Orthogonal scalar phases turn a coefficient column into a random vector
with exactly the same mean square. This is the finite Parseval identity
used for the randomized commutator coefficients in §3.
-/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Ω W : Type*} [Fintype Ω] [Fintype W] [DecidableEq W]

def finitePhaseSum (χ : W → Ω → ℂ) (v : W → H) (t : Ω) : H :=
  ∑ w, χ w t • v w

theorem finitePhaseSum_inner (χ : W → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t : Ω, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v u : W → H) :
    (𝔼 t : Ω, inner ℂ (finitePhaseSum χ v t) (finitePhaseSum χ u t)) =
      ∑ w, inner ℂ (v w) (u w) := by
  simp_rw [finitePhaseSum, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    starRingEnd_apply, ← mul_assoc, Finset.expect_sum_comm, ← Finset.expect_mul]
  calc
    _ = ∑ i : W, ∑ j : W, (if i = j then (1 : ℂ) else 0) *
        inner ℂ (v i) (u j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [hχ]
    _ = _ := by simp

/-- Parseval's identity for any finite family of orthogonal phases. -/
theorem finitePhaseSum_mean_square (χ : W → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t : Ω, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : W → H) :
    (𝔼 t : Ω, ‖finitePhaseSum χ v t‖ ^ 2) = ∑ w, ‖v w‖ ^ 2 := by
  let reMap : ℂ →ₗ[ℚ≥0] ℝ := Complex.reLm.restrictScalars ℚ≥0
  have h := congrArg reMap (finitePhaseSum_inner χ hχ v v)
  rw [map_expect, map_sum] at h
  change (𝔼 t : Ω, RCLike.re (inner ℂ (finitePhaseSum χ v t) (finitePhaseSum χ v t))) =
    ∑ w, RCLike.re (inner ℂ (v w) (v w)) at h
  simpa only [← norm_sq_eq_re_inner] using h

omit [Fintype W] in
/-- Distinct additive characters supply the required orthogonal phases. -/
theorem additiveCharacters_orthogonal {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : W → AddChar G ℂ) (hχ : Function.Injective χ) (i j : W) :
    (𝔼 t : G, star (χ i t) * χ j t) = if i = j then 1 else 0 := by
  have h := AddChar.wInner_cWeight_eq_boole (χ i) (χ j)
  simpa only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
    hχ.eq_iff, starRingEnd_apply, mul_comm] using h

theorem additiveCharacters_mean_square {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : W → AddChar G ℂ) (hχ : Function.Injective χ) (v : W → H) :
    (𝔼 t : G, ‖finitePhaseSum (fun w => χ w) v t‖ ^ 2) = ∑ w, ‖v w‖ ^ 2 :=
  finitePhaseSum_mean_square _ (additiveCharacters_orthogonal χ hχ) v

/-- A finite orthogonal phase average preserves any coefficient-column
bound, with no factor for the number of coefficients. -/
theorem finitePhaseSum_rms_le (χ : W → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t : Ω, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : W → H) {C : ℝ} (hv : ‖WithLp.toLp 2 v‖ ≤ C) :
    Real.sqrt (𝔼 t : Ω, ‖finitePhaseSum χ v t‖ ^ 2) ≤ C := by
  rw [finitePhaseSum_mean_square χ hχ, ← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)]
  exact hv

/-- If every phase polynomial is unitary, its coefficient column is an
isometry. This proves the coefficient-column identity used before clipping. -/
theorem unitary_phase_coefficient_column [CompleteSpace H] [Nonempty Ω]
    (χ : W → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t : Ω, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (K : W → H →L[ℂ] H)
    (hK : ∀ t, (∑ w, χ w t • K w) ∈ unitary (H →L[ℂ] H)) (x : H) :
    ‖WithLp.toLp 2 (fun w => K w x)‖ = ‖x‖ := by
  have hphase (t : Ω) : ‖finitePhaseSum χ (fun w => K w x) t‖ = ‖x‖ := by
    have heq : finitePhaseSum χ (fun w => K w x) t = (∑ w, χ w t • K w) x := by
      simp [finitePhaseSum, _root_.sum_apply]
    rw [heq]
    exact ContinuousLinearMap.norm_map_of_mem_unitary (hK t) x
  have hsq : ‖WithLp.toLp 2 (fun w => K w x)‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, ← finitePhaseSum_mean_square χ hχ]
    simp only [hphase]
    simp
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun w => K w x)), norm_nonneg x]

end

end KadisonKastler

end OAI
