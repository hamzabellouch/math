import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.OddPowerNonlinearity
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! Uniform finite-order bounds for the polynomial nonlinearity on strictly
subunit balls.  Complexifying the two real variables permits Cauchy estimates
with constants independent of the power. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

noncomputable def homogeneousSubunitPolynomial (n : ℕ) (x : ℂ × ℂ) : ℂ :=
  x.1 ^ (n + 1) * x.2 ^ n

theorem homogeneousSubunitPolynomial_contDiff (n : ℕ) :
    ContDiff ℂ ∞ (homogeneousSubunitPolynomial n) := by
  exact (contDiff_fst.pow (n + 1)).mul (contDiff_snd.pow n)

theorem homogeneousSubunitPolynomial_norm (n : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (x : ℂ × ℂ) (hx : ‖x‖ ≤ ρ) :
    ‖homogeneousSubunitPolynomial n x‖ ≤ ρ ^ (2 * n + 1) := by
  have hx₁ : ‖x.1‖ ≤ ρ := (norm_fst_le x).trans hx
  have hx₂ : ‖x.2‖ ≤ ρ := (norm_snd_le x).trans hx
  calc
    _ = ‖x.1‖ ^ (n + 1) * ‖x.2‖ ^ n := by
      simp only [homogeneousSubunitPolynomial, norm_mul, norm_pow]
    _ ≤ ρ ^ (n + 1) * ρ ^ n := by gcongr
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The gap between the two radii absorbs every fixed derivative order. -/
theorem homogeneousSubunitPolynomial_derivatives (k : ℕ) (ρ σ : ℝ)
    (hρ : 0 ≤ ρ) (hρσ : ρ < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x : ℂ × ℂ, ‖x‖ ≤ ρ →
      ‖iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) x‖ ≤
        C * σ ^ (2 * n + 1) := by
  induction k generalizing ρ with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro n x hx
    rw [norm_iteratedFDeriv_zero, one_mul]
    exact homogeneousSubunitPolynomial_norm n σ (hρ.trans hρσ.le) x
      (hx.trans hρσ.le)
  | succ k ih =>
    let τ : ℝ := (ρ + σ) / 2
    have hρτ : ρ < τ := by dsimp only [τ]; linarith
    have hτσ : τ < σ := by dsimp only [τ]; linarith
    obtain ⟨B, hB, hjet⟩ := ih τ (hρ.trans hρτ.le) hτσ
    let δ : ℝ := τ - ρ
    have hδ : 0 < δ := sub_pos.mpr hρτ
    refine ⟨2 * B / δ, by positivity, ?_⟩
    intro n x hx
    have hxτ : ‖x‖ ≤ τ := hx.trans hρτ.le
    have hd : Differentiable ℂ (iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n)) :=
      ContDiff.differentiable_iteratedFDeriv (n := ∞) (by exact_mod_cast ENat.natCast_lt_top k)
        (homogeneousSubunitPolynomial_contDiff n)
    have hmaps : MapsTo (iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n))
        (Metric.ball x δ)
        (Metric.closedBall (iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) x)
          (2 * (B * σ ^ (2 * n + 1)))) := by
      intro y hy
      have hxy : ‖y - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have hyτ : ‖y‖ ≤ τ := by
        have hn := norm_add_le (y - x) x
        rw [sub_add_cancel] at hn
        dsimp only [δ] at hxy
        linarith
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        _ ≤ ‖iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) y‖ +
            ‖iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) x‖ := norm_sub_le _ _
        _ ≤ B * σ ^ (2 * n + 1) + B * σ ^ (2 * n + 1) :=
          add_le_add (hjet n y hyτ) (hjet n x hxτ)
        _ = _ := by ring
    have hb := Complex.norm_fderiv_le_div_of_mapsTo_ball hd.differentiableOn hmaps hδ
    calc
      _ = ‖fderiv ℂ (iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n)) x‖ :=
        norm_fderiv_iteratedFDeriv.symm
      _ ≤ 2 * (B * σ ^ (2 * n + 1)) / δ := hb
      _ = _ := by ring

/-- All fixed-order complexified jets tend uniformly to zero on a subunit ball. -/
theorem homogeneousSubunitPolynomial_derivatives_small (k : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℂ × ℂ, ‖x‖ ≤ ρ →
      ‖iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) x‖ < ε := by
  let σ : ℝ := (ρ + 1) / 2
  have hρσ : ρ < σ := by dsimp only [σ]; linarith
  have hσ : 0 ≤ σ := hρ.trans hρσ.le
  have hσ1 : σ < 1 := by dsimp only [σ]; linarith
  obtain ⟨C, hC, hjet⟩ := homogeneousSubunitPolynomial_derivatives k ρ σ hρ hρσ
  have ht : Tendsto (fun n : ℕ => C * σ ^ (2 * n + 1)) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg σ)
      (pow_lt_one₀ hσ hσ1 (by decide : 2 ≠ 0))
    convert hp.mul_const (C * σ) using 1
    · funext n
      rw [pow_succ, pow_mul]
      ring
    · ring_nf
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro x hx
  exact (hjet n x hx).trans_lt hn

theorem homogeneousSubunitPolynomial_diagonal (n : ℕ) (z : ℂ) :
    homogeneousSubunitPolynomial n (z, star z) = oddPowerNonlinearity n z := rfl

noncomputable def homogeneousSubunitDiagonal : ℂ →ₗᵢ[ℝ] ℂ × ℂ where
  toLinearMap := ((ContinuousLinearMap.id ℝ ℂ).prod
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap).toLinearMap
  norm_map' z := by simp [Prod.norm_def]

theorem homogeneousSubunitPolynomial_real_norm (n k : ℕ) (x : ℂ × ℂ) :
    ‖iteratedFDeriv ℝ k (homogeneousSubunitPolynomial n) x‖ =
      ‖iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) x‖ := by
  have hc : ContDiffAt ℂ k (homogeneousSubunitPolynomial n) x :=
    (homogeneousSubunitPolynomial_contDiff n).contDiffAt.of_le (by simp)
  have he := hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)
  change (iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) x).restrictScalars ℝ =
    iteratedFDeriv ℝ k (homogeneousSubunitPolynomial n) x at he
  rw [← he, ContinuousMultilinearMap.norm_restrictScalars]

theorem homogeneousSubunitPolynomial_oddPower_bound (n k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (oddPowerNonlinearity n) z‖ ≤
      ‖iteratedFDeriv ℂ k (homogeneousSubunitPolynomial n) (z, star z)‖ := by
  have he : oddPowerNonlinearity n =
      homogeneousSubunitPolynomial n ∘ homogeneousSubunitDiagonal.toContinuousLinearMap := rfl
  rw [he, homogeneousSubunitDiagonal.toContinuousLinearMap.iteratedFDeriv_comp_right
    ((homogeneousSubunitPolynomial_contDiff n).restrict_scalars ℝ) z (by simp)]
  exact (ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _
    (fun _ => homogeneousSubunitDiagonal)).trans_eq
      (homogeneousSubunitPolynomial_real_norm n k (z, star z))

/-- Uniform decay holds for the actual real odd-power derivatives, including
the real-linear derivative used in the spectral potential. -/
theorem homogeneous_oddPower_derivatives_subunit (k : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ ρ →
      ‖iteratedFDeriv ℝ k (oddPowerNonlinearity n) z‖ < ε := by
  filter_upwards [homogeneousSubunitPolynomial_derivatives_small k ρ hρ hρ1 ε hε]
    with n hn
  intro z hz
  apply (homogeneousSubunitPolynomial_oddPower_bound n k z).trans_lt
  apply hn (z, star z)
  simpa only [Prod.norm_def, norm_star, max_self] using hz

end DefocusingNLS

end OAI
