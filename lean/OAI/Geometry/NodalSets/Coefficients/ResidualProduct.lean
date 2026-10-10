import OAI.Geometry.NodalSets.Coefficients.ResidualTaylor
import OAI.Geometry.NodalSets.Coefficients.SmoothFiniteResidual

namespace OAI

namespace Yau.Jets
open scoped ContDiff
noncomputable section

lemma DerivativeBound.enlarge {k : ℕ} {f : Coord → ℂ} {x : Coord} {A B : ℝ}
    (h : DerivativeBound k f x A) (hAB : A ≤ B) : DerivativeBound k f x B :=
  fun j hj ↦ (h j hj).trans hAB

lemma DerivativeBound.const_mul {k : ℕ} {f : Coord → ℂ} {x : Coord} {C : ℝ}
    (h : DerivativeBound k f x C) (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    DerivativeBound k (fun z ↦ c * f z) x (‖c‖ * C) := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (fun z ↦ c • f z) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le
    (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))).contDiffAt, norm_smul]
  exact mul_le_mul_of_nonneg_left (h j hj) (norm_nonneg c)

lemma DerivativeBound.scale_power {k : ℕ} {f : Coord → ℂ} {x : Coord}
    {C N p q : ℝ} (h : DerivativeBound k f x (C * N ^ p))
    (hf : ContDiff ℝ ∞ f) (hC : 0 ≤ C) (hN : 0 < N)
    (c : ℂ) (hc : ‖c‖ ≤ N ^ q) :
    DerivativeBound k (fun z ↦ c * f z) x (C * N ^ (p+q)) := by
  apply (h.const_mul hf c).enlarge
  calc
    _ ≤ N ^ q * (C * N ^ p) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [Real.rpow_add hN]; ring

lemma DerivativeBound.exponent_mono {k : ℕ} {f : Coord → ℂ} {x : Coord}
    {C N p q : ℝ} (h : DerivativeBound k f x (C * N ^ p))
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hpq : p ≤ q) :
    DerivativeBound k f x (C * N ^ q) :=
  h.enlarge (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hpq) hC)

lemma norm_complex_inv_pow {N : ℝ} (hN : 0 < N) (j : ℕ) :
    ‖((N : ℂ)⁻¹ ^ j)‖ = N ^ (-(j : ℝ)) := by
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN,
    inv_pow, Real.rpow_neg hN.le, Real.rpow_natCast]

theorem residual_times_exponential_bound {phi f : Coord → ℂ}
    (hp : ContDiff ℝ ∞ phi) (hf : ContDiff ℝ ∞ f) (k0 : ℕ) (x : Coord)
    {C D N K S : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hN : 1 ≤ N)
    (hb : DerivativeBound k0 f x (C * N ^ (-K-k0)))
    (hphase : DerivativeBound k0 phi x D) (hgap : (phi x).re ≤ S) :
    DerivativeBound k0 (fun z ↦ f z * waveExp phi N z) x
      (2 ^ k0 * C * (k0.factorial : ℝ) * D ^ k0 * N ^ (-K) * Real.exp (N*S)) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let Q := (k0.factorial : ℝ) * D ^ k0
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have he : DerivativeBound k0 (waveExp phi N) x (Q * N ^ k0 * Real.exp (N*S)) := by
    intro j hj
    apply (waveExp_derivative_bound hp j x hD hN
      (fun i _ hi ↦ hphase i (hi.trans hj))).trans
    have hfact : (j.factorial : ℝ) ≤ k0.factorial := by exact_mod_cast Nat.factorial_le hj
    have hpow : D ^ j ≤ D ^ k0 := pow_le_pow_right₀ hD hj
    have hNpow : N ^ j ≤ N ^ k0 := pow_le_pow_right₀ hN hj
    have hexp : Real.exp (N * (phi x).re) ≤ Real.exp (N*S) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgap hNp.le)
    dsimp [Q]
    gcongr
  have hh := hb.mul hf (waveExp_contDiff hp N) (by positivity) (by positivity) he
  convert hh using 1
  rw [show N ^ (-K) = N ^ (-K-k0) * N ^ k0 by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNp]
    congr 1
    ring]
  dsimp [Q]
  ring

end
end Yau.Jets

end OAI
