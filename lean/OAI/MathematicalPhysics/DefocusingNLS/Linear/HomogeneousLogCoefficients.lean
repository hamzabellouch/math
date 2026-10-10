import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetOperations
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEulerBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialLogarithmicSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularField

namespace OAI

/-! # The actual radial coefficients satisfy the finite Euler-row bounds

In logarithmic radius, the normalized profile contributes bounded jets.
The sole growing coefficient is the explicit Schrödinger diagonal.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

noncomputable def homogeneousLogFastDiagonal : End :=
  spectralTwoColumns (Complex.I / 2, 0) (0, -Complex.I / 2)

noncomputable def homogeneousLogRadialDamping (t : ℝ) : End :=
  (10 : End) + Real.exp (2 * t) • homogeneousLogFastDiagonal

noncomputable def homogeneousLogRadialStiffness (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (t : ℝ) : End :=
  Real.exp (2 * t) • spectralTwoColumns (-Complex.I * νp / 2, 0)
      (0, Complex.I * νm / 2) +
    spectralTwoColumns (-eta, 0) (0, -eta) +
    Real.exp (2 * t) • spectralTwoColumns
      (-spectralDiagonalCoefficient m (Q t), -star (spectralCrossCoefficient m (Q t)))
      (-spectralCrossCoefficient m (Q t), -star (spectralDiagonalCoefficient m (Q t)))

theorem homogeneousLogFastDiagonal_norm (w : V) :
    ‖homogeneousLogFastDiagonal w‖ = (1 / 2 : ℝ) * ‖w‖ := by
  simp only [homogeneousLogFastDiagonal, spectralTwoColumns_apply, Prod.norm_def,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    mul_zero, add_zero, zero_add, norm_mul, norm_div, norm_neg,
    Complex.norm_I, Complex.norm_ofNat]
  rw [← max_mul_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_comm]

theorem HasLogJetBound.spectralDiagonal {σ : ℝ} {q : ℝ → ℂ}
    (hq : HasLogJetBound σ q) (m : ℕ) :
    HasLogJetBound (2 * (m : ℝ) * σ) (fun t => spectralDiagonalCoefficient m (q t)) := by
  have hp := ((hq.pow m).mul (hq.conj.pow m)).const_mul (m + 1)
  have he : (m : ℝ) * σ + (m : ℝ) * σ = 2 * (m : ℝ) * σ := by ring
  simpa only [spectralDiagonalCoefficient, he, Nat.cast_add, Nat.cast_one, mul_assoc] using hp

theorem HasLogJetBound.spectralCross {σ : ℝ} {q : ℝ → ℂ}
    (hq : HasLogJetBound σ q) (m : ℕ) (hm : 1 ≤ m) :
    HasLogJetBound (2 * (m : ℝ) * σ) (fun t => spectralCrossCoefficient m (q t)) := by
  have hp := ((hq.pow (m + 1)).mul (hq.conj.pow (m - 1))).const_mul m
  have he : ((m + 1 : ℕ) : ℝ) * σ + ((m - 1 : ℕ) : ℝ) * σ = 2 * (m : ℝ) * σ := by
    rw [Nat.cast_add, Nat.cast_sub hm]
    push_cast
    ring
  simpa only [spectralCrossCoefficient, he, mul_assoc] using hp

theorem homogeneousLogRadialStiffness_bound (νp νm eta : ℂ) (m : ℕ)
    (hm : 1 ≤ m) (σ : ℝ) (hσ : 2 * (m : ℝ) * σ = -2)
    (Q : ℝ → ℂ) (hQ : HasLogJetBound σ Q) :
    HasLogJetBound 2 (homogeneousLogRadialStiffness νp νm eta m Q) := by
  have hD : HasLogJetBound (-2) (fun t => spectralDiagonalCoefficient m (Q t)) := by
    simpa only [hσ] using hQ.spectralDiagonal m
  have hC : HasLogJetBound (-2) (fun t => spectralCrossCoefficient m (Q t)) := by
    simpa only [hσ] using hQ.spectralCross m hm
  let F : ℝ → End := fun t => spectralTwoColumns
    (-spectralDiagonalCoefficient m (Q t), -star (spectralCrossCoefficient m (Q t)))
    (-spectralCrossCoefficient m (Q t), -star (spectralDiagonalCoefficient m (Q t)))
  have hF : HasLogJetBound (-2) F :=
    (hD.neg.pair hC.conj.neg).twoColumns (hC.neg.pair hD.conj.neg)
  have hsmall : HasLogJetBound 0 (fun t => Real.exp (2 * t) • F t) := by
    have hp := (HasLogJetBound.exponential 2 (1 : End)).mul hF
    have he : (fun t => (Real.exp (2 * t) • (1 : End)) * F t) =
        (fun t => Real.exp (2 * t) • F t) := by
      funext t
      rfl
    simpa only [he, show (2 : ℝ) + -2 = 0 by norm_num] using hp
  exact ((HasLogJetBound.exponential 2
    (spectralTwoColumns (-Complex.I * νp / 2, 0) (0, Complex.I * νm / 2))).add
      ((HasLogJetBound.const (spectralTwoColumns (-eta, 0) (0, -eta))).mono
        (by norm_num : (0 : ℝ) ≤ 2))).add (hsmall.mono (by norm_num : (0 : ℝ) ≤ 2))

theorem radialExteriorCanonical_logJetBound (ν b : ℂ) (m : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν m b L) (hb : b ≠ 0) :
    HasLogJetBound 0 (fun t => (radialExteriorCanonical ν m b L t).1) := by
  refine ⟨⟨L, radialExteriorODE_position_contDiffOn ν m _ L
    (fun t ht => ((radialExteriorCanonical_spec hX).2.2 t ht.le).2)⟩, ?_⟩
  intro k
  simpa only [zero_mul, Real.exp_zero, mul_one] using
    radialExteriorCanonical_derivatives_bounded ν b m L hX hb k

theorem homogeneousPhysicalProfile_logJetBound (ν : ℂ) (q : ℝ → ℂ)
    (hq : HasLogJetBound 0 q) :
    HasLogJetBound ν.re (fun t => Complex.exp (ν * (t : ℂ)) * q t) := by
  obtain ⟨L, hL⟩ := hq.smooth
  refine ⟨⟨L, (radial_complexExp_contDiff ν).contDiffOn.mul hL⟩, ?_⟩
  apply radial_logarithmic_product_bound ν q L hL
  intro k
  simpa only [zero_mul, Real.exp_zero, mul_one] using hq.bound k

theorem homogeneousCanonicalEulerRows_norm_lower (ν νp νm eta b : ℂ)
    (m n : ℕ) (hm : 1 ≤ m) (hν : 2 * (m : ℝ) * ν.re = -2)
    (L : ℝ) (hX : HasRadialExterior ν m b L) (hb : b ≠ 0) :
    ∀ᶠ t : ℝ in atTop, ∀ w : V,
      ((1 / 2 : ℝ) ^ n / 2) * Real.exp (2 * (n : ℝ) * t) * ‖w‖ ≤
        ‖(homogeneousEulerRows homogeneousLogRadialDamping
          (homogeneousLogRadialStiffness νp νm eta m
            (fun s => Complex.exp (ν * (s : ℂ)) *
              (radialExteriorCanonical ν m b L s).1)) (n + 1)).2 t w‖ := by
  exact homogeneousEulerRows_norm_lower _ _ homogeneousLogFastDiagonal
    (fun _ => (10 : End)) (HasLogJetBound.const _)
    (homogeneousLogRadialStiffness_bound νp νm eta m hm ν.re hν _
      (homogeneousPhysicalProfile_logJetBound ν _
        (radialExteriorCanonical_logJetBound ν b m L hX hb)))
    (fun _ => rfl) (1 / 2) (by norm_num) homogeneousLogFastDiagonal_norm n

end DefocusingNLS

end OAI
