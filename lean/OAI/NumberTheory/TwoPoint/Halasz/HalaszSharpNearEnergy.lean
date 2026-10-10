import OAI.NumberTheory.TwoPoint.Halasz.HalaszSharpNearScalars

namespace OAI

/-! Near-center energy with the exceptional prefix density squared.
The phase-shaped approximation is applied to the typical coefficient
itself, before the Fourier energy is integrated. -/

namespace TwoPointCorrelations

open Finset MeasureTheory

lemma halasz_sharp_near_energy (B F : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (C₁ C₂ D L M R : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hD : 0 ≤ D)
    (hL : 1 ≤ L) (hR : 0 ≤ R)
    (hcenter : ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean F 0 k‖ ≤ C₁*(Real.exp (-M/2)+Real.log L/L)*k)
    (hprefix : ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B 0 k - halaszPhaseMean F 0 k‖ ≤ C₂*R*k)
    (hnear : ∀ u ∈ Set.Icc (-(L^(1/16:ℝ))) (L^(1/16:ℝ)), ∀ k ∈ Icc N (2*N),
      ‖halaszPhaseMean B u k -
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*halaszPhaseMean B 0 k‖ ≤
          (D*L^(-3/50:ℝ))*k) :
    (∫ u in -(L^(1/16:ℝ))..(L^(1/16:ℝ)), ‖mrtDyadicPolynomial B N u‖^2) ≤
      (600*Real.pi*C₁^2+300*Real.pi*C₂^2+100*D^2)*
        (R^2+Real.exp (-M)+L^(-1/32:ℝ)) := by
  let A := C₁*(Real.exp (-M/2)+Real.log L/L)+C₂*R
  have hL0 : 0 < L := by linarith
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg hC₁ (add_nonneg (Real.exp_pos _).le
        (div_nonneg (Real.log_nonneg hL) hL0.le))) (mul_nonneg hC₂ hR)
  have hc : ∀ k ∈ Icc N (2*N), ‖halaszPhaseMean B 0 k‖ ≤ A*k := by
    intro k hk
    calc
      _ = ‖(halaszPhaseMean B 0 k-halaszPhaseMean F 0 k)+halaszPhaseMean F 0 k‖ := by
        congr 1
        abel
      _ ≤ ‖halaszPhaseMean B 0 k-halaszPhaseMean F 0 k‖+‖halaszPhaseMean F 0 k‖ :=
        norm_add_le _ _
      _ ≤ C₂*R*k+C₁*(Real.exp (-M/2)+Real.log L/L)*k :=
        add_le_add (hprefix k hk) (hcenter k hk)
      _ = A*k := by dsimp [A]; ring
  have hh := halasz_near_dyadic_energy B hN A (D*L^(-3/50:ℝ))
    (L^(1/16:ℝ)) hA (mul_nonneg hD (Real.rpow_nonneg hL0.le _))
    (Real.rpow_nonneg hL0.le _) hc hnear
  exact hh.trans (halasz_sharp_near_scalar C₁ C₂ D L M R hL)

end TwoPointCorrelations

end OAI
