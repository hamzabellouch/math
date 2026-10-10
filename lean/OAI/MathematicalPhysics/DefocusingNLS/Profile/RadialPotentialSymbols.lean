import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSymbolProducts
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds

namespace OAI

/-! Both coefficients of the true finite-power linearization have symbol order minus two. -/

open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def radialPotentialDiagonal (m : ℕ) (Q : E → ℂ) (x : E) : ℂ :=
  ((m+1 : ℕ) : ℂ)*(Q x)^m*(star (Q x))^m

noncomputable def radialPotentialAntilinear (m : ℕ) (Q : E → ℂ) (x : E) : ℂ :=
  (m : ℂ)*(Q x)^(m+1)*(star (Q x))^(m-1)

theorem radialPotential_decomposition (m : ℕ) (Q : E → ℂ) (x : E) (v : ℂ) :
    oddPowerDerivative m (Q x) v =
      radialPotentialDiagonal m Q x*v+radialPotentialAntilinear m Q x*star v := by
  simp [oddPowerDerivative,radialPotentialDiagonal,radialPotentialAntilinear,smul_eq_mul]

theorem radialPotentialDiagonal_symbol {σ : ℝ} {Q : E → ℂ}
    (hQ : HasCartesianSymbol σ Q) (m : ℕ) :
    HasCartesianSymbol ((2*(m : ℝ))*σ) (radialPotentialDiagonal m Q) := by
  have h := ((hQ.pow m).mul (hQ.conj.pow m)).const_mul ((m+1 : ℕ) : ℂ)
  have he : (m : ℝ)*σ+(m : ℝ)*σ=(2*(m : ℝ))*σ := by ring
  change HasCartesianSymbol ((2*(m : ℝ))*σ) (fun x => ((m+1 : ℕ) : ℂ)*(Q x)^m*(star (Q x))^m)
  simpa only [he,mul_assoc] using h

theorem radialPotentialAntilinear_symbol {σ : ℝ} {Q : E → ℂ}
    (hQ : HasCartesianSymbol σ Q) (m : ℕ) (hm : 1 ≤ m) :
    HasCartesianSymbol ((2*(m : ℝ))*σ) (radialPotentialAntilinear m Q) := by
  have h := ((hQ.pow (m+1)).mul (hQ.conj.pow (m-1))).const_mul (m : ℂ)
  have he : ((m+1 : ℕ) : ℝ)*σ+((m-1 : ℕ) : ℝ)*σ=(2*(m : ℝ))*σ := by
    rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub hm,Nat.cast_one]
    ring
  change HasCartesianSymbol ((2*(m : ℝ))*σ) (fun x => (m : ℂ)*(Q x)^(m+1)*(star (Q x))^(m-1))
  simpa only [he,mul_assoc] using h

theorem radialMatchedPotential_symbols (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    HasCartesianSymbol (-2) (radialPotentialDiagonal (n+radialInnerShootingThreshold)
      (radialMatchedCartesian n z)) ∧
    HasCartesianSymbol (-2) (radialPotentialAntilinear (n+radialInnerShootingThreshold)
      (radialMatchedCartesian n z)) := by
  have hQ := radialMatchedCartesian_hasCartesianSymbol n z hX hz
  have hp := radialShootingInner_power_pos n (profileMatchingParameter z)
  have he : (2*((n+radialInnerShootingThreshold : ℕ) : ℝ))*(-2*radialShootingA n)= -2 := by
    nlinarith [radialShootingA_power n (profileMatchingParameter z)]
  exact ⟨by simpa only [he] using radialPotentialDiagonal_symbol hQ (n+radialInnerShootingThreshold),
    by simpa only [he] using radialPotentialAntilinear_symbol hQ (n+radialInnerShootingThreshold) hp⟩

end DefocusingNLS

end OAI
