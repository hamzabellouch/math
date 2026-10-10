import OAI.Probability.InvariantIsing.Cavity.CavityFiniteRoot
import OAI.Probability.InvariantIsing.Cavity.CavityProjectedInnovation

namespace OAI

/-! Scalar projections of the innovations and the ordinary residual for
the actual finite spectral cavity blocks. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

theorem cavity_finite_projected_innovation {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x y ζ : ℝ) (hx : 0 < x) (hy : 0 < y) (hζ : ζ ≠ 0)
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hΔ : (finiteInverse rho lam hrho hsum x • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹ -
      (finiteInverse rho lam hrho hsum y • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹ = ζ • S) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let K := A - A₀
    let P := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let C := (finiteInverse rho lam hrho hsum y • 1 - A₀)⁻¹
    L.transpose * ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) * L =
      ((finiteR rho lam hrho hsum x - finiteR rho lam hrho hsum y) / ζ) • 1 := by
  intro D E A A₀ L K P C
  have hK : K.transpose = K := by
    dsimp only [K, A, A₀, D, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hC : C.transpose = C := by
    simp only [C, A₀, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.diagonal_transpose]
  exact cavity_projected_innovation_covariance K P C S L (E.transpose * D * E)
    (finiteR rho lam hrho hsum x) (finiteR rho lam hrho hsum y) ζ hζ hK hC
    (cavity_finite_tilt_isUnit rho lam hrho hsum B hB g x hx)
    (cavity_finite_tilt_isUnit rho lam hrho hsum B hB g y hy) hΔ
    (cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g x hx)
    (cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g y hy)

theorem cavity_finite_projected_residual {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    L.transpose * cavityResolvent (A - A₀) H * L =
      (finiteR rho lam hrho hsum x - finiteR rho lam hrho hsum 0) • 1 := by
  intro D E A A₀ L H
  have hp := cavity_finite_projected_resolvent rho lam hrho hsum B hB hBE hcomplete g x hx
  change E.transpose * D * E + L.transpose * cavityResolvent (A - A₀) H * L = _ at hp
  rw [cavity_limiting_cavityBlock_eq_finiteR_zero rho lam hrho hsum] at hp
  rw [sub_smul]
  exact eq_sub_of_add_eq' hp

theorem cavity_finite_projected_scaled_root {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x q₀ : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho
    let K := A - A₀
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let H' := (1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) • (H * H)
    L.transpose * ((1 - H * K)⁻¹ * (q₀ • H') * ((1 - H * K)⁻¹).transpose) * L =
      (q₀ * deriv (finiteR rho lam hrho hsum) x) • 1 := by
  intro A A₀ L K H H'
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [cavity_finite_projected_root_covariance rho lam hrho hsum B hB hBE hcomplete g x hx,
    smul_smul]

end InvariantIsing

end

end OAI
