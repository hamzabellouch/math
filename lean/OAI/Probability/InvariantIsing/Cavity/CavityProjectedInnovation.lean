import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCovariance
import OAI.Probability.InvariantIsing.Cavity.CavityScalarFieldLaw

namespace OAI

/-! The Schur field identity identifies the covariance of each projected
quadratic innovation with a scalar increment. This is the finite matrix
step in the identification of the cavity field path. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace InvariantIsing

theorem cavity_projected_resolvent_difference {d n : ℕ}
    (K P C : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC : ℝ)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1) :
    L.transpose * (cavityResolvent K P - cavityResolvent K C) * L =
      (rP - rC) • 1 := by
  calc
    _ = L.transpose * cavityResolvent K P * L -
        L.transpose * cavityResolvent K C * L := by rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (C₀ + L.transpose * cavityResolvent K P * L) -
        (C₀ + L.transpose * cavityResolvent K C * L) := by abel
    _ = (rP - rC) • 1 := by rw [hP, hC, sub_smul]

/-- The independent innovation covariance from `cav:q-innovations`,
after projection to the cavity sites, is a scalar resolvent difference. -/
theorem cavity_projected_innovation_covariance {d n : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC ζ : ℝ) (hζ : ζ ≠ 0)
    (hK : K.transpose = K) (hCsym : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1) :
    L.transpose * ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose) * L =
      ((rP - rC) / ζ) • 1 := by
  have hcov : (1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose =
      ζ⁻¹ • (cavityResolvent K P - cavityResolvent K C) := by
    rw [← cavity_innovation_covariance_mul K P C S ζ hK hCsym hPdet hCdet hΔ,
      smul_smul, inv_mul_cancel₀ hζ, one_smul]
  rw [hcov, Matrix.mul_smul, Matrix.smul_mul,
    cavity_projected_resolvent_difference K P C L C₀ rP rC hP hC, smul_smul]
  congr 1
  ring

/-- The exact projected Gaussian law at one independent innovation.
Its scalar variance is specified by the two Schur field values. -/
theorem cavity_projected_innovation_law {d n : ℕ}
    (K P C S : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (rP rC ζ : ℝ) (hζ : ζ ≠ 0)
    (hK : K.transpose = K) (hCsym : C.transpose = C)
    (hPdet : IsUnit (1 - P * K).det) (hCdet : IsUnit (1 - C * K).det)
    (hΔ : P - C = ζ • S)
    (hP : C₀ + L.transpose * cavityResolvent K P * L = rP • 1)
    (hC : C₀ + L.transpose * cavityResolvent K C * L = rC • 1)
    (hcov : ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose).PosSemidef)
    (v : ℝ≥0) (hv : (v : ℝ) = (rP - rC) / ζ) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin d) =>
      WithLp.ofLp (L.transpose.toEuclideanLin z))
      (multivariateGaussian 0 ((1 - P * K)⁻¹ * S * ((1 - C * K)⁻¹).transpose))
      (vectorGaussianLaw n v : Measure (Fin n → ℝ)) := by
  apply cavity_scalar_projected_field_law _ hcov L v
  rw [cavity_projected_innovation_covariance K P C S L C₀ rP rC ζ hζ hK hCsym
    hPdet hCdet hΔ hP hC, hv]

end InvariantIsing

end

end OAI
