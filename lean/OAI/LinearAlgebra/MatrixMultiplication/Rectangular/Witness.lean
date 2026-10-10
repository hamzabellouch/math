import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexWitness
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificates
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.ASI
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.RateLimit

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

namespace MatrixMultiplication.RectangularWitness

open Filter
open scoped Topology

theorem aspect_lower {g h : ℝ}
    (hg : (27961 : ℝ) / 25000 < g)
    (hh₀ : 0 < h) (hh : h < (15761 : ℝ) / 5000) :
    (55922 : ℝ) / 78805 < 2 * g / h := by
  apply (lt_div_iff₀ hh₀).2
  nlinarith

theorem target_aspect_lt {g h : ℝ}
    (hg : (27961 : ℝ) / 25000 < g)
    (hh₀ : 0 < h) (hh : h < (15761 : ℝ) / 5000) :
    (709 : ℝ) / 1000 < 2 * g / h := by
  exact (by norm_num : (709 : ℝ) / 1000 < 55922 / 78805).trans
    (aspect_lower hg hh₀ hh)

theorem aspect_lt_one {g h : ℝ}
    (hg : g < (6991 : ℝ) / 6250)
    (hh : (31519 : ℝ) / 10000 < h) : 2 * g / h < 1 := by
  have hh₀ : 0 < h := by linarith
  apply (div_lt_iff₀ hh₀).2
  linarith

theorem exponent_upper {c h : ℝ}
    (hc : c < (10987 : ℝ) / 10000)
    (hh : (31519 : ℝ) / 10000 < h) :
    6 * c / h < (65922 : ℝ) / 31519 := by
  have hh₀ : 0 < h := by linarith
  apply (div_lt_iff₀ hh₀).2
  nlinarith

theorem exponent_lt_target {c h : ℝ}
    (hc : c < (10987 : ℝ) / 10000)
    (hh : (31519 : ℝ) / 10000 < h) :
    6 * c / h < (523 : ℝ) / 250 := by
  exact (exponent_upper hc hh).trans
    (by norm_num : (65922 : ℝ) / 31519 < 523 / 250)

theorem omega_lt_of_balanced_family
    (W : ℕ → ComplexWitness.FiniteRectangularWitness)
    (scale : ℕ → ℝ) (k target g h H : ℝ)
    (k_nonneg : 0 ≤ k) (h_positive : 0 < h)
    (aspect_gap : k * h < 2 * g) (cost_gap : 6 * Real.log 3 < target * h)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (outer_rate : Tendsto
      (fun n => Real.log ((W n).outer : ℝ) / scale n) atTop (𝓝 h))
    (inner_rate : Tendsto
      (fun n => Real.log ((W n).inner : ℝ) / scale n) atTop (𝓝 (2 * g)))
    (multiplicity_rate : Tendsto
      (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 (2 * H)))
    (rank_rate : Tendsto
      (fun n => Real.log ((W n).rank : ℝ) / scale n) atTop
      (𝓝 (6 * Real.log 3 + 2 * H))) :
    Arithmetic.rectangularOmega ℂ k < target := by
  have hbound := RectangularRateLimit.exponent_le_of_finite_asi
    (fun n => (W n).outer_pos) (fun n => (W n).inner_pos)
    scale_positive outer_rate inner_rate multiplicity_rate rank_rate h_positive aspect_gap
    (fun n ha hab => Arithmetic.equalRectangular_log_inequality_of_polynomialApproximation
      ha (W n).multiplicity_pos k_nonneg hab (W n).approximation)
  have hcancel : (6 * Real.log 3 + 2 * H - 2 * H) / h = 6 * Real.log 3 / h := by ring
  rw [hcancel] at hbound
  exact hbound.trans_lt ((div_lt_iff₀ h_positive).2 cost_gap)

theorem omega_lt_target_of_nearby_balanced_family
    (W : ℕ → ComplexWitness.FiniteRectangularWitness)
    (scale : ℕ → ℝ) (g h H : ℝ)
    (g_lower : (27961 : ℝ) / 25000 < g)
    (h_lower : (31519 : ℝ) / 10000 < h)
    (h_upper : h < (15761 : ℝ) / 5000)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (outer_rate : Tendsto
      (fun n => Real.log ((W n).outer : ℝ) / scale n) atTop
      (𝓝 h))
    (inner_rate : Tendsto
      (fun n => Real.log ((W n).inner : ℝ) / scale n) atTop
      (𝓝 (2 * g)))
    (multiplicity_rate : Tendsto
      (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 (2 * H)))
    (rank_rate : Tendsto
      (fun n => Real.log ((W n).rank : ℝ) / scale n) atTop
      (𝓝 (6 * Real.log 3 + 2 * H))) :
    Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250 := by
  have hh₀ : 0 < h := by linarith
  have hgap : (709 : ℝ) / 1000 * h < 2 * g :=
    (lt_div_iff₀ hh₀).1 (target_aspect_lt g_lower hh₀ h_upper)
  apply omega_lt_of_balanced_family W scale (709 / 1000) (523 / 250) g h H
    (by norm_num) hh₀ hgap _ scale_positive outer_rate inner_rate multiplicity_rate rank_rate
  exact (div_lt_iff₀ hh₀).1
    (exponent_lt_target ComplexCertificates.log_three_upper h_lower)

theorem omega_lt_target_of_balanced_family
    (W : ℕ → ComplexWitness.FiniteRectangularWitness)
    (scale : ℕ → ℝ) (H : ℝ)
    (scale_positive : ∀ᶠ n in atTop, 0 < scale n)
    (outer_rate : Tendsto
      (fun n => Real.log ((W n).outer : ℝ) / scale n) atTop
      (𝓝 ComplexCertificates.curveH))
    (inner_rate : Tendsto
      (fun n => Real.log ((W n).inner : ℝ) / scale n) atTop
      (𝓝 (2 * ComplexCertificates.curveG)))
    (multiplicity_rate : Tendsto
      (fun n => Real.log ((W n).multiplicity : ℝ) / scale n) atTop (𝓝 (2 * H)))
    (rank_rate : Tendsto
      (fun n => Real.log ((W n).rank : ℝ) / scale n) atTop
      (𝓝 (6 * Real.log 3 + 2 * H))) :
    Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250 :=
  omega_lt_target_of_nearby_balanced_family W scale
    ComplexCertificates.curveG ComplexCertificates.curveH H
    ComplexCertificates.curveG_bounds.1 ComplexCertificates.curveH_bounds.1
    ComplexCertificates.curveH_bounds.2 scale_positive outer_rate inner_rate
    multiplicity_rate rank_rate

end MatrixMultiplication.RectangularWitness

end OAI
