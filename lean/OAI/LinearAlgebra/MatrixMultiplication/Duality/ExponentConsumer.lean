import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Exponent
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificatesDual
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexWitness
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.ASI
import OAI.LinearAlgebra.MatrixMultiplication.Rectangular.RateLimit

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualExponentBound

open Filter
open scoped Topology

def fixedAspect : ℝ := 4651 / 10000

theorem target_lt_fixedAspect : (93 : ℝ) / 200 < fixedAspect := by
  norm_num [fixedAspect]

theorem fixedAspect_lt_certificate : fixedAspect < (1548637 : ℝ) / 3327360 := by
  norm_num [fixedAspect]

theorem fixedAspect_lt_dual_aspect : fixedAspect < DualWitness.aspect :=
  fixedAspect_lt_certificate.trans ComplexCertificates.dual_aspect_lower

theorem fixedAspect_mem_unit : fixedAspect ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [fixedAspect]

structure ActualFamily (k budget : ℝ) where
  witness : ℕ → ComplexWitness.FiniteRectangularWitness
  scale : ℕ → ℝ
  outerRate : ℝ
  innerRate : ℝ
  multiplicityRate : ℝ
  rankRate : ℝ
  scale_positive : ∀ᶠ n in atTop, 0 < scale n
  outer_positive : 0 < outerRate
  outer_limit : Tendsto
    (fun n => Real.log ((witness n).outer : ℝ) / scale n) atTop (𝓝 outerRate)
  inner_limit : Tendsto
    (fun n => Real.log ((witness n).inner : ℝ) / scale n) atTop (𝓝 innerRate)
  multiplicity_limit : Tendsto
    (fun n => Real.log ((witness n).multiplicity : ℝ) / scale n) atTop (𝓝 multiplicityRate)
  rank_limit : Tendsto
    (fun n => Real.log ((witness n).rank : ℝ) / scale n) atTop (𝓝 rankRate)
  aspect_gap : k * outerRate < innerRate
  cost_bound : rankRate - multiplicityRate ≤ budget * outerRate

namespace ActualFamily

theorem omega_le {k budget : ℝ} (P : ActualFamily k budget) (hk : 0 ≤ k) :
    Arithmetic.rectangularOmega ℂ k ≤ budget := by
  have hbound := RectangularRateLimit.exponent_le_of_finite_asi
    (fun n => (P.witness n).outer_pos) (fun n => (P.witness n).inner_pos)
    P.scale_positive P.outer_limit P.inner_limit P.multiplicity_limit P.rank_limit
    P.outer_positive P.aspect_gap
    (fun n ha hab => Arithmetic.equalRectangular_log_inequality_of_polynomialApproximation
      ha (P.witness n).multiplicity_pos hk hab (P.witness n).approximation)
  exact hbound.trans ((div_le_iff₀ P.outer_positive).2 P.cost_bound)

end ActualFamily

theorem omega_eq_two_of_arbitrarily_close_families {k : ℝ} (hk : 0 ≤ k)
    (families : ∀ ε : ℝ, 0 < ε → Nonempty (ActualFamily k (2 + ε))) :
    Arithmetic.rectangularOmega ℂ k = 2 := by
  apply le_antisymm _ (Arithmetic.rectangularOmega_two_le k)
  by_contra h
  have hω : 2 < Arithmetic.rectangularOmega ℂ k := lt_of_not_ge h
  have hε : 0 < (Arithmetic.rectangularOmega ℂ k - 2) / 2 := by linarith
  obtain ⟨P⟩ := families ((Arithmetic.rectangularOmega ℂ k - 2) / 2) hε
  have hbound := P.omega_le hk
  linarith

theorem alpha_gt_target_of_arbitrarily_close_families
    (families : ∀ ε : ℝ, 0 < ε → Nonempty (ActualFamily fixedAspect (2 + ε))) :
    (93 : ℝ) / 200 < Arithmetic.complexAlpha := by
  have hω := omega_eq_two_of_arbitrarily_close_families fixedAspect_mem_unit.1 families
  exact target_lt_fixedAspect.trans_le (Arithmetic.le_complexAlpha fixedAspect_mem_unit hω)

end MatrixMultiplication.DualExponentBound

end

end OAI
