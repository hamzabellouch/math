import OAI.Analysis.LipschitzHilbert.Estimates.PlanarCoefficientBudget
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarCoefficientNorm
import OAI.Analysis.LipschitzHilbert.Packets.LinePacketFamily

namespace OAI

/-! The actual analyzing coefficients, normalized once, define the line
packet family used in concentration. Their local budget is proved. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert
namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def coefficientScale (P : PlanarPacketFamily N κ ι) : ℝ := P.constant * Real.pi^2

theorem coefficientScale_pos (P : PlanarPacketFamily N κ ι) : 0 < P.coefficientScale :=
  mul_pos P.constant_pos (pow_pos Real.pi_pos _)

def analyzedLine (P : PlanarPacketFamily N κ ι) (d : Fin N → ℝ)
    (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (y : ℝ)
    (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant / P.length j) *
      (lineEnvelope (P.centerX j i) (P.length j) 3 x *
       lineEnvelope (P.centerZ j i) P.width 2 y)) : LinePacketFamily N κ ι where
  baseX := P.baseX
  baseZ := P.baseZ
  topLength := P.topLength
  width := P.width
  lineY := y
  constant := P.constant
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  constant_pos := P.constant_pos
  coeff := fun j i => P.coefficientScale⁻¹ • P.mainCoefficient d v g j i
  wave := fun j i k => P.wave j i k y
  site := P.site
  site_injective := P.site_injective
  coeff_norm := by
    intro j i
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr P.coefficientScale_pos)]
    apply (mul_le_mul_of_nonneg_left (P.mainCoefficient_norm d v hv g hg hg1 j i)
      (inv_nonneg.mpr P.coefficientScale_pos.le)).trans_eq
    exact inv_mul_cancel₀ P.coefficientScale_pos.ne'
  wave_bound := by
    intro j i k x
    apply (P.wave_bound j i k y x).trans
    apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
    apply mul_le_mul_of_nonneg_left (lineEnvelope_antitone _ _ _ (by decide : 2 ≤ 3))
      (lineEnvelope_nonneg _ _ _ _)
  deriv_bound := hderiv

theorem analyzedLine_localBudget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
      (y : ℝ)
      (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant / P.length j) *
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
         lineEnvelope (P.centerZ j i) P.width 2 y)),
      Monotone d →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      (P.analyzedLine d v hv g hg hg1 y hderiv).HasLocalBudget
        (A * P.constant^2 * P.coefficientScale⁻¹^2) := by
  obtain ⟨A,hA,hbudget⟩ := mainCoefficient_localBudget hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro P d v hv g hg hg1 y hderiv hd hlow hhigh u r hr b
  have h := hbudget N κ ι P d v g hd hv hg hg1 hlow hhigh u y r hr b
  change (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j,
    ‖P.coefficientScale⁻¹ • P.mainCoefficient d v g j i‖^2) ≤ _
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr P.coefficientScale_pos), mul_pow]
  calc
    _ = P.coefficientScale⁻¹^2 *
        (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j, ‖P.mainCoefficient d v g j i‖^2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ P.coefficientScale⁻¹^2 * (A * P.constant^2 * r) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
