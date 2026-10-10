import OAI.Analysis.LipschitzHilbert.Packets.AnalyzedLineFamily
import OAI.Analysis.LipschitzHilbert.Estimates.TopWindowMoments

namespace OAI

/-! Uniform local budgets for the actual analyzing coefficients. The
constant is fixed before the finite Hilbert and scale index types. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert.PlanarPacketFamily

theorem uniform_analyzedLine_localBudget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
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
  intro N κ ι _ _ P d v hv g hg hg1 y hderiv hd hlow hhigh u r hr b
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


theorem uniform_analyzed_top_moment (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A M : ℝ, 0 < A ∧ 0 < M ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
      (y : ℝ)
      (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant / P.length j) *
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
         lineEnvelope (P.centerZ j i) P.width 2 y)),
      Monotone d →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      let Q := P.analyzedLine d v hv g hg hg1 y hderiv
      ∀ (q : ℕ) (T : TopPacketWindow Q q) (grid : FiniteLineGrid),
      1 < grid.branching → P.topLength ≤ grid.width → ∀ p : ℝ, 0 ≤ p →
      (∫⁻ x, (ENNReal.ofReal |(polynomialWeight T.baseX T.radiusX q x *
        polynomialWeight T.baseZ T.radiusZ q y) * Q.variation x|)^p ∂grid.lineMeasure) ≤
      (2:ℝ≥0∞)^p * (7 * ENNReal.ofReal
        ((p * (((grid.branching:ℝ)+2) *
          (2*Real.sqrt (M*T.constant^2*(A*P.constant^2*P.coefficientScale⁻¹^2)+1) +
            4*(T.constant*(4*Real.pi)^2))) / Real.log (3/2))^p) +
        (ENNReal.ofReal (Real.sqrt (M*T.constant^2*(A*P.constant^2*P.coefficientScale⁻¹^2)+1)))^p) *
          grid.lineMeasure Set.univ := by
  obtain ⟨A,hA,hbudget⟩ := uniform_analyzedLine_localBudget hL hlo hhi
  obtain ⟨M,hM,hmoment⟩ := TopPacketWindow.line_moment hL hlo hhi
  refine ⟨A,M,hA,hM,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 y hderiv hd hlow hhigh
  dsimp only
  intro q T grid hb hwidth p hp
  let Q := P.analyzedLine d v hv g hg hg1 y hderiv
  exact hmoment N κ ι Q (A*P.constant^2*P.coefficientScale⁻¹^2) (by positivity)
    (hbudget N κ ι P d v hv g hg hg1 y hderiv hd hlow hhigh)
    (fun j i k ξ hξ => hlow j i k y ξ hξ)
    (fun j i k ξ hξ => hhigh j i k y ξ hξ) q T grid hb hwidth p hp

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
