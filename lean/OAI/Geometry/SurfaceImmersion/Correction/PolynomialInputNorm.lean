import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors

namespace OAI

/-! Bounds on the actual tensor input norm of the phase solver. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean WeightedEstimates
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

theorem norm_le_of_weightedBound (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (I : ℕ → ℝ) (hI : ∀ m, 1 ≤ I m)
    (hcoords : ∀ m j, 1 ≤ j → j ≤ m → ∀ x ∈ c.e.target,
      ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ I m)
    (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (f : SupportedField (F := ComplexTensor) (modeSupport K))
    (hb : WeightedBound Set.univ s m C f) :
    c.norm f m ≤ tensorChartBudget m (I m) (I (m + 1)) * C := by
  have hn := supportedSeminorm_le_of_weightedBound hs hC f hb
  have hfield := RealModes.weighted_coordDeriv_of_jets c.e.open_target c.smoothInverse s.coe_nonneg hs1
    (zero_le_one.trans (hI (m + 1))) (hcoords (m + 1))
  have hh := tensorChartPush_bound c.e (modeSupport K) c.supportChart c.smoothInverse hs hs1
    (hI m) (zero_le_one.trans (hI (m + 1))) (hcoords m) hfield f
  exact hh.trans (mul_le_mul_of_nonneg_left hn
    (tensorChartBudget_nonneg m (zero_le_one.trans (hI m)) (zero_le_one.trans (hI (m + 1)))))

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
