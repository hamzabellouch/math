import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFTerminalStability
import OAI.Probability.SKBarriers.Gaussian.LipschitzObservable

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_terminal_stability_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B A C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (haA : LipschitzWith A a) (hbC : LipschitzWith C b)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    {ε δ : ℝ} (hε : 0≤ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haA haB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hg hgL hbC hbB s t ht x)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_) hf hg hε hfg haA.continuous hbC.continuous B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
