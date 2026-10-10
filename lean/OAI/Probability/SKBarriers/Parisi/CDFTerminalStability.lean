import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedPrimitive

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_terminal_stability (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) (hmono : Monotone m)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    {a b : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    {C δ : ℝ} (hC : 0 ≤ C) (haC : ∀ z, |a z| ≤ C) (hbC : ∀ z, |b z| ≤ C)
    (hab : ∀ z, |a z-b z| ≤ δ) (x : ℝ) :
    |scalarHierarchyAverage n m v f a x-scalarHierarchyAverage n m v g b x| ≤
      δ+2*C*(Real.exp (2*ε)-1) := by
  rw [scalarHierarchyAverage_eq_integral n m v hf ha hC haC,
    scalarHierarchyAverage_eq_integral n m v hg hb hC hbC]
  exact hierarchyPathLaw_observable_stability n m hm hmono
    ((hf.translate x).compCLM (coordinateLinear n v))
    ((hg.translate x).compCLM (coordinateLinear n v)) hε
    (fun z => hfg (x+coordinateLinear n v z))
    (ha.comp (continuous_const.add (coordinateLinear n v).continuous))
    (hb.comp (continuous_const.add (coordinateLinear n v).continuous))
    hC (fun z => haC (x+coordinateLinear n v z)) (fun z => hbC (x+coordinateLinear n v z))
    (fun z => hab (x+coordinateLinear n v z)) 0

theorem scalarCDFAverage_terminal_stability (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b da db : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (ha : ∀ z, HasDerivAt a (da z) z) (hb : ∀ z, HasDerivAt b (db z) z)
    (hda : Continuous da) (hdb : Continuous db)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    (hdaC : ∀ z, |da z| ≤ C) (hdbC : ∀ z, |db z| ≤ C)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  have h₁ := dyadicScalarAverage_tendsto_C1 β hα hmono hf ha hda hfK haB hdaC s t ht x
  have h₂ := dyadicScalarAverage_tendsto_C1 β hα hmono hg hb hdb hgL hbB hdbC s t ht x
  apply le_of_tendsto (h₁.sub h₂).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_)
    hf hg hε hfg
    (continuous_iff_continuousAt.mpr (fun z => (ha z).continuousAt))
    (continuous_iff_continuousAt.mpr (fun z => (hb z).continuousAt))
    B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact (List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t)) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
