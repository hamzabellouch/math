import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatRegularity
import OAI.Geometry.WeakHessian.LocalBounds.GammaVariableContinuity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile198
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.weighted_heat_curvature_continuousOn {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V) {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    {f Af : Lp ℝ 2 (exponentialMeasure m V)} (ξ : Lp ℝ 2 (exponentialMeasure m V))
    (hf : (cheeger_closedQuadraticEnergy h).IsFormGenerator f Af)
    {Cf CAf : ℝ} (hCf : 0 ≤ Cf) (hCAf : 0 ≤ CAf)
    (hfb : ∀ᵐ x ∂exponentialMeasure m V,|f x| ≤ Cf)
    (hAfb : ∀ᵐ x ∂exponentialMeasure m V,|Af x| ≤ CAf)
    {k : X → ℝ} (hkm : AEStronglyMeasurable k (exponentialMeasure m V))
    {B : ℝ} (hkb : ∀ᵐ x ∂exponentialMeasure m V,|k x| ≤ B) (T : ℝ) :
    ContinuousOn (fun s => ∫ x,(cheegerHeat h s ξ x*k x)*
      gamma (exponentialMeasure m V) (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) f) x
        ∂exponentialMeasure m V) (Icc 0 T) := by
  let ν := exponentialMeasure m V
  let Q := cheeger_closedQuadraticEnergy h
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hgen (s : ℝ) : IsLaplacian ν (cheegerHeat h (T-s) f) (cheegerHeat h (T-s) Af) :=
    (hrcd.weighted_formGenerator_iff hfin o hBV h _ _).mpr (Q.formGenerator_heat ν hf (T-s))
  have hb (v : Lp ℝ 2 ν) : ContinuousOn (fun s => cheegerHeat h (T-s) v) (Icc 0 T) :=
    (cheegerHeat_continuousOn hnfin h v).comp (continuous_const.sub continuous_id).continuousOn
      (fun _ hs => sub_nonneg.mpr hs.2)
  obtain ⟨M,hM⟩ := hrcd.weighted_heat_uniform_lipschitz hN hfull hfin o hV hBV h hf hCf hCAf hfb hAfb
  obtain ⟨n,hn⟩ := exists_nat_ge (M:ℝ)
  apply continuousOn_graph_gamma_pairing hnfin hnpar hgen (hb f) (hb Af)
    ((cheegerHeat_continuousOn hnfin h ξ).mono Icc_subset_Ici_self) n _ hkm hkb
  intro s hs
  obtain ⟨g,hg,hge⟩ := hM (T-s) (sub_nonneg.mpr hs.2)
  filter_upwards [weakGradient_congr_ae hge,weakGradient_le_lipschitz hnfin hg,
    weakGradient_nonneg (m := ν) (cheegerHeat h (T-s) f : X → ℝ)] with x he hb h0
  rw [abs_of_nonneg h0,← he]
  exact hb.trans hn
end WeakHessian

end
end InlinedFile198

end OAI
