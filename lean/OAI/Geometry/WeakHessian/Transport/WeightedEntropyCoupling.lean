import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedConservation
import OAI.Geometry.WeakHessian.Transport.EntropyCoupling

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma integrable_mul_of_exp_weights {u W : X → ℝ}
    (hu : MemLp (fun x => u x*Real.exp (W x)) 2 m)
    (hW : MemLp (fun x => W x*Real.exp (-W x)) 2 m) :
    Integrable (fun x => u x*W x) m := by
  apply (hu.integrable_mul hW).congr
  exact ae_of_all _ fun x => by
    change (u x*Real.exp (W x))*(W x*Real.exp (-W x)) = u x*W x
    rw [show (u x*Real.exp (W x))*(W x*Real.exp (-W x)) =
      (u x*W x)*(Real.exp (W x)*Real.exp (-W x)) by ring,
      ← Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]

lemma RCD.weighted_heat_entropy_tails {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0) :
    ∃ a : ℝ,0 < a ∧ Integrable (fun x => Real.exp (-(a*dist x o))) (exponentialMeasure m V) ∧
      Integrable (fun x => u x*(a*dist x o)) (exponentialMeasure m V) ∧
      ∀ t : ℝ,0 ≤ t → Integrable (fun x => cheegerHeat h t u x*(a*dist x o)) (exponentialMeasure m V) := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hi,h2,hD,hh,hhi⟩ := hrcd.1.exists_strong_entropy_confinement hN hfull hfin o
  have hCt : (↑(Real.exp BV).toNNReal : ℝ≥0∞) ≠ ∞ := by simp
  have hi' : Integrable (fun x => Real.exp (-(a*dist x o))) ν := by
    apply memLp_one_iff_integrable.mp
    exact (memLp_one_iff_integrable.mpr hi).of_measure_le_smul hCt hν
  have hD' : MemLp (fun x => (a*dist x o)*Real.exp (-(a*dist x o))) 2 ν :=
    hD.of_measure_le_smul hCt hν
  have huW := memLp_exp_dist_of_support u ha.le o hR
  refine ⟨a,ha,hi',integrable_mul_of_exp_weights huW hD',?_⟩
  intro t ht
  exact integrable_mul_of_exp_weights
    (identified_cheegerHeat_weighted hID hnpar hnfin o h u (lipschitz_mul_dist o a) huW ht).1 hD'

lemma RCD.weighted_heat_entropy_coupling {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hun : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hmass : ∫ x,u x ∂exponentialMeasure m V = 1)
    {B : ℝ} (hB : 0 ≤ B) (hub : ∀ᵐ x ∂exponentialMeasure m V,|u x| ≤ B)
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure (exponentialMeasure m V) (cheegerHeat h T u) ∧
      p.map Prod.snd = densityMeasure (exponentialMeasure m V) u ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤
        ENNReal.ofReal (2*T*((∫ x,reducedEntropy (u x) ∂exponentialMeasure m V)-
          (∫ x,reducedEntropy (cheegerHeat h T u x) ∂exponentialMeasure m V))) := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hi,huW,hPW⟩ := hrcd.weighted_heat_entropy_tails hN hfull hfin o hBV h u hR
  have hPm := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hun
    (integrable_of_integral_eq_one hmass) hT
  exact cheegerHeat_entropy_coupling hnfin o hID hnpar h u hun hub hB hT hmass
    (hPm.2.trans hmass) huW (hPW T hT) hi

end WeakHessian

end
end

end OAI
