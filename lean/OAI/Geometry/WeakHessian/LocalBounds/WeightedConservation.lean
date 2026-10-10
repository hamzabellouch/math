import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.WeightedEnergySpace
import OAI.Geometry.WeakHessian.LocalBounds.IdentifiedConservation

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile217
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [SigmaFinite m] in
lemma RCD.weighted_heat_mass_supported {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    {R : ℝ} (hR : ∀ᵐ x ∂exponentialMeasure m V,R ≤ dist x o → u x = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) (exponentialMeasure m V) ∧
      (∫ x,cheegerHeat h t u x ∂exponentialMeasure m V) = ∫ x,u x ∂exponentialMeasure m V := by
  let ν := exponentialMeasure m V
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hBV
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal) hν
  have hnpar := (hrcd.1.global_localGradientParallelogram hfin o hrcd.2).change_measure
    (C := (Real.exp BV).toNNReal) (D := (Real.exp BV).toNNReal) hm hν
  have hID := fun f hf => hrcd.weighted_cheegerEnergy_integral hfin o hBV (f := f) hf
  obtain ⟨a,ha,hd⟩ := hrcd.1.exists_decay_weight hN hfull hfin o
  have hW : LipschitzWith ‖a‖₊ (fun x => a*dist x o) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |a*dist x o-a*dist y o| ≤ |a| * dist x y
    rw [← mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_dist_sub_le x y o) (abs_nonneg a)
  have huW := memLp_exp_dist_of_support u ha.le o hR
  have hd' : MemLp (fun x => Real.exp (-(a*dist x o))) 2 ν := by
    simpa only [neg_mul] using hd.of_measure_le_smul (by simp : (↑(Real.exp BV).toNNReal : ℝ≥0∞) ≠ ∞) hν
  refine ⟨integrable_of_memLp_mul_exp
    (identified_cheegerHeat_weighted hID hnpar hnfin o h u hW huW ht).1 hd', ?_⟩
  exact identified_cheegerHeat_mass_localized hID hnpar hnfin o h u hW huW hd' ht

omit [SigmaFinite m] in
lemma RCD.weighted_heat_mass_nonneg {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hu : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hi : Integrable u (exponentialMeasure m V)) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (cheegerHeat h t u) (exponentialMeasure m V) ∧
      (∫ x,cheegerHeat h t u x ∂exponentialMeasure m V) = ∫ x,u x ∂exponentialMeasure m V := by
  let ν := exponentialMeasure m V
  have hnfin := hfin.of_le_smul (C := (Real.exp BV).toNNReal)
    (exponentialMeasure_comparable (m := m) hBV).2
  have hsub := cheegerHeat_submass hnfin o h u hu hi ht
  refine ⟨hsub.1,le_antisymm hsub.2 ?_⟩
  have hχ (n : ℕ) : ∀ᵐ x ∂ν, |radialCutoff o n x| ≤ (1:ℝ) := ae_of_all _ fun x => by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let us (n : ℕ) : Lp ℝ 2 ν := boundedMulLp (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (hχ n) u
  have he (n : ℕ) : us n =ᵐ[ν] fun x => u x*radialCutoff o n x := boundedMulLp_ae _ _ u
  have hs (n : ℕ) : ∀ᵐ x ∂ν, (n:ℝ)+1 ≤ dist x o → us n x = 0 := by
    filter_upwards [he n] with x hx hdist
    rw [hx]
    have hz : radialCutoff o n x = 0 := by
      apply max_eq_left
      have H : 1 ≤ dist x o/((n:ℝ)+1) := (le_div_iff₀ (by positivity)).mpr (by simpa using hdist)
      linarith
    rw [hz,mul_zero]
  have hle (n : ℕ) : ∀ᵐ x ∂ν, us n x ≤ u x := by
    filter_upwards [he n,hu] with x hx hpos
    rw [hx]
    exact mul_le_of_le_one_right hpos (radialCutoff_le_one o n x)
  have hmass (n : ℕ) := hrcd.weighted_heat_mass_supported hN hfull hfin o hBV h (us n) (hs n) ht
  have hbound (n : ℕ) : (∫ x,u x*radialCutoff o n x ∂ν) ≤ ∫ x,cheegerHeat h t u x ∂ν := by
    rw [← integral_congr_ae (he n),← (hmass n).2]
    exact integral_mono_ae (hmass n).1 hsub.1 (cheegerHeat_order h ht (us n) u (hle n))
  exact le_of_tendsto (integral_radialCutoff_tendsto o hi) (Eventually.of_forall hbound)

omit [SigmaFinite m] in
lemma RCD.weighted_heat_probability {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {V : X → ℝ} {BV : ℝ} (hBV : ∀ x,|V x| ≤ BV)
    (h : QuadraticCheegerEnergy (exponentialMeasure m V))
    (u : Lp ℝ 2 (exponentialMeasure m V))
    (hu : ∀ᵐ x ∂exponentialMeasure m V,0 ≤ u x)
    (hmass : ∫ x,u x ∂exponentialMeasure m V = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (densityMeasure (exponentialMeasure m V) (cheegerHeat h t u)) := by
  have H := hrcd.weighted_heat_mass_nonneg hN hfull hfin o hBV h u hu
    (integrable_of_integral_eq_one hmass) ht
  exact densityMeasure_probability_of_integrable _ (cheegerHeat_nonneg h ht u hu) H.1 (H.2.trans hmass)
end WeakHessian

end
end InlinedFile217

end OAI
