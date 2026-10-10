import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CDSobolevLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile181
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma RCD.cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {f : X → ℝ} (hf : Sobolev m f) :
    cheegerEnergy m f = ENNReal.ofReal ((∫ x,(weakGradient m f x)^2 ∂m)/2) := by
  rw [hrcd.1.global_cheegerEnergy_eq_weakGradient hfin o hf,norm_toLp_sq_eq_integral]

omit [SigmaFinite m] in
lemma RCD.weighted_cheegerEnergy_integral {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B)
    {f : X → ℝ} (hf : Sobolev (exponentialMeasure m V) f) :
    cheegerEnergy (exponentialMeasure m V) f =
      ENNReal.ofReal ((∫ x,(weakGradient (exponentialMeasure m V) f x)^2
        ∂exponentialMeasure m V)/2) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  have hfm := (sobolev_exponentialMeasure_iff hB f).mpr hf
  have H := cheegerEnergy_integral_of_comparable hfin
    (fun f hf => hrcd.cheegerEnergy_integral hfin o hf)
    (C := (Real.exp B).toNNReal) (E := (Real.exp B).toNNReal) hm hν hfm
  rw [H]
  congr 2
  apply integral_congr_ae
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le
    (weakGradient_exponentialMeasure (m := m) hB f)] with x hx
  rw [hx]

omit [SigmaFinite m] in
lemma RCD.weighted_quadraticCheegerEnergy {K N : ℝ} (hrcd : RCD m K N)
    (hfin : FiniteOnBoundedSets m) (o : X) {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B) :
    QuadraticCheegerEnergy (exponentialMeasure m V) := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  exact quadraticCheegerEnergy_of_comparable hfin hrcd.2
    (fun f hf => hrcd.cheegerEnergy_integral hfin o hf)
    (C := (Real.exp B).toNNReal) (E := (Real.exp B).toNNReal) hm hν

lemma RCD.weighted_sobolev_to_lipschitz {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    {V : X → ℝ} {B : ℝ} (hB : ∀ x,|V x| ≤ B)
    {f D : X → ℝ} (hf : LocallyL2 (exponentialMeasure m V) f)
    (hD : IsLocalWeakUpperGradient (exponentialMeasure m V) f D)
    {L : ℝ≥0} (hDL : ∀ᵐ x ∂exponentialMeasure m V,D x ≤ L) :
    ∃ g : X → ℝ,LipschitzWith L g ∧ g =ᵐ[exponentialMeasure m V] f := by
  obtain ⟨hm,hν⟩ := exponentialMeasure_comparable (m := m) hB
  obtain ⟨g,hg,he⟩ := hrcd.1.sobolev_to_lipschitz hN hfull hfin
    (hf.of_measure_le_smul (C := (Real.exp B).toNNReal) hm)
    (hD.of_measure_le_smul (D := (Real.exp B).toNNReal) hm)
    ((Measure.absolutelyContinuous_of_le_smul hm).ae_le hDL)
  exact ⟨g,hg,(Measure.absolutelyContinuous_of_le_smul hν).ae_le he⟩
end WeakHessian

end
end InlinedFile181

end OAI
