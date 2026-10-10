import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Scalar
import OAI.Geometry.CAT0Fillings.Prism.Chart
import OAI.Geometry.CAT0Fillings.Prism.Mass
import OAI.Geometry.CAT0Fillings.Currents.ControlledSum

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
noncomputable def prismFamily (C : ℕ → IntegerChart X k) : Functional (ℝ × X) (k+1) :=
  fun b π => ∑' i, (C i).prism.action b π

lemma prismFamily_current (C : ℕ → IntegerChart X k)
    (hs : Summable (fun i => mass (C i).action)) : IsMetricCurrent (prismFamily C) := by
  choose μ hfin hμ heq using fun i => (C i).action_isMetricCurrent.exists_controls_mass_eq
  let : ∀ i, IsFiniteMeasure (μ i) := hfin
  let ν : ℕ → Measure (ℝ × X) := fun i =>
    (k+1:ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod (μ i)
  have hν (i) : Controls (C i).prism.action (ν i) := (C i).prism_controls (hμ i)
  have hvreal (i) : (ν i).real univ = (k+1:ℝ)*mass (C i).action := by
    rw [heq i]
    dsimp [ν]
    rw [measureReal_nnreal_smul_apply]
    simp [measureReal_def,←Set.univ_prod_univ,Measure.prod_prod]
  apply isMetricCurrent_tsum_controlled (μ := ν) (fun i => (C i).prism.action_isMetricCurrent) hν
  simpa only [hvreal] using hs.mul_left (k+1:ℝ)

lemma prismFamily_rectifiable (C : ℕ → IntegerChart X k)
    (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hs : Summable (fun i => mass (C i).action)) : IntegerRectifiable (prismFamily C) := by
  refine ⟨fun i => (C i).prism,fun i j hij => (C i).prism_image_disjoint (hd hij),
    fun i => (C i).prism.action_isMetricCurrent,?_,fun _ _ => rfl⟩
  exact (hs.mul_left (k+1:ℝ)).of_nonneg_of_le
    (fun i => mass_nonneg (C i).prism.action) (fun i => (C i).mass_prism_le)

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma prismFamily_compactlySupported (C : ℕ → IntegerChart X k) :
    CompactlySupported (prismFamily C) := by
  refine ⟨Icc (0:ℝ) 1 ×ˢ (univ : Set X),isCompact_Icc.prod isCompact_univ,?_⟩
  intro b π hab hb
  change (∑' i, (C i).prism.action b π) = 0
  suffices hzero : ∀ i, (C i).prism.action b π = 0 by simp only [hzero,tsum_zero]
  intro i
  rw [IntegerChart.action,ite_eq_left hab]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro z hz
  have him : (C i).prism.param ⟨z,hz⟩ ∈ Icc (0:ℝ) 1 ×ˢ (univ : Set X) := by
    exact ⟨hz.1,mem_univ _⟩
  rw [(C i).prism.scalar_eq hz,hb _ him,mul_zero,zero_mul]

theorem exists_rectifiable_prism {T : Functional X k} (hT : IntegerRectifiable T) :
    ∃ C : ℕ → IntegerChart X k,
      (∀ b π, T b π = ∑' i, (C i).action b π) ∧
      IsMetricCurrent (prismFamily C) ∧ IntegerRectifiable (prismFamily C) ∧
      CompactlySupported (prismFamily C) := by
  obtain ⟨C,hd,_,hs,heq⟩ := hT
  exact ⟨C,heq,prismFamily_current C hs,prismFamily_rectifiable C hd hs,
    prismFamily_compactlySupported C⟩
end CAT0Fillings
end
end

end OAI
