import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.DenseTests
import OAI.Geometry.CAT0Fillings.Currents.CanonicalMass

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
lemma integral_continuousMap_lipschitz (μ : FiniteMeasure X) (M : ℝ≥0) (hM : μ.mass ≤ M) :
    LipschitzWith M (fun f : C(X,ℝ) => ∫ x, f x ∂(μ : Measure X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hfi : Integrable (fun x => f x) (μ : Measure X) := (BoundedContinuousFunction.mkOfCompact f).integrable _
  have hgi : Integrable (fun x => g x) (μ : Measure X) := (BoundedContinuousFunction.mkOfCompact g).integrable _
  rw [dist_eq_norm,←integral_sub hfi hgi]
  have hi := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
    (Eventually.of_forall fun x => (f-g).norm_coe_le_norm x)
  have hm : (μ : Measure X).real univ ≤ (M : ℝ) := NNReal.coe_le_coe.mpr hM
  exact hi.trans (by rw [dist_eq_norm]; nlinarith [norm_nonneg (f-g)])

theorem finiteMeasure_bounded_weak_subsequence (μs : ℕ → FiniteMeasure X)
    (M : ℝ≥0) (hM : ∀ j, (μs j).mass ≤ M) :
    ∃ μ : FiniteMeasure X, μ.mass ≤ M ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (μs ∘ ψ) atTop (𝓝 μ) := by
  obtain ⟨μ,hμ,hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X M).exists_mapClusterPt_of_frequently
      (l := atTop) (Eventually.of_forall hM).frequently
  let l := comap μs (𝓝 μ) ⊓ atTop
  have hl : NeBot l := neBot_inf_comap_iff_map'.mpr hcluster
  let := hl
  have hμlim : Tendsto μs l (𝓝 μ) := tendsto_iff_comap.mpr inf_le_left
  obtain ⟨D,hD⟩ := TopologicalSpace.exists_dense_seq C(X,ℝ)
  let F (ν : FiniteMeasure X) : ℕ → ℝ := fun i => ∫ x, D i x ∂(ν : Measure X)
  have hF : Tendsto (fun j => F (μs j)) l (𝓝 (F μ)) :=
    tendsto_pi_nhds.mpr fun i => (FiniteMeasure.continuous_integral_continuousMap (D i)).tendsto μ |>.comp hμlim
  obtain ⟨ψ,hψ,hψlim⟩ := (hF.mapClusterPt.mono (show l ≤ atTop from inf_le_right)).tendsto_subseq
  refine ⟨μ,hμ,ψ,hψ,FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_⟩
  intro f
  exact tendsto_of_lipschitz_dense
    (fun j => integral_continuousMap_lipschitz (μs (ψ j)) M (hM (ψ j)))
    (integral_continuousMap_lipschitz μ M hμ) hD
    (fun i => tendsto_pi_nhds.mp hψlim i) f.toContinuousMap

end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory Filter MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma exists_weak_controlling_subsequence {k : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (M : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    ∃ μs : ℕ → FiniteMeasure X, ∃ μ : FiniteMeasure X,
      (∀ j, Controls (Ts j) (μs j)) ∧ Controls T μ ∧ μ.mass ≤ M ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (μs ∘ ψ) atTop (𝓝 μ) := by
  let μs (j : ℕ) : FiniteMeasure X := ⟨currentMassMeasure (hTs j),inferInstance⟩
  have hc j : Controls (Ts j) (μs j) := currentMassMeasure_controls (hTs j)
  have hm j : (μs j).mass ≤ M := by
    apply NNReal.coe_le_coe.mp
    change (currentMassMeasure (hTs j)).real univ ≤ (M : ℝ)
    rw [currentMassMeasure_total]
    exact hM j
  obtain ⟨μ,hμ,ψ,hψ,hmulim⟩ := finiteMeasure_bounded_weak_subsequence μs M hm
  refine ⟨μs,μ,hc,?_,hμ,ψ,hψ,hmulim⟩
  exact controls_of_weak_limits hmulim (fun j => hc (ψ j))
    (fun b π _ => (hlim b π).comp hψ.tendsto_atTop)

lemma exists_joint_weak_controlling_subsequence {k m : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    {Us : ℕ → Functional X m} {U : Functional X m}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hUs : ∀ j, IsMetricCurrent (Us j))
    (M N : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (Us j) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)))
    (hulim : ∀ b π, Tendsto (fun j => Us j b π) atTop (𝓝 (U b π))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ μs νs : ℕ → FiniteMeasure X, ∃ μ ν : FiniteMeasure X,
      (∀ j, Controls (Ts (ψ j)) (μs j)) ∧ Controls T μ ∧
      (∀ j, Controls (Us (ψ j)) (νs j)) ∧ Controls U ν ∧
      Tendsto μs atTop (𝓝 μ) ∧ Tendsto νs atTop (𝓝 ν) := by
  obtain ⟨μs,μ,hμs,hμ,_,φ,hφ,hφlim⟩ := exists_weak_controlling_subsequence hTs M hM hlim
  obtain ⟨νs,ν,hνs,hν,_,χ,hχ,hχlim⟩ := exists_weak_controlling_subsequence
    (fun j => hUs (φ j)) N (fun j => hN (φ j))
    (fun b π => (hulim b π).comp hφ.tendsto_atTop)
  exact ⟨φ ∘ χ,hφ.comp hχ,μs ∘ φ ∘ χ,νs ∘ χ,μ,ν,
    (fun j => hμs (φ (χ j))),hμ,(fun j => hνs (χ j)),hν,
    hφlim.comp hχ.tendsto_atTop,hχlim⟩

end CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma ae_exists_bounded_subsequence_of_integral_bound {A : Type*} [MeasurableSpace A]
    (μ : Measure A) {G : ℕ → A → ℝ} (hG : ∀ j, Integrable (G j) μ)
    (hG0 : ∀ j, ∀ᵐ x ∂μ, 0 ≤ G j x) (M : ℝ) (hM : ∀ j, (∫ x, G j x ∂μ) ≤ M) :
    ∀ᵐ x ∂μ, ∃ C : ℝ, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, G (ψ j) x ≤ C := by
  let hmeas (j : ℕ) := (hG j).aemeasurable.ennreal_ofReal
  let f (j : ℕ) : A → ℝ≥0∞ := (hmeas j).mk _
  have hf (j : ℕ) : Measurable (f j) := (hmeas j).measurable_mk
  have heq (j : ℕ) : (fun x => ENNReal.ofReal (G j x)) =ᵐ[μ] f j := (hmeas j).ae_eq_mk
  have hI (j : ℕ) : (∫⁻ x, f j x ∂μ) ≤ ENNReal.ofReal M := by
    rw [←lintegral_congr_ae (heq j),←ofReal_integral_eq_lintegral_ofReal (hG j) (hG0 j)]
    exact ENNReal.ofReal_le_ofReal (hM j)
  have hfat : (∫⁻ x, liminf (fun j => f j x) atTop ∂μ) < (⊤ : ℝ≥0∞) := by
    apply lt_of_le_of_lt (lintegral_liminf_le hf)
    exact lt_of_le_of_lt (liminf_le_of_frequently_le (Frequently.of_forall hI)) ENNReal.ofReal_lt_top
  have ha := ae_lt_top (Measurable.liminf hf) hfat.ne
  filter_upwards [ha,ae_all_iff.mpr heq] with x hx he
  obtain ⟨N,hN⟩ := ENNReal.exists_nat_gt hx.ne
  obtain ⟨ψ,hψ,hψbound⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_liminf_lt (u := fun j => f j x) (f := atTop) (h := hN))
  refine ⟨N,ψ,hψ,fun j => ?_⟩
  have hj : ENNReal.ofReal (G (ψ j) x) ≤ ENNReal.ofReal (N:ℝ) := by
    rw [he,ENNReal.ofReal_natCast]
    exact (hψbound j).le
  exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg N)).mp hj

end CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable
open BorelCoefficients MassMeasure


attribute [local instance] Classical.propDecidable
open Set Metric
open scoped NNReal

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

end CAT0Fillings
end

end OAI
