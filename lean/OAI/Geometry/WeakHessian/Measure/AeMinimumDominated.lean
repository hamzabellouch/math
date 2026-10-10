import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.RunningMin

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace WeakHessianCalculus

lemma exists_ae_minimum_dominated {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (S : Set (X → ℝ)) (B : X → ℝ) (hB : Integrable B ν) (hS : S.Nonempty)
    (hmeas : ∀ f ∈ S, AEMeasurable f ν)
    (hbound : ∀ f ∈ S, ∀ x, 0 ≤ f x ∧ f x ≤ B x)
    (hmin : ∀ f ∈ S, ∀ g ∈ S, (fun x => min (f x) (g x)) ∈ S)
    (hclosed : ∀ (u : ℕ → X → ℝ), (∀ n, u n ∈ S) → ∀ d : X → ℝ,
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (d x))) → d ∈ S) :
    ∃ d ∈ S, ∀ f ∈ S, ∀ᵐ x ∂ν, d x ≤ f x := by
  have hi : ∀ f ∈ S, Integrable f ν := by
    intro f hf
    apply hB.mono' (hmeas f hf).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound f hf x).1] using (hbound f hf x).2
  let E : Set ℝ := (fun f : X → ℝ => ∫ x, f x ∂ν) '' S
  have hE : E.Nonempty := hS.image _
  have hEb : BddBelow E := ⟨0, by
    rintro e ⟨f, hf, rfl⟩
    exact integral_nonneg (fun x => (hbound f hf x).1)⟩
  obtain ⟨e, _heanti, helim, he⟩ := exists_seq_tendsto_sInf hE hEb
  choose u hu hue using he
  let v := runningMin u
  have hv : ∀ n, v n ∈ S := runningMin_mem hu hmin
  let d : X → ℝ := fun x => ⨅ n, v n x
  have hvb : ∀ x, BddBelow (Set.range (fun n => v n x)) := by
    intro x
    exact ⟨0, fun _ ⟨n, hn⟩ => hn ▸ (hbound _ (hv n) x).1⟩
  have hdlim : ∀ x, Tendsto (fun n => v n x) atTop (𝓝 (d x)) :=
    fun x => tendsto_atTop_ciInf (runningMin_antitone u x) (hvb x)
  have hd : d ∈ S := hclosed v hv d hdlim
  have hevle : ∀ n, (∫ x, v n x ∂ν) ≤ e n := by
    intro n
    rw [← hue n]
    exact integral_mono (hi _ (hv n)) (hi _ (hu n)) (runningMin_le u n)
  have hlow : ∀ f ∈ S, sInf E ≤ ∫ x, f x ∂ν :=
    fun f hf => csInf_le hEb ⟨f,hf,rfl⟩
  have hvilim : Tendsto (fun n => ∫ x, v n x ∂ν) atTop (𝓝 (sInf E)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds helim
      (fun n => hlow _ (hv n)) hevle
  have hlimint : Tendsto (fun n => ∫ x, v n x ∂ν) atTop (𝓝 (∫ x, d x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun n => (hmeas _ (hv n)).aestronglyMeasurable) hB
    · intro n
      exact ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound _ (hv n) x).1] using
          (hbound _ (hv n) x).2
    · exact ae_of_all _ hdlim
  have hdenergy : (∫ x, d x ∂ν) = sInf E := tendsto_nhds_unique hlimint hvilim
  refine ⟨d, hd, ?_⟩
  intro f hf
  let z : X → ℝ := fun x => min (d x) (f x)
  have hz : z ∈ S := hmin _ hd _ hf
  have hze : (∫ x, z x ∂ν) = ∫ x, d x ∂ν := le_antisymm
    (integral_mono (hi _ hz) (hi _ hd) (fun x => min_le_left _ _))
    (hdenergy ▸ hlow _ hz)
  have hzero : (∫ x, d x - z x ∂ν) = 0 := by
    rw [integral_sub (hi _ hd) (hi _ hz), hze, sub_self]
  have hnon : ∀ᵐ x ∂ν, 0 ≤ d x - z x := ae_of_all _ fun _ => sub_nonneg.mpr (min_le_left _ _)
  have heq := (integral_eq_zero_iff_of_nonneg_ae hnon ((hi _ hd).sub (hi _ hz))).mp hzero
  filter_upwards [heq] with x hx
  exact le_trans (le_of_eq (sub_eq_zero.mp hx)) (min_le_right _ _)



lemma exists_equivalent_integrable_measure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {B : X → ℝ} (hB : AEMeasurable B μ) :
    ∃ ν : Measure X, μ ≪ ν ∧ ν ≪ μ ∧ Integrable B ν := by
  let w : X → ℝ≥0∞ := fun x => ENNReal.ofReal (1 / (1 + |B x|))
  have hw : AEMeasurable w μ := (aemeasurable_const.div
    (aemeasurable_const.add hB.abs)).ennreal_ofReal
  have hpos : ∀ x, 0 < 1 + |B x| := fun x => by positivity
  have hμν : μ ≪ μ.withDensity w := withDensity_absolutelyContinuous' hw
    (ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (one_div_pos.mpr (hpos x))).ne')
  refine ⟨μ.withDensity w, hμν, withDensity_absolutelyContinuous μ w, ?_⟩
  rw [integrable_withDensity_iff_integrable_smul₀' hw
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  apply (integrable_const (1 : ℝ)).mono' (hw.ennreal_toReal.mul hB).aestronglyMeasurable
  filter_upwards [] with x
  change |(ENNReal.ofReal (1 / (1 + |B x|))).toReal * B x| ≤ 1
  rw [ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr (hpos x))), abs_mul,
    abs_of_pos (one_div_pos.mpr (hpos x)), one_div_mul_eq_div]
  exact (div_le_one (hpos x)).mpr (by linarith [abs_nonneg (B x)])
end WeakHessianCalculus

end

end OAI
