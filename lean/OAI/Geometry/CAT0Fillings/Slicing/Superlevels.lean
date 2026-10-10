import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.GeneralCoarea
import OAI.Geometry.CAT0Fillings.Slicing.WeakRestriction

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
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter SmoothCutoff BorelCoefficients BorelRestriction MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
omit [CompactSpace X] in
lemma ae_level_measure_zero (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : BoundedLip u) : ∀ᵐ t : ℝ, μ {x | u x = t} = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ) hu.continuous.measurable
  filter_upwards [hc.ae_notMem volume] with t ht
  exact le_antisymm (le_of_not_gt ht) (bot_le)

noncomputable def superlevelSlice {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    (u : X → ℝ) (t : ℝ) : Functional X k :=
  restrictCurrent hB {x | t < u x} - boundarySucc (restrictCurrent hT {x | t < u x})

lemma superlevelSlice_weak_tendsto {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hT : IsMetricCurrent T)
    (hBs : ∀ j, IsMetricCurrent (boundarySucc (Ts j))) (hB : IsMetricCurrent (boundarySucc T))
    (μs νs : ι → FiniteMeasure X) (μ ν : FiniteMeasure X)
    (hμs : ∀ j, Controls (Ts j) (μs j)) (hμ : Controls T μ)
    (hνs : ∀ j, Controls (boundarySucc (Ts j)) (νs j)) (hν : Controls (boundarySucc T) ν)
    (hμlim : Tendsto μs l (𝓝 μ)) (hνlim : Tendsto νs l (𝓝 ν))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (htμ : (μ : Measure X) {x | u x = t} = 0) (htν : (ν : Measure X) {x | u x = t} = 0)
    (b : X → ℝ) (π : Fin k → X → ℝ) :
    Tendsto (fun j => superlevelSlice (hTs j) (hBs j) u t b π) l
      (𝓝 (superlevelSlice hT hB u t b π)) := by
  have hrestr := restrictCurrent_weak_tendsto hTs hT μs μ hμs hμ hμlim hlim hu t htμ
  have hbd := boundarySucc_weak_limit (fun b π => hrestr b π)
  have hrestrB := restrictCurrent_weak_tendsto hBs hB νs ν hνs hν hνlim
    (boundarySucc_weak_limit hlim) hu t htν b π
  exact hrestrB.sub (hbd b π)

lemma ae_superlevelSlice_weak_tendsto {ι : Type*} {l : Filter ι} {k : ℕ}
    {Ts : ι → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsMetricCurrent (Ts j)) (hT : IsMetricCurrent T)
    (hBs : ∀ j, IsMetricCurrent (boundarySucc (Ts j))) (hB : IsMetricCurrent (boundarySucc T))
    (μs νs : ι → FiniteMeasure X) (μ ν : FiniteMeasure X)
    (hμs : ∀ j, Controls (Ts j) (μs j)) (hμ : Controls T μ)
    (hνs : ∀ j, Controls (boundarySucc (Ts j)) (νs j)) (hν : Controls (boundarySucc T) ν)
    (hμlim : Tendsto μs l (𝓝 μ)) (hνlim : Tendsto νs l (𝓝 ν))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) l (𝓝 (T b π)))
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, ∀ b π, Tendsto (fun j => superlevelSlice (hTs j) (hBs j) u t b π) l
      (𝓝 (superlevelSlice hT hB u t b π)) := by
  filter_upwards [ae_level_measure_zero (μ : Measure X) hu,ae_level_measure_zero (ν : Measure X) hu]
    with t hμt hνt
  exact superlevelSlice_weak_tendsto hTs hT hBs hB μs νs μ ν hμs hμ hνs hν hμlim hνlim hlim hu t hμt hνt

end CAT0Fillings.Slicing
namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients SmoothCutoff BorelRestriction MassMeasure Foundations
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma ae_superlevelSlice_eq_coarea {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : BoundedLip u) {S : ℝ → Functional X k}
    (hS : ∀ᵐ t : ℝ, IsMetricCurrent (S t))
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π) :
    ∀ᵐ t : ℝ, superlevelSlice hT hB u t = S t := by
  let E (t : ℝ) := {x | t < u x}
  have hE t : MeasurableSet (E t) := measurableSet_lt measurable_const hu.continuous.measurable
  let B (t : ℝ) := restrictCurrent hB (E t)
  have hBc t : IsMetricCurrent (B t) := restrictCurrent_isMetricCurrent hB (hE t)
  have htest (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
      ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT (E t)) b π = (B t + -S t) b π := by
    filter_upwards [ae_tendsto_dprofile_integral (hact b π hab).1] with t ht
    have hl := profile_boundary_tendsto hT hu t b π hab
    have hr := (profile_current_tendsto hB hu t b π hab).sub ht
    have heq (n : ℕ) := boundary_profile_coarea_general hT hI hB hu hact hweight ((n:ℝ≥0)+1) t hab
    simpa only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using
      tendsto_nhds_unique (hl.congr (fun n => heq n)) hr
  have heq : ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT (E t)) = B t + -S t :=
    ae_boundary_eq_of_ae_test_eq volume
      (Eventually.of_forall fun t => restrictCurrent_isMetricCurrent hT (hE t))
      (hS.mono fun t ht => (hBc t).add ht.neg) htest
  filter_upwards [heq] with t ht
  change B t - boundarySucc (restrictCurrent hT (E t)) = S t
  rw [ht]
  abel

lemma superlevelSlice_coarea_bound [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K*mass T ∧
      ∀ᵐ t : ℝ, IsMetricCurrent (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        IntegerRectifiable (superlevelSlice hT.1 hT.2.2.1 u t) ∧
        mass (superlevelSlice hT.1 hT.2.2.1 u t) ≤ G t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  refine ⟨G,hG,hG0,hGI,?_⟩
  filter_upwards [hS,ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1 hu
    (hS.mono fun t ht => ht.1) hact hweight] with t ht he
  rw [he]
  exact ht

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Set MeasureTheory Filter
open scoped Topology NNReal

end

end OAI
