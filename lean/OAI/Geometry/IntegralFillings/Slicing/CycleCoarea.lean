import Mathlib
import OAI.Geometry.IntegralFillings.Slicing.RectifiableCoarea
import OAI.Geometry.IntegralFillings.Slicing.NormalRestriction
import OAI.Geometry.IntegralFillings.Slicing.ProfileIntegral
import OAI.Geometry.IntegralFillings.Currents.Negation

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
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open scoped ENNReal NNReal Topology
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.Slicing
open Set MeasureTheory Filter BorelCoefficients SmoothCutoff BorelRestriction MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [Nonempty X] in
lemma boundary_profile_coarea {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    (hI : IntegerRectifiable T) (hz : IsCycle T) {u : X → ℝ} (hu : BoundedLip u)
    {S : ℝ → Functional X k}
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π)
    (a : ℝ≥0) (t : ℝ) {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    boundarySucc (weightedCurrent (currentMassMeasure hT) hT (profile a t ∘ u)) b π =
      -(∫ s : ℝ, dprofile a t s * S s b π) := by
  rw [weightedCurrent_boundary_cycle hT hI hz _ (currentMassMeasure_controls hT)
    (profile_comp_boundedLip hu a t)]
  simp only [Pi.neg_apply,contractCurrent_apply _ _ hab]
  congr 1
  have hπ' : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) :=
    fun i => Fin.cases hu.1 (fun j => hab.2 j) i
  have hchain := Foundations.IntegerRectifiable.apply_update_comp hI hab.1 hu
    (profile_hasDerivAt a t) (profile_comp_boundedLip hu a t)
    (dprofile_comp_boundedLip hu a t) (Matrix.vecCons u π) hπ' 0
  simp only [vecCons_update_head] at hchain
  rw [hchain]
  have heq : (fun x => b x*dprofile a t (u x)) = (fun x => dprofile a t (u x)*b x) := by
    funext x; exact mul_comm _ _
  rw [heq]
  change T (fun x => (dprofile a t ∘ u) x*b x) (Matrix.vecCons u π) = _
  rw [(hact _ π ⟨(dprofile_comp_boundedLip hu a t).mul hab.1,hab.2⟩).2]
  exact integral_congr_ae (hweight b π hab (dprofile a t) (dprofile_comp_boundedLip hu a t))

theorem ae_integral_restrict_cycle {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) (hz : IsCycle T)
    (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass T ∧
      ∀ᵐ t : ℝ, IsIntegral (k+1) (restrictCurrent hT {x | t < u x}) ∧
        mass (boundarySucc (restrictCurrent hT {x | t < u x})) ≤ G t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT hI hX hK
  have hR := ae_normal_restrict_cycle hT hI hz hu
  have htest (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
      ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT {x | t < u x}) b π = (-S t) b π := by
    filter_upwards [ae_tendsto_dprofile_integral (hact b π hab).1] with t ht
    have hl := profile_boundary_tendsto hT hu t b π hab
    have heq (n : ℕ) := boundary_profile_coarea hT hI hz hu hact hweight ((n:ℝ≥0)+1) t hab
    exact tendsto_nhds_unique (hl.congr (fun n => heq n)) ht.neg
  have heq : ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT {x | t < u x}) = -S t :=
    Foundations.ae_eq_of_ae_test_eq volume (hR.mono fun _ ht => ht.2.2)
      (hS.mono fun _ ht => ht.1.neg) htest
  refine ⟨G,hG,hG0,hGI,?_⟩
  filter_upwards [hR,hS,heq] with t hr hs he
  refine ⟨⟨hr.1,hr.2.1,hr.2.2,?_⟩,?_⟩
  · rw [he]
    exact hs.2.1.neg
  · rw [he,mass_neg]
    exact hs.2.2

end SharpIntegralFillings.Slicing

end

end OAI
