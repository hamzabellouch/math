import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.NormalRestriction
import OAI.Geometry.CAT0Fillings.Slicing.ProfileIntegral
import OAI.Geometry.CAT0Fillings.Currents.Negation
import OAI.Geometry.CAT0Fillings.Currents.Addition
import OAI.Geometry.CAT0Fillings.Slicing.BoundaryTests

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

namespace CAT0Fillings.Slicing
open Set MeasureTheory Filter BorelCoefficients SmoothCutoff BorelRestriction MassMeasure
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}
omit [Nonempty X] in
lemma weightedCurrent_boundary {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    (hI : IntegerRectifiable T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : BoundedLip u) :
    boundarySucc (weightedCurrent (currentMassMeasure hT) hT u) =
      weightedCurrent (currentMassMeasure hB) hB u - contractCurrent u T := by
  classical
  funext b π
  by_cases hab : Admissible b π
  · have hcons : Admissible (fun _ : X => (1:ℝ)) (Matrix.vecCons b π) :=
      ⟨BoundedLip.const 1,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩
    simp only [boundarySucc,ite_eq_left hab,weightedCurrent,ite_eq_left hcons,mul_one,
      Pi.sub_apply,contractCurrent_apply _ _ hab]
    rw [borelAction_eq _ hT (currentMassMeasure_controls hT)
      ⟨hu,fun i => Fin.cases hab.1.1 (fun j => hab.2 j) i⟩,
      borelAction_eq _ hB (currentMassMeasure_controls hB) ⟨hu.mul hab.1,hab.2⟩]
    have h := Foundations.IntegerRectifiable.product_rule hI hab.1 hu π hab.2
    have he : (fun x => b x*u x) = (fun x => u x*b x) := by funext x; exact mul_comm _ _
    rw [he] at h
    linarith
  · simp only [boundarySucc,ite_eq_right hab,Pi.sub_apply,weightedCurrent,contractCurrent,sub_zero]

omit [Nonempty X] in
lemma profile_current_tendsto {T : Functional X k} (hT : IsMetricCurrent T)
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
    Tendsto (fun n : ℕ => weightedCurrent (currentMassMeasure hT) hT
      (profile ((n:ℝ≥0)+1) t ∘ u) b π) atTop
      (𝓝 (restrictCurrent hT {x | t < u x} b π)) := by
  let μ := currentMassMeasure hT
  let E := {x | t < u x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hu.continuous.measurable
  obtain ⟨M,hM⟩ := hab.1.2
  let N := max M 0
  have hN : 0 ≤ N := le_max_right _ _
  have hnb : ∀ x, |b x| ≤ N := fun x => (hM x).trans (le_max_left _ _)
  have hlim : Tendsto (fun n : ℕ => ∫ x, |profile ((n:ℝ≥0)+1) t (u x)*b x - E.indicator b x| ∂μ)
      atTop (𝓝 0) := by
    have hbfun (n : ℕ) (x : X) :
      |profile ((n:ℝ≥0)+1) t (u x)*b x - E.indicator b x| ≤
        N * |profile ((n:ℝ≥0)+1) t (u x)-E.indicator (fun _ => (1:ℝ)) x| := by
      have hi : E.indicator b x = E.indicator (fun _ => (1:ℝ)) x*b x := by
        by_cases hx : x ∈ E <;> simp [hx]
      rw [hi,←sub_mul,abs_mul,mul_comm]
      exact mul_le_mul_of_nonneg_right (hnb x) (abs_nonneg _)
    apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using (profile_L1_tendsto μ hu t).const_mul N)
    rw [←integral_const_mul]
    apply integral_mono
    · exact ((integrable_boundedLip μ ((profile_comp_boundedLip hu _ t).mul hab.1)).sub
        ((integrable_boundedLip μ hab.1).indicator hE)).abs
    · exact (((integrable_boundedLip μ (profile_comp_boundedLip hu _ t)).sub
        ((integrable_const _).indicator hE)).abs).const_mul N
    · exact hbfun n
  simp only [weightedCurrent,restrictCurrent,ite_eq_left hab,Function.comp_apply]
  exact borelAction_tendsto μ hT (currentMassMeasure_controls hT)
    ((integrable_boundedLip μ hab.1).indicator hE)
    (fun n => integrable_boundedLip μ ((profile_comp_boundedLip hu _ t).mul hab.1))
    hlim π hab.2

omit [Nonempty X] in
lemma boundary_profile_coarea_general {T : Functional X (k+1)} (hT : IsMetricCurrent T)
    (hI : IntegerRectifiable T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : BoundedLip u) {S : ℝ → Functional X k}
    (hact : ∀ b π, Admissible b π → Integrable (fun t : ℝ => S t b π) ∧
      T b (Matrix.vecCons u π) = ∫ t : ℝ, S t b π)
    (hweight : ∀ b π, Admissible b π → ∀ φ : ℝ → ℝ, BoundedLip (φ ∘ u) →
      ∀ᵐ t : ℝ, S t (fun x => φ (u x)*b x) π = φ t * S t b π)
    (a : ℝ≥0) (t : ℝ) {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    boundarySucc (weightedCurrent (currentMassMeasure hT) hT (profile a t ∘ u)) b π =
      weightedCurrent (currentMassMeasure hB) hB (profile a t ∘ u) b π -
      ∫ s : ℝ, dprofile a t s * S s b π := by
  rw [weightedCurrent_boundary hT hI hB (profile_comp_boundedLip hu a t)]
  simp only [Pi.sub_apply,contractCurrent_apply _ _ hab]
  congr 1
  have hπ' : ∀ i, ∃ L : ℝ≥0, LipschitzWith L (Matrix.vecCons u π i) :=
    fun i => Fin.cases hu.1 (fun j => hab.2 j) i
  have hchain := Foundations.IntegerRectifiable.apply_update_comp hI hab.1 hu
    (profile_hasDerivAt a t) (profile_comp_boundedLip hu a t)
    (dprofile_comp_boundedLip hu a t) (Matrix.vecCons u π) hπ' 0
  simp only [vecCons_update_head] at hchain
  rw [hchain]
  have heq : (fun x => b x*dprofile a t (u x)) = (fun x => (dprofile a t ∘ u) x*b x) := by
    funext x; exact mul_comm _ _
  rw [heq,(hact _ π ⟨(dprofile_comp_boundedLip hu a t).mul hab.1,hab.2⟩).2]
  exact integral_congr_ae (hweight b π hab (dprofile a t) (dprofile_comp_boundedLip hu a t))

theorem ae_integral_restrict {T : Functional X (k+1)} (hT : IsIntegral (k+1) T)
    (hX : IsCAT0 X) {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∃ G : ℝ → ℝ, Integrable G ∧ (∀ t, 0 ≤ G t) ∧
      (∫ t : ℝ, G t) ≤ K * mass T ∧
      ∀ᵐ t : ℝ, IsIntegral (k+1) (restrictCurrent hT.1 {x | t < u x}) ∧
        mass (boundarySucc (restrictCurrent hT.1 {x | t < u x})) ≤
          mass (restrictCurrent hT.2.2.1 {x | t < u x}) + G t := by
  have hu : BoundedLip u := ⟨⟨K,hK⟩,by
    obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuous.continuousOn
    exact ⟨M,fun x => by simpa only [Real.norm_eq_abs] using hM x (mem_univ _)⟩⟩
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  let E (t : ℝ) := {x | t < u x}
  have hE t : MeasurableSet (E t) := measurableSet_lt measurable_const hu.continuous.measurable
  let B (t : ℝ) := restrictCurrent hT.2.2.1 (E t)
  have hB t : IsMetricCurrent (B t) := restrictCurrent_isMetricCurrent hT.2.2.1 (hE t)
  have htest (b : X → ℝ) (π : Fin k → X → ℝ) (hab : Admissible b π) :
      ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT.1 (E t)) b π = (B t + -S t) b π := by
    filter_upwards [ae_tendsto_dprofile_integral (hact b π hab).1] with t ht
    have hl := profile_boundary_tendsto hT.1 hu t b π hab
    have hr := (profile_current_tendsto hT.2.2.1 hu t b π hab).sub ht
    have heq (n : ℕ) := boundary_profile_coarea_general hT.1 hT.2.1 hT.2.2.1 hu hact hweight ((n:ℝ≥0)+1) t hab
    simpa only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using
      tendsto_nhds_unique (hl.congr (fun n => heq n)) hr
  have heq : ∀ᵐ t : ℝ, boundarySucc (restrictCurrent hT.1 (E t)) = B t + -S t :=
    Foundations.ae_boundary_eq_of_ae_test_eq volume
      (Eventually.of_forall fun t => restrictCurrent_isMetricCurrent hT.1 (hE t))
      (hS.mono fun t ht => (hB t).add ht.1.neg) htest
  refine ⟨G,hG,hG0,hGI,?_⟩
  filter_upwards [hS,heq] with t hs he
  have hBI := integerRectifiable_restrict hT.2.2.1 hT.2.2.2 (hE t)
  have hMC := (hB t).add hs.1.neg
  have hIR := hBI.add (hB t) hs.1.neg hs.2.1.neg
  refine ⟨⟨restrictCurrent_isMetricCurrent hT.1 (hE t),
    integerRectifiable_restrict hT.1 hT.2.1 (hE t),he.symm ▸ hMC,he.symm ▸ hIR⟩,?_⟩
  rw [he]
  exact (mass_add_le (hB t) hs.1.neg).trans (by simpa only [mass_neg] using add_le_add (le_rfl : mass (B t) ≤ mass (B t)) hs.2.2)

end CAT0Fillings.Slicing

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
