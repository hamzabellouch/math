import OAI.NumberTheory.PrimePackets.ErgodicDecomposition
import Mathlib.MeasureTheory.Measure.Support

namespace OAI

/-!
# Ergodic orbits accumulate on the support of a restricted measure

For a countable ergodic group action, almost every orbit meets every
positive-measure set. Applying this to a countable topological basis
shows that the orbit's visits to a measurable set accumulate on the
support of the restricted measure. This is the orbit-density step of
EKL (2006), Proposition 4.3.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Classical

namespace DukePrimeDegree

variable {H Y : Type*} [Group H] [Countable H] [MulAction H Y]
  [MeasurableSpace Y] [MeasurableConstSMul H Y]

/-- The saturation of a positive-measure set is conull in an ergodic action. -/
theorem ae_orbit_meets_of_measure_ne_zero
    (μ : Measure Y) [ErgodicSMul H Y μ]
    (S : Set Y) (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    ∀ᵐ y ∂μ, ∃ h : H, h • y ∈ S := by
  let V : Set Y := ⋃ h : H, (fun y => h • y) ⁻¹' S
  have hV : MeasurableSet V := MeasurableSet.iUnion fun h => hS.preimage (measurable_const_smul h)
  have hinv (g : H) : (fun y => g • y) ⁻¹' V = V := by
    ext y
    simp only [V, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨h, hh⟩
      exact ⟨h * g, by simpa only [mul_smul] using hh⟩
    · rintro ⟨h, hh⟩
      refine ⟨h * g⁻¹, ?_⟩
      simpa only [mul_smul, inv_smul_smul] using hh
  have hconst := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (μ := μ) hV
    (fun g => by rw [hinv g])
  rcases eventuallyEmptyOrUniv_iff.mp hconst with hfull | hnull
  · simpa only [V, mem_iUnion, mem_preimage] using hfull
  · have hz : μ V = 0 := measure_eq_zero_iff_ae_notMem.mpr hnull
    apply (hpos (measure_mono_null (s := S) (t := V) ?_ hz)).elim
    intro y hy
    exact mem_iUnion.mpr ⟨1, by simpa using hy⟩

variable [TopologicalSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]

/-- Almost every orbit's visits to `K` accumulate on the entire support
of the restricted measure; no closedness assumption on `K` is needed. -/
theorem ae_restricted_support_subset_orbit_closure
    (μ : Measure Y) [ErgodicSMul H Y μ] (K : Set Y) (hK : MeasurableSet K) :
    ∀ᵐ y ∂μ, (μ.restrict K).support ⊆
      closure {z : Y | z ∈ K ∧ ∃ h : H, h • y = z} := by
  have hall : ∀ᵐ y ∂μ, ∀ U ∈ TopologicalSpace.countableBasis Y,
      μ (K ∩ U) ≠ 0 → ∃ h : H, h • y ∈ K ∩ U := by
    apply (ae_ball_iff (TopologicalSpace.countable_countableBasis Y)).mpr
    intro U hU
    by_cases hp : μ (K ∩ U) = 0
    · exact ae_of_all _ (fun _ h => (h hp).elim)
    · have hUm := (TopologicalSpace.isOpen_of_mem_countableBasis hU).measurableSet
      exact (ae_orbit_meets_of_measure_ne_zero (H := H) μ _ (hK.inter hUm) hp).mono
        fun y hy _ => hy
  filter_upwards [hall] with y hy
  intro z hz
  apply mem_closure_iff.mpr
  intro V hV hzV
  obtain ⟨U, hU, hzU, hUV⟩ :=
    (TopologicalSpace.isBasis_countableBasis Y).exists_subset_of_mem_open hzV hV
  have hUp : 0 < μ (K ∩ U) := by
    have hp := (Measure.mem_support_iff_forall z).mp hz U
      ((TopologicalSpace.isOpen_of_mem_countableBasis hU).mem_nhds hzU)
    rwa [Measure.restrict_apply (TopologicalSpace.isOpen_of_mem_countableBasis hU).measurableSet,
      inter_comm] at hp
  obtain ⟨h, hhK, hhU⟩ := hy U hU hUp.ne'
  exact ⟨h • y, hUV hhU, hhK, h, rfl⟩

end DukePrimeDegree

end

end OAI
