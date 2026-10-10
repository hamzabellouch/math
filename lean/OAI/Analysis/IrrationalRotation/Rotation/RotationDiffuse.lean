import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Rotation.RotationTrace
import OAI.Analysis.IrrationalRotation.Rotation.RotationCenter
import OAI.Analysis.IrrationalRotation.Analysis.DiffuseFromSmallPartitions
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Invariant233.Rotation

def borelSetProjection (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    Hilbert →L[ℂ] Hilbert :=
  measurableRepresentation θ (s.indicator (fun _ => (1 : ℂ))) 1 zero_le_one
    (measurable_const.indicator hs) (by
      intro x
      by_cases hx : x ∈ s <;> simp [hx])

theorem borelSetProjection_mem (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    borelSetProjection θ s hs ∈ algebra θ :=
  measurableRepresentation_mem_algebra _ _ _ _ _ _

theorem borelSetProjection_isStarProjection (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) : IsStarProjection (borelSetProjection θ s hs) := by
  constructor
  · change borelSetProjection θ s hs * borelSetProjection θ s hs = borelSetProjection θ s hs
    symm
    apply WeightedShift.fieldDiagonal_mul_of_coeff_eq
    exact Eventually.of_forall fun x k => by
      change s.indicator (fun _ => (1 : ℂ)) (action θ k x) =
        s.indicator (fun _ => (1 : ℂ)) (action θ k x) *
          s.indicator (fun _ => (1 : ℂ)) (action θ k x)
      by_cases hx : action θ k x ∈ s <;> simp [hx]
  · change star (borelSetProjection θ s hs) = borelSetProjection θ s hs
    symm
    apply WeightedShift.fieldDiagonal_star_of_eq
    exact Eventually.of_forall fun x => lp.ext (funext fun k => by
      change s.indicator (fun _ => (1 : ℂ)) (action θ k x) =
        star (s.indicator (fun _ => (1 : ℂ)) (action θ k x))
      by_cases hx : action θ k x ∈ s <;> simp [hx])

theorem vectorTrace_borelSetProjection (θ : ℝ) (s : Set Circle) (hs : MeasurableSet s) :
    vectorTrace vacuum (borelSetProjection θ s hs) = (circleMeasure.real s : ℂ) := by
  change inner ℂ vacuum (borelSetProjection θ s hs vacuum) = _
  rw [L2.inner_def]
  have heq : (fun x => inner ℂ (vacuum x) (borelSetProjection θ s hs vacuum x)) =ᵐ[circleMeasure]
      s.indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [Lp.coeFn_const 2 circleMeasure (lp.single 2 (0 : ℤ) (1 : ℂ) : Fiber),
      WeightedShift.fieldDiagonal_ae (measurableOrbitWeight θ (s.indicator (fun _ => (1 : ℂ))) 1
        (by intro x; by_cases hx : x ∈ s <;> simp [hx])) _ _ _ _ vacuum] with x hv hp
    change vacuum x = lp.single 2 (0 : ℤ) (1 : ℂ) at hv
    change borelSetProjection θ s hs vacuum x = _ at hp
    rw [hp, hv, lp.inner_single_left]
    change inner ℂ (1 : ℂ) (s.indicator (fun _ => (1 : ℂ)) (action θ 0 x) * 1) = _
    simp [action]
  rw [integral_congr_ae heq, integral_indicator hs, integral_const]
  simp [Measure.real]

theorem borelSetProjection_joint_kernel {ι : Type*} [Fintype ι]
    (θ : ℝ) (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hcover : ∀ x : Circle, ∃ i, x ∈ s i) (v : Hilbert)
    (hv : ∀ i, borelSetProjection θ (s i) (hs i) v = 0) : v = 0 := by
  have hcoord : ∀ i, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      (s i).indicator (fun _ => (1 : ℂ)) (action θ k x) * v x k = 0 := by
    intro i
    have h := measurableRepresentation_coordinates_ae θ
      ((s i).indicator (fun _ => (1 : ℂ))) 1 zero_le_one
      (measurable_const.indicator (hs i)) (by intro x; by_cases hx : x ∈ s i <;> simp [hx]) v
    change ∀ᵐ x ∂circleMeasure, ∀ k,
      borelSetProjection θ (s i) (hs i) v x k = _ at h
    rw [hv i] at h
    filter_upwards [h, Lp.coeFn_zero Fiber 2 circleMeasure] with x hx hz
    intro k
    simpa [hz] using (hx k).symm
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, Lp.coeFn_zero Fiber 2 circleMeasure] with x hx hz
  rw [hz]
  apply lp.ext
  funext k
  obtain ⟨i, hi⟩ := hcover (action θ k x)
  simpa [hi] using hx i k

theorem algebra_isDiffuse (θ : ℝ) : IsDiffuseVonNeumannAlgebra (algebra θ) := by
  classical
  apply isDiffuse_of_small_trace_separating_families (algebra θ) vacuum (vacuum_faithfulTracial θ)
  intro ε hε
  have hsmall (x : Circle) : ∃ U : Set Circle, x ∈ U ∧ IsOpen U ∧ circleMeasure U < ENNReal.ofReal ε := by
    obtain ⟨U, hxU, hU, hm⟩ := isCompact_singleton.exists_isOpen_lt_of_lt
      (μ := circleMeasure) (K := {x}) (ENNReal.ofReal ε) (by
        have hz : circleMeasure {x} = 0 := by
          change volume {x} = 0
          rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
          norm_num
        rw [hz]
        exact ENNReal.ofReal_pos.mpr hε)
    exact ⟨U, hxU (Set.mem_singleton x), hU, hm⟩
  choose U hxU hU hm using hsmall
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  let e := Fintype.equivFin t
  let s : Fin (Fintype.card t) → Set Circle := fun i => U (e.symm i)
  have hs : ∀ i, MeasurableSet (s i) := fun i => (hU (e.symm i)).measurableSet
  refine ⟨Fintype.card t, fun i => borelSetProjection θ (s i) (hs i),
    fun i => borelSetProjection_mem θ (s i) (hs i),
    fun i => borelSetProjection_isStarProjection θ (s i) (hs i), ?_, ?_⟩
  · intro i
    rw [vectorTrace_borelSetProjection]
    change (circleMeasure (s i)).toReal < ε
    exact (ENNReal.toReal_lt_of_lt_ofReal (hm (e.symm i)))
  · apply borelSetProjection_joint_kernel θ s hs
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact ⟨e ⟨y, hy⟩, by simpa only [s, Equiv.symm_apply_apply] using hxy⟩

theorem algebra_isTypeII1FactorWithVector (θ : ℝ) (hθ : Irrational θ) :
    IsTypeII1FactorWithVector (algebra θ) vacuum :=
  ⟨algebra_isFactor_independent θ hθ, algebra_isDiffuse θ, vacuum_faithfulTracial θ⟩

end Invariant233.Rotation

end

end OAI
