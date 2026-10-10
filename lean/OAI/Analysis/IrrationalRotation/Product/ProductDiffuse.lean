import OAI.Analysis.IrrationalRotation.Product.ProductMultiplierFunctionalCalculus
import OAI.Analysis.IrrationalRotation.Product.ProductScalarity
import OAI.Analysis.IrrationalRotation.Product.ProductTracialVector
import OAI.Analysis.IrrationalRotation.Analysis.DiffuseFromSmallPartitions
import Mathlib.MeasureTheory.Measure.Regular

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Invariant233.ProductModel

def borelSetProjection (θ : ℕ → ℝ) (s : Set Base) (hs : MeasurableSet s) :
    Hilbert →L[ℂ] Hilbert :=
  multiplier θ (s.indicator (fun _ => (1 : ℂ))) 1 zero_le_one
    (measurable_const.indicator hs) (by
      intro x
      by_cases hx : x ∈ s <;> simp [hx])

theorem borelSetProjection_mem (θ : ℕ → ℝ) (s : Set Base) (hs : MeasurableSet s) :
    borelSetProjection θ s hs ∈ factor θ :=
  subset_vonNeumannGenerated _ (Or.inr ⟨_, _, _, _, _, rfl⟩)

theorem borelSetProjection_isStarProjection (θ : ℕ → ℝ) (s : Set Base)
    (hs : MeasurableSet s) : IsStarProjection (borelSetProjection θ s hs) := by
  constructor
  · change borelSetProjection θ s hs * borelSetProjection θ s hs = borelSetProjection θ s hs
    symm
    apply WeightedShift.fieldDiagonal_mul_of_coeff_eq
    exact Eventually.of_forall fun x k => by
      change s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) =
        s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) *
          s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x)
      by_cases hx : rotationIterate θ k x ∈ s <;> simp [hx]
  · change star (borelSetProjection θ s hs) = borelSetProjection θ s hs
    symm
    apply WeightedShift.fieldDiagonal_star_of_eq
    exact Eventually.of_forall fun x => lp.ext (funext fun k => by
      change s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) =
        star (s.indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x))
      by_cases hx : rotationIterate θ k x ∈ s <;> simp [hx])

theorem vectorTrace_borelSetProjection (θ : ℕ → ℝ) (s : Set Base) (hs : MeasurableSet s) :
    vectorTrace traceVector (borelSetProjection θ s hs) = (baseMeasure.real s : ℂ) := by
  unfold borelSetProjection
  rw [vectorTrace_multiplier, integral_indicator hs, integral_const]
  simp [Measure.real]

theorem borelSetProjection_joint_kernel {ι : Type*} [Fintype ι]
    (θ : ℕ → ℝ) (s : ι → Set Base) (hs : ∀ i, MeasurableSet (s i))
    (hcover : ∀ x : Base, ∃ i, x ∈ s i) (v : Hilbert)
    (hv : ∀ i, borelSetProjection θ (s i) (hs i) v = 0) : v = 0 := by
  have hcoord : ∀ i, ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (s i).indicator (fun _ => (1 : ℂ)) (rotationIterate θ k x) * v x k = 0 := by
    intro i
    have h := multiplier_coordinates_ae θ
      ((s i).indicator (fun _ => (1 : ℂ))) 1 zero_le_one
      (measurable_const.indicator (hs i)) (by intro x; by_cases hx : x ∈ s i <;> simp [hx]) v
    change ∀ᵐ x ∂baseMeasure, ∀ k,
      borelSetProjection θ (s i) (hs i) v x k = _ at h
    rw [hv i] at h
    filter_upwards [h, Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hz
    intro k
    simpa [hz] using (hx k).symm
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, Lp.coeFn_zero Fiber 2 baseMeasure] with x hx hz
  rw [hz]
  apply lp.ext
  funext k
  obtain ⟨i, hi⟩ := hcover (rotationIterate θ k x)
  simpa [hi] using hx i k

theorem factor_isDiffuse (θ : ℕ → ℝ) : IsDiffuseVonNeumannAlgebra (factor θ) := by
  classical
  apply isDiffuse_of_small_trace_separating_families (factor θ) traceVector (traceVector_faithfulTracial θ)
  intro ε hε
  have hsmall (x : Base) : ∃ U : Set Base, x ∈ U ∧ IsOpen U ∧ baseMeasure U < ENNReal.ofReal ε := by
    obtain ⟨U, hxU, hU, hm⟩ := isCompact_singleton.exists_isOpen_lt_of_lt
      (μ := baseMeasure) (K := {x}) (ENNReal.ofReal ε) (by
        have hz0 : circleMeasure {x 0} = 0 := by
          change volume {x 0} = 0
          rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
          norm_num
        have hz : baseMeasure {x} = 0 := by
          apply le_antisymm _ (by positivity)
          calc
            baseMeasure {x} ≤ baseMeasure ((fun y : Base => y 0) ⁻¹' {x 0}) := by
              apply measure_mono
              intro y hy
              change y 0 = x 0
              exact congrArg (fun z : Base => z 0) (Set.mem_singleton_iff.mp hy)
            _ = circleMeasure {x 0} := by
              exact (measurePreserving_eval_infinitePi (fun _ : ℕ => circleMeasure) 0).measure_preimage
                (measurableSet_singleton (x 0)).nullMeasurableSet
            _ = 0 := hz0
        rw [hz]
        exact ENNReal.ofReal_pos.mpr hε)
    exact ⟨U, hxU (Set.mem_singleton x), hU, hm⟩
  choose U hxU hU hm using hsmall
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  let e := Fintype.equivFin t
  let s : Fin (Fintype.card t) → Set Base := fun i => U (e.symm i)
  have hs : ∀ i, MeasurableSet (s i) := fun i => (hU (e.symm i)).measurableSet
  refine ⟨Fintype.card t, fun i => borelSetProjection θ (s i) (hs i),
    fun i => borelSetProjection_mem θ (s i) (hs i),
    fun i => borelSetProjection_isStarProjection θ (s i) (hs i), ?_, ?_⟩
  · intro i
    rw [vectorTrace_borelSetProjection]
    change (baseMeasure (s i)).toReal < ε
    exact (ENNReal.toReal_lt_of_lt_ofReal (hm (e.symm i)))
  · apply borelSetProjection_joint_kernel θ s hs
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
    exact ⟨e ⟨y, hy⟩, by simpa only [s, Equiv.symm_apply_apply] using hxy⟩

theorem factor_isTypeII1FactorWithVector (θ : ℕ → ℝ) (hθ : JointlyRationallyIndependent θ) :
    IsTypeII1FactorWithVector (factor θ) traceVector :=
  ⟨factor_isFactor θ hθ, factor_isDiffuse θ, traceVector_faithfulTracial θ⟩

end Invariant233.ProductModel

end

end OAI
