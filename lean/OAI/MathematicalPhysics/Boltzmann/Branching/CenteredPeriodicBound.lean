import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicSourceBound
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusChart

namespace OAI

/-! # Almost-everywhere periodic bounds from the centered fundamental cube -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_shift_in_centered_cell (y : JetPrototype.Space) :
    ∃ (n : JetLattice.Lattice) (x : Velocity), x ∈ TorusChart.cube ∧
      y-displacement n = JetPeriodicDatum.spatialMap x := by
  obtain ⟨v,hv⟩ := spatialMap_surjective y
  let n : JetLattice.Lattice := fun k => ⌈v k-1/2⌉
  let x : Velocity := WithLp.toLp 2 (fun k => v k-(n k : ℝ))
  refine ⟨n,x,?_,?_⟩
  · intro k
    change -(1/2:ℝ) < v k-(⌈v k-1/2⌉:ℝ) ∧ v k-(⌈v k-1/2⌉:ℝ) ≤ 1/2
    constructor
    · linarith [Int.ceil_lt_add_one (v k-1/2)]
    · linarith [Int.le_ceil (v k-1/2)]
  · rw [← hv]
    apply Prod.ext
    · apply (WithLp.ext_iff 2).mpr
      funext k
      rfl
    · rfl

theorem ae_bound_of_centered_cell {T : ℝ} {k : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hkm : Measurable k) (hwm : Measurable w)
    (hperiodic : ∀ n, pull (displacement n) k = k)
    (hcell : ∀ t ∈ Ioc 0 T, ∀ x : Velocity, x ∈ TorusChart.cube →
      ∀ᵐ v : Velocity, k (t,(JetPeriodicDatum.spatialMap x,v)) ≤ w t) :
    ∀ᵐ u ∂WeightedLocal.spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
  apply ae_bound_of_cell hkm hwm hperiodic
  intro t ht x _
  obtain ⟨n,y,hy,he⟩ := exists_shift_in_centered_cell (JetPeriodicDatum.spatialMap x)
  filter_upwards [hcell t ht y hy] with v hv
  have hk := congrFun (hperiodic n) (t,(JetPeriodicDatum.spatialMap x,v))
  change k (t,(JetPeriodicDatum.spatialMap x-displacement n,v)) =
    k (t,(JetPeriodicDatum.spatialMap x,v)) at hk
  rw [he] at hk
  rwa [← hk]

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
