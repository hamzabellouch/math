import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Analysis.PurePointDiffuse

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.WeightedShift

variable {X I : Type*} [MeasurableSpace X] {μ : Measure X} [Countable I]

theorem jointEigenspace_fieldDiagonal_eq_bot
    (a : I → X → Weight) (C : I → ℝ) (hC : ∀ i, 0 ≤ C i)
    (ha : ∀ i x, ‖a i x‖ ≤ C i)
    (hm : ∀ i k, AEStronglyMeasurable (fun x => a i x k) μ)
    (ev : I → ℂ)
    (hnull : ∀ k : ℤ, μ {x | ∀ i, a i x k = ev i} = 0) :
    jointEigenspace (fun i => fieldDiagonal (a i) (C i) (hC i) (ha i) (hm i)) ev = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have heigen := mem_jointEigenspace.mp hf
  have hcoord : ∀ i, ∀ᵐ x ∂μ, ∀ k : ℤ,
      a i x k * f x k = ev i * f x k := by
    intro i
    have hsmul := Lp.coeFn_smul (ev i) f
    filter_upwards [fieldDiagonal_coordinate_ae (a i) (C i) (hC i) (ha i) (hm i) f,
      hsmul] with x hx hs k
    have h := congrArg (fun v : Lp Hilbert 2 μ => v x k) (heigen i)
    rw [hx] at h
    rw [hs] at h
    exact h
  have havoid : ∀ k : ℤ, ∀ᵐ x ∂μ, ¬ ∀ i, a i x k = ev i := by
    intro k
    exact measure_eq_zero_iff_ae_notMem.mp (hnull k)
  have hfzero : f = 0 := by
    apply Lp.ext
    filter_upwards [ae_all_iff.mpr hcoord, ae_all_iff.mpr havoid, Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := μ)]
      with x hx hav hz
    rw [hz]
    apply lp.ext
    funext k
    change f x k = 0
    by_contra hfk
    apply hav k
    intro i
    exact mul_right_cancel₀ hfk (hx i k)
  exact hfzero

end Invariant233.WeightedShift

end

end OAI
