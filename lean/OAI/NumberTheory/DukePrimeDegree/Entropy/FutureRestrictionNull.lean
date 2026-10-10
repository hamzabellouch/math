import OAI.NumberTheory.PrimePackets.LeafSupport

namespace OAI

/-! # Removing a box restriction with only a null-set exception

For future-kernel gluing it suffices that the future measure outside a
box vanishes. Literal containment of every point in the fiber is stronger
than necessary.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem normalized_restriction_of_null_diff {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hB₀ : ν B ≠ 0) (hBtop : ν B ≠ ∞) (hnull : ν (A \ B) = 0) :
    (anchorNormalize ((anchorNormalize ν B).restrict B) A).restrict A =
      (anchorNormalize ν A).restrict A := by
  have hmem : ∀ᵐ y ∂ν.restrict A, y ∈ B := by
    rw [ae_iff]
    change ν.restrict A Bᶜ = 0
    rw [Measure.restrict_apply hB.compl]
    simpa only [Set.sdiff_eq, Set.inter_comm] using hnull
  have heq : (ν.restrict B).restrict A = ν.restrict A := by
    calc
      (ν.restrict B).restrict A = (ν.restrict A).restrict B := by
        rw [Measure.restrict_restrict hA, Measure.restrict_restrict hB, Set.inter_comm]
      _ = ν.restrict A := Measure.restrict_eq_self_of_ae_mem hmem
  have hmass : ν.restrict B A = ν A := by
    have h := congrArg (fun ρ : Measure Y => ρ univ) heq
    simpa only [Measure.restrict_apply_univ] using h
  have hscale : (anchorNormalize ν B).restrict B = (ν B)⁻¹ • ν.restrict B := by
    rw [anchorNormalize, Measure.restrict_smul]
  rw [hscale, anchorNormalize_smul _ _ _ (ENNReal.inv_ne_zero.mpr hBtop)
    (ENNReal.inv_ne_top.mpr hB₀)]
  simp only [anchorNormalize, Measure.restrict_smul, hmass, heq]

end DukePrimeDegree

end

end OAI
