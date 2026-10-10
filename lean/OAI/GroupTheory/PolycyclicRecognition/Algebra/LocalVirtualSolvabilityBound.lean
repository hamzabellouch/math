import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedCentralLayerSolvability
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualNilpotentNormalCore
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalLocallyNilpotentDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformLocalVirtualSolvability
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedLocallyFiniteKernel

namespace OAI

/-! # Uniform virtual solvability in locally virtually nilpotent groups -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

def virtualSolvabilityIndexBound (b d : ℕ) : ℕ :=
  3 ^ ((2 * d * d) * (2 * d * d)) * b ^ b

theorem virtuallyNilpotent_bounded_solvable_subgroup [Group.FG G]
    (b d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    (hG : Group.IsVirtuallyNilpotent G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ H.index ≤ virtualSolvabilityIndexBound b d ∧
      derivedSeries H (2 * d + 2) = ⊥ := by
  obtain ⟨F, hFn, hFi, hF, hFt⟩ := exists_normal_torsionFree_nilpotent_finiteIndex hG
  let := hFn
  let := hFi
  let := hF
  have hFg : F.FG := (Group.fg_iff_subgroup_fg F).mp inferInstance
  let : HasProjectiveDimensionLE (trivialIntegral F) d := hd.nilpotent_subgroup_dimension F hFg hFt
  obtain ⟨H, hHi, hHb, hHr⟩ := bounded_solvable_subgroup_of_nilpotent_finiteIndex F hFt b d hb
  have hc : Group.nilpotencyClass F ≤ 2 * d := nilpotencyClass_le_twice_cohomologicalDimension d
  refine ⟨H, hHi, ?_, ?_⟩
  · apply hHb.trans
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_self_le_mul_self (Nat.mul_le_mul_right d hc)
  · apply eq_bot_iff.mpr
    exact (derivedSeries_antitone H (Nat.add_le_add_right hc 2)).trans_eq hHr

theorem locallyVirtuallyNilpotent_bounded_solvable_subgroup
    (b d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : ∀ N : Subgroup G, Finite N → Nat.card N ≤ b)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ H.index ≤ virtualSolvabilityIndexBound b d ∧
      derivedSeries H (2 * d + 2) = ⊥ := by
  apply uniformLocalVirtualSolvability
  intro H hH
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  apply virtuallyNilpotent_bounded_solvable_subgroup b d (hd.subgroup H) _ (hlocal H hH)
  intro N hN
  let := hN
  let e := N.equivMapOfInjective H.subtype Subtype.val_injective
  let : Finite (N.map H.subtype) := Finite.of_equiv N e.toEquiv
  simpa only [Nat.card_congr e.toEquiv] using hb (N.map H.subtype) inferInstance

theorem locallyVirtuallyNilpotent_virtualSolvable
    (d : ℕ) (hd : RationalHomologyDimensionLE G d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsVirtuallyNilpotent H) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨H, hHi, _, hHr⟩ := locallyVirtuallyNilpotent_bounded_solvable_subgroup b d hd hb hlocal
  exact ⟨H, hHi, ⟨2 * d + 2, hHr⟩⟩

end PolycyclicRecognition

end

end OAI
