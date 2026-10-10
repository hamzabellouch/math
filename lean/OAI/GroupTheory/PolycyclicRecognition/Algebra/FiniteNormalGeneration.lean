import OAI.GroupTheory.PolycyclicRecognition.Algebra.Abelian
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicFiniteGeneration
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Abelianization.Defs

namespace OAI

/-! # Finite normal generators over an abelian quotient

A finitely generated ambient group supplies finitely many normal generators
for every normal subgroup with abelian quotient. This prepares the finite
group-ring module in the nilpotent-by-abelian finiteness argument.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped commutatorElement
variable {G : Type} [Group G]

theorem commutator_le_normal_of_generators (s : Set G)
    (hgen : Subgroup.closure s = ⊤) (N : Subgroup G) [N.Normal]
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, ⁅x, y⁆ ∈ N) : commutator G ≤ N := by
  let f := QuotientGroup.mk' N
  have hs (x : G) (hx : x ∈ s) (y : G) (hy : y ∈ s) :
      Commute (f x) (f y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hcomm x hx y hy)
  have hsall (x : G) (hx : x ∈ s) (y : G) : Commute (f x) (f y) := by
    have hy : y ∈ Subgroup.closure s := hgen ▸ Subgroup.mem_top _
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hs x hx y hy
    | one => rw [map_one]; exact Commute.one_right _
    | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul_right hz
    | inv y _ hy => rw [map_inv]; exact hy.inv_right
  have hall (x y : G) : Commute (f x) (f y) := by
    have hx : x ∈ Subgroup.closure s := hgen ▸ Subgroup.mem_top _
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hsall x hx y
    | one => rw [map_one]; exact Commute.one_left _
    | mul x z _ _ hx hz => rw [map_mul]; exact hx.mul_left hz
    | inv x _ hx => rw [map_inv]; exact hx.inv_left
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  apply (QuotientGroup.eq_one_iff _).mp
  change f ⁅x, y⁆ = 1
  rw [map_commutatorElement]
  exact (hall x y).commutator_eq

theorem commutator_finitelyNormallyGenerated [Group.FG G] :
    (commutator G).IsFinitelyNormallyGenerated := by
  obtain ⟨s, hgen, hs⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let c := (fun p : G × G => ⁅p.1, p.2⁆) '' (s ×ˢ s)
  refine ⟨c, (hs.prod hs).image _, le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨⟨x, y⟩, _, rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · apply commutator_le_normal_of_generators s hgen
    intro x hx y hy
    exact Subgroup.subset_normalClosure ⟨(x, y), ⟨hx, hy⟩, rfl⟩

theorem finitelyNormallyGenerated_of_commutator_le [Group.FG G]
    (N : Subgroup G) [N.Normal] (hN : commutator G ≤ N) :
    N.IsFinitelyNormallyGenerated := by
  let f := Abelianization.of (G := G)
  let : Group.FG (Abelianization G) :=
    Group.fg_of_surjective (f := f) (QuotientGroup.mk'_surjective (commutator G))
  let A := N.map f
  let : Group.FG A :=
    ((isPolycyclic_of_finitelyGenerated_commGroup (Abelianization G)).of_injective
      A.subtype A.subtype_injective).finitelyGenerated
  have hA : A.IsFinitelyNormallyGenerated := .of_FG A
  have hf : f.ker.IsFinitelyNormallyGenerated := by
    change (Abelianization.of (G := G)).ker.IsFinitelyNormallyGenerated
    rw [Abelianization.ker_of]
    exact commutator_finitelyNormallyGenerated
  have h := hA.comap (f := f) (QuotientGroup.mk'_surjective (commutator G)) hf
  have hker : f.ker ≤ N := by simpa only [f, Abelianization.ker_of] using hN
  change ((N.map f).comap f).IsFinitelyNormallyGenerated at h
  rwa [Subgroup.comap_map_eq_self hker] at h

theorem finitelyNormallyGenerated_of_abelian_quotient [Group.FG G]
    (N : Subgroup G) [N.Normal] [IsMulCommutative (G ⧸ N)] :
    N.IsFinitelyNormallyGenerated := by
  apply finitelyNormallyGenerated_of_commutator_le N
  have h := Abelianization.commutator_subset_ker (QuotientGroup.mk' N)
  simpa only [QuotientGroup.ker_mk'] using h

end PolycyclicRecognition

end

end OAI
