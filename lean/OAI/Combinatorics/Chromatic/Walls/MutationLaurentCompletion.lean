import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationRegradeCompatibility
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentDeshear
import OAI.Combinatorics.Chromatic.Walls.RootLaurentCompletion
import OAI.Combinatorics.Chromatic.QuantumTorus.MutationInfinityBound

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
include hcoord in
lemma mutation_infinity_full_bound {n : ℕ} {m : M}
    (hm : HasRootDegree (mutatedRoots Ω C pc) n m) :
    (n:ℤ) ≤ -pureDegree coord pc m+(mutationSize Ω C pc+1:ℤ)*
      nonpDegree (mutatedCoordinates Ω C coord pc) pc m := by
  obtain ⟨d,hd,hc,hC⟩:=root_coordinates (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) hm
  have hn (i : I) : 0 ≤ mutatedCoordinates Ω C coord pc m i := by
    rw [hc]
    exact Int.natCast_nonneg _
  have hs : (∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
      mutatedCoordinates Ω C coord pc m i) ≤
      (mutationSize Ω C pc:ℤ)*nonpDegree (mutatedCoordinates Ω C coord pc) pc m := by
    change _ ≤ (mutationSize Ω C pc:ℤ)*(∑i∈Finset.univ.erase pc,
      mutatedCoordinates Ω C coord pc m i)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hn i)
    exact (max_le (abs_nonneg _) (neg_le_abs _)).trans
      (mutationSize_bound Ω C pc i (Finset.mem_erase.mp hi).1)
  have hk : pureDegree coord pc m = -mutatedCoordinates Ω C coord pc m pc+
      ∑i∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc i)*
        mutatedCoordinates Ω C coord pc m i := by
    have H:=congrArg (fun f : I → ℤ => f pc)
      (mutatedCoefficientMap_involutive pc (mutationPairing Ω C pc) (coord m))
    rw [mutatedCoefficientMap_at] at H
    exact H.symm
  have he:=nonpDegree_root_eq (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) pc hm
  nlinarith

variable (v : (LaurentSeries ℚ)ˣ)
local instance mutationLaurentCompletionRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationLaurentCompletionAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationLaurentCompletionAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup

include hcoord in
lemma mutated_series_laurentBounded {f : PowerSeries (Torus v Ω)}
    (hf : SeriesGraded v Ω (mutatedRoots Ω C pc) f) :
    LaurentBounded v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
      (-pureDegree coord pc) (mutationSize Ω C pc) f := by
  intro n m hn
  have hm : HasRootDegree (mutatedRoots Ω C pc) n m := by
    by_contra h
    exact hn (hf n m h)
  exact ⟨nonpDegree_root_nonneg (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) pc hm,
    mutation_infinity_lower_bound Ω C coord hcoord pc hm,
    mutation_infinity_full_bound Ω C coord hcoord pc hm⟩

def mutatedLaurent (f : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    PowerSeries (HahnSeries ℤ (Torus v Ω)) :=
  laurentRegrade v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
    (-pureDegree coord pc) (mutationSize Ω C pc) f.val
    (mutated_series_laurentBounded Ω C coord hcoord pc v f.property.2)

include hcoord in
lemma mutatedLaurent_injective :
    Function.Injective (mutatedLaurent Ω C coord hcoord pc v) := by
  intro f g h
  apply Subtype.ext
  exact laurentRegrade_injective v Ω _ _
    (rootOrder (mutatedCoordinates Ω C coord pc)) _
    (mutated_series_laurentBounded Ω C coord hcoord pc v f.property.2)
    (mutated_series_laurentBounded Ω C coord hcoord pc v g.property.2)
    (completed_full_homogeneous v Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) f)
    (completed_full_homogeneous v Ω (mutatedRoots Ω C pc)
      (mutatedCoordinates Ω C coord pc)
      (mutatedCoordinates_retraction Ω C coord hcoord pc) g) h

def completedInfinityUnit (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (laurentBoundedSubring v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
      (-pureDegree coord pc) (mutationSize Ω C pc))ˣ where
  val:=⟨F.val,mutated_series_laurentBounded Ω C coord hcoord pc v F.property.2⟩
  inv:=⟨(completedInverse v Ω (mutatedRoots Ω C pc) F).val,
    mutated_series_laurentBounded Ω C coord hcoord pc v
      (completedInverse v Ω (mutatedRoots Ω C pc) F).property.2⟩
  val_inv:=Subtype.ext (mul_completedInverse v Ω (mutatedRoots Ω C pc) F)
  inv_val:=Subtype.ext (completedInverse_mul v Ω (mutatedRoots Ω C pc) F)

def infinityCompletedUnit (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (PowerSeries (HahnSeries ℤ (Torus v Ω)))ˣ :=
  Units.map (laurentRegradeHom v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc)
    (-pureDegree coord pc) (mutationSize Ω C pc))
    (completedInfinityUnit Ω C coord hcoord pc v F)

@[simp] lemma infinityCompletedUnit_val (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (infinityCompletedUnit Ω C coord hcoord pc v F).val =
      mutatedLaurent Ω C coord hcoord pc v F := rfl

@[simp] lemma infinityCompletedUnit_inv (F : CompletedPositive v Ω (mutatedRoots Ω C pc)) :
    (infinityCompletedUnit Ω C coord hcoord pc v F).inv =
      mutatedLaurent Ω C coord hcoord pc v (completedInverse v Ω (mutatedRoots Ω C pc) F) := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
