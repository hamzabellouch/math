import OAI.NumberTheory.TwoPoint.Bounds.ResidueWitnessHybrid
import OAI.NumberTheory.TwoPoint.Bounds.PaddingWitnessProbability

namespace OAI

/-! Forcing lit nonsingletons commutes with singleton differences; padding stays outside them. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem selectedMixedDifference_invariant_factor {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (S M : Finset ι) (hSM : S ⊆ M) (a x : ι → A)
    (R F : (ι → A) → ℝ)
    (hR : ∀ y z, (∀ i, i ∉ M → y i = z i) → R y = R z) :
    selectedMixedDifference S a (fun y => R y * F y) x =
      R x * selectedMixedDifference S a F x := by
  have hsame (z : S → A) :
      R (joinCoordinates S z (fun i : {i // i ∉ S} => x i)) = R x := by
    apply hR
    intro i hi
    have hiS : i ∉ S := fun his => hi (hSM his)
    simp only [joinCoordinates, hiS, dite_false]
  unfold selectedMixedDifference
  simp_rw [hsame]
  exact mixedDifference_const_mul _ _ _ _

theorem selectedMixedDifference_force_disjoint {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] (S T : Finset ι) (hST : Disjoint S T)
    (a b x : ι → A) (F : (ι → A) → ℝ) :
    selectedMixedDifference S a (fun y => F (forceCoordinates T b y)) x =
      selectedMixedDifference S a F (forceCoordinates T b x) := by
  have hcomm (z : S → A) :
      forceCoordinates T b (joinCoordinates S z (fun i : {i // i ∉ S} => x i)) =
        joinCoordinates S z (fun i : {i // i ∉ S} => forceCoordinates T b x i) := by
    funext i
    by_cases hiS : i ∈ S
    · have hiT : i ∉ T := fun hiT => disjoint_left.mp hST hiS hiT
      simp only [forceCoordinates_apply, hiT, ite_false, joinCoordinates, hiS, dite_true]
    · simp only [joinCoordinates, hiS, dite_false, forceCoordinates_apply]
  have hx : (fun i : S => forceCoordinates T b x i) = (fun i : S => x i) := by
    funext i
    have hiT : i.val ∉ T := fun hiT => disjoint_left.mp hST i.property hiT
    simp only [forceCoordinates_apply, hiT, ite_false]
  unfold selectedMixedDifference
  simp_rw [hcomm]
  rw [hx]

theorem selectedMixedDifference_retainedMainTests {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (S M : Finset ι) (hSM : S ⊆ M)
    (h B : ℕ) (main : List SignedStep) (a x : ι → Fin B) (F : (ι → Fin B) → ℝ) :
    selectedMixedDifference S a
      (fun y => (if RetainedMainTests p M h B main y then 1 else 0) * F y) x =
      (if RetainedMainTests p M h B main x then 1 else 0) *
        selectedMixedDifference S a F x := by
  have hsame (z : S → Fin B) :
      RetainedMainTests p M h B main (joinCoordinates S z (fun i : {i // i ∉ S} => x i)) ↔
        RetainedMainTests p M h B main x := by
    apply retainedMainTests_congr
    intro i hi
    have hiS : i ∉ S := fun his => hi (hSM his)
    simp only [joinCoordinates, hiS, dite_false]
  unfold selectedMixedDifference
  simp_rw [hsame]
  exact mixedDifference_const_mul _ _ _ _

lemma witnessAvoidance_abs_le_one {ι A W : Type*} [Fintype W]
    (I : W → (ι → A) → Bool) (x : ι → A) : |witnessAvoidance I x| ≤ 1 := by
  unfold witnessAvoidance
  rw [abs_prod]
  calc
    _ ≤ ∏ _w : W, (1 : ℝ) := by
      apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro w _
      cases hi : I w x <;> norm_num [hi]
    _ = _ := prod_const_one

end TwoPointCorrelations

end OAI
