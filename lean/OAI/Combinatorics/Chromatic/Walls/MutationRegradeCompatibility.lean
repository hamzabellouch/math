import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WallRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)
variable (pc : I) (pos : Bool)
local instance mutationRegradeCompatibilityRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutationRegradeCompatibilityAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance mutationRegradeCompatibilityAddGroup : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup

omit [DecidableEq I] in
include hcoord in
lemma completed_full_homogeneous (f : CompletedPositive v Ω C) :
    FullHomogeneous v Ω (rootOrder coord) f.val := by
  intro n m hm
  exact rootOrder_eq C coord hcoord (by by_contra hh; exact hm (f.property.2 n m hh))

include hcoord in
lemma fiberCompletion_nonp_bound (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    RegradeBound v Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val := by
  intro n m hm
  have hr : HasRootDegree C n m:=by by_contra hh; exact hm (f.property.2 n m hh)
  have hnp:=nonpDegree_root_nonneg C coord hcoord pc hr
  have H:=fiber_full_degree_bound Ω C coord hcoord pc pos hr (hf n m hm)
  refine ⟨hnp,?_⟩
  rw [←Int.toNat_of_nonneg hnp] at H
  exact_mod_cast H

include hcoord in
lemma mutationCompletion_read_full (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos))
    (n : ℕ) (m : M) (hm : HasRootDegree C n m) :
    coeff (mutationNewOrder Ω C coord pc pos m).toNat
      (mutationCompletion Ω hΩ C coord pc pos v f.val)
      (mutationLinearPiece Ω C pc pos m)=coeff n f.val m := by
  rw [mutationCompletion,coeff_map,mutationTorusPush_read]
  exact regrade_read v Ω _ _ (rootOrder coord)
    (mutationCompletion_bound Ω hΩ C coord hcoord pc pos v f hf)
    (completed_full_homogeneous v Ω C coord hcoord f) n m (rootOrder_eq C coord hcoord hm)

include hcoord in
lemma mutationCompletion_nonp_bound (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    RegradeBound v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos v f.val) := by
  intro d m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read] at hm
  have hd : d=(mutationNewOrder Ω C coord pc pos a).toNat:=by
    by_contra hh
    exact hm (ite_eq_right hh)
  rw [ite_eq_left hd] at hm
  obtain ⟨n,hn,hval⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
  have hr : HasRootDegree C n a:=by by_contra hh; exact hval (f.property.2 n a hh)
  have hb:=hf n a hval
  obtain ⟨d',hr',hde⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos hr hb
  have ho:=mutationNewOrder_of_root Ω C coord hcoord pc pos hr'
  rw [ho,Int.toNat_natCast] at hd
  subst d'
  have hu:=fiberUpper_degree_bound Ω C coord hcoord pc pos hr
  have hk : 0≤coord a pc:=by
    obtain ⟨b,hb,hbc,he⟩:=root_coordinates C coord hcoord hr
    rw [hbc]
    exact Int.natCast_nonneg _
  have hnp:=nonpDegree_root_nonneg C coord hcoord pc hr
  have H : (d:ℤ)≤((mutationSize Ω C pc+1:ℕ):ℤ)*nonpDegree coord pc a:=by
    push_cast
    nlinarith
  rw [mutated_nonpDegree Ω C coord hcoord pc pos a]
  refine ⟨hnp,?_⟩
  rw [←Int.toNat_of_nonneg hnp] at H
  exact_mod_cast H

include hcoord in
theorem mutation_regrade_compatibility (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    PowerSeries.map (mutationTorusPush Ω hΩ C pc pos v)
      (regrade v Ω (nonpDegree coord pc) (mutationSize Ω C pc+1) f.val)=
    regrade v Ω (nonpDegree (mutatedCoordinates Ω C coord pc) pc) (mutationSize Ω C pc+1)
      (mutationCompletion Ω hΩ C coord pc pos v f.val) := by
  classical
  apply PowerSeries.ext
  intro D
  ext m
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [coeff_map,mutationTorusPush_read]
  by_cases hD : D=(nonpDegree coord pc a).toNat
  · subst D
    by_cases ha : ∃n,coeff n f.val a≠0
    · obtain ⟨n,hn⟩:=ha
      have hr : HasRootDegree C n a:=by by_contra hh; exact hn (f.property.2 n a hh)
      obtain ⟨d,hd,hde⟩:=mutation_root_image Ω C coord hcoord pc hΩ pos hr (hf n a hn)
      have ho:=mutationNewOrder_of_root Ω C coord hcoord pc pos hd
      rw [regrade_read v Ω _ _ (rootOrder coord)
        (fiberCompletion_nonp_bound v Ω C coord hcoord pc pos f hf)
        (completed_full_homogeneous v Ω C coord hcoord f) n a (rootOrder_eq C coord hcoord hr)]
      rw [←mutated_nonpDegree Ω C coord hcoord pc pos a]
      rw [regrade_read v Ω _ _ (rootOrder (mutatedCoordinates Ω C coord pc))
        (mutationCompletion_nonp_bound v Ω hΩ C coord hcoord pc pos f hf)
        (completed_full_homogeneous v Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
          (mutatedCoordinates_retraction Ω C coord hcoord pc)
          (mutationCompletedPositive Ω hΩ C coord hcoord pc pos v f hf)) d _
        (rootOrder_eq (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
          (mutatedCoordinates_retraction Ω C coord hcoord pc) hd)]
      have H:=mutationCompletion_read_full v Ω hΩ C coord hcoord pc pos f hf n a hr
      rw [ho,Int.toNat_natCast] at H
      exact H.symm
    · push Not at ha
      simp only [regrade_coeff_eval,mutated_nonpDegree Ω C coord hcoord pc pos a]
      rw [Finset.sum_eq_zero (fun n hn=>ha n)]
      symm
      apply Finset.sum_eq_zero
      intro d hd
      rw [mutationCompletion_coeff_read]
      split_ifs
      · exact Finset.sum_eq_zero (fun n hn=>ha n)
      · rfl
  · simp only [regrade_coeff_eval,mutated_nonpDegree Ω C coord hcoord pc pos a,ite_eq_right hD]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
