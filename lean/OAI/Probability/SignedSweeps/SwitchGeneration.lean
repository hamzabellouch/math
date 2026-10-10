import OAI.Probability.SignedSweeps.Model

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma swap_mem_fiberSubgroup {A C : Type*} [DecidableEq A] (f : A → C)
    {x y : A} (hxy : f x = f y) : Equiv.swap x y ∈ fiberSubgroup f := by
  intro z
  by_cases hx : z = x
  · subst z; simpa using hxy.symm
  by_cases hy : z = y
  · subst z; simpa using hxy
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma top_of_coordinate_swaps {I A X : Type*} [Fintype I] [Finite X] [DecidableEq I] [DecidableEq X]
    (e : (I → A) ≃ X) (H : Subgroup (Equiv.Perm X))
    (hH : ∀ (i : I) (x : I → A) (a : A),
      Equiv.swap (e x) (e (Function.update x i a)) ∈ H) : H = ⊤ := by
  classical
  have aux : ∀ s : Finset I, ∀ x y : I → A,
      (∀ i, i ∉ s → x i = y i) → Equiv.swap (e x) (e y) ∈ H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y hxy
      have he : x = y := funext (fun i => hxy i (by simp))
      rw [he, Equiv.swap_self]
      exact H.one_mem
    | @insert i s hi ih =>
      intro x y hxy
      refine SubmonoidClass.swap_mem_trans H (hH i x (y i)) (ih _ y ?_)
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · rw [Function.update_of_ne hji]
        exact hxy j (by simp [hj, hji])
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro g ⟨x, y, _, rfl⟩
  simpa using aux Finset.univ (e.symm x) (e.symm y) (by simp)

lemma coordinateSubgroups_generate (d : ℕ) (H : Subgroup (SymmetricGroup (2 ^ d)))
    (hH : ∀ i, coordinateSubgroup d i ≤ H) : H = ⊤ := by
  classical
  apply top_of_coordinate_swaps (positionsEquiv d) H
  intro i x a
  apply hH i
  apply swap_mem_fiberSubgroup
  funext j
  simp only [Equiv.symm_apply_apply]
  exact (Function.update_of_ne j.2 _ _).symm

def vectorStabilizer {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ G E) (x : E) : Subgroup G where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) x = x
    rw [map_mul, Module.End.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ g⁻¹ x = x
    have hh := congrArg (fun y => ρ g⁻¹ y) hg
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at hh
    exact hh.symm

lemma fixed_by_layers_fixed_by_all {d : ℕ} (lam : Partition (2 ^ d)) (x : Specht lam)
    (hx : ∀ i (g : coordinateSubgroup d i), spechtRepresentation lam g.1 x = x) :
    ∀ g, spechtRepresentation lam g x = x := by
  have ht := coordinateSubgroups_generate d (vectorStabilizer (spechtRepresentation lam) x)
    (fun i g hg => hx i ⟨g, hg⟩)
  intro g
  have hg : g ∈ vectorStabilizer (spechtRepresentation lam) x := ht ▸ Subgroup.mem_top _
  exact hg

end SignedSweeps
end

end OAI
