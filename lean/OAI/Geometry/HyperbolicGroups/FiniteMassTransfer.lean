import Mathlib

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A]

/-- Push a nonnegative mass along an actual finite map. -/
def pushMass (f : A → B) (weight : A → ℝ) (b : B) : ℝ :=
  ∑ a : A, if f a = b then weight a else 0

lemma pushMass_nonneg (f : A → B) (weight : A → ℝ) (hw : ∀ a, 0 ≤ weight a) :
    ∀ b, 0 ≤ pushMass f weight b := by
  classical
  intro b
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hw a
  · exact le_rfl

lemma pushMass_total [Fintype B] (f : A → B) (weight : A → ℝ) :
    ∑ b : B, pushMass f weight b = ∑ a : A, weight a := by
  classical
  unfold pushMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

lemma pushMass_sum (f : A → B) (weight : A → ℝ) (C : Finset B) :
    ∑ b ∈ C, pushMass f weight b =
      ∑ a ∈ Finset.univ.filter (fun a => f a ∈ C), weight a := by
  classical
  unfold pushMass
  rw [Finset.sum_comm,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

/-- If the image of a set lies in one dual component, its primal mass is
bounded by that component's pushed-forward mass, with no injectivity of
the assignment assumed or needed. -/
theorem mass_le_pushMass (f : A → B) (weight : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (U : Finset A) (C : Finset B) (hUC : ∀ a ∈ U, f a ∈ C) :
    ∑ a ∈ U, weight a ≤ ∑ b ∈ C, pushMass f weight b := by
  classical
  rw [pushMass_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hUC a ha⟩
  · exact fun a _ _ => hw a

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
