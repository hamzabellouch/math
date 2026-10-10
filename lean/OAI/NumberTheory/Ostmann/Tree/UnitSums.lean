import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_units_of_zero {A : Type*} [AddCommMonoid A] (f : F → A) (hf : f 0=0) :
    ∑ u : Fˣ, f u = ∑ x : F, f x := by
  have hu : (∑ u : Fˣ, f u) = ∑ x ∈ Finset.univ.erase (0:F), f x := by
    apply Finset.sum_bij (fun (u : Fˣ) _ => (u:F))
    · intro u _
      exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
    · intro u _ v _ h
      exact Units.ext h
    · intro x hx
      refine ⟨Units.mk0 x (Finset.ne_of_mem_erase hx), Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  rw [hu]
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0:F))
  simpa only [hf, add_zero] using h

theorem sum_units_add_zero {A : Type*} [AddCommMonoid A] (f : F → A) :
    (∑ u : Fˣ, f u) + f 0 = ∑ x : F, f x := by
  have hu : (∑ u : Fˣ, f u) = ∑ x ∈ Finset.univ.erase (0:F), f x := by
    apply Finset.sum_bij (fun (u : Fˣ) _ => (u:F))
    · intro u _
      exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
    · intro u _ v _ h
      exact Units.ext h
    · intro x hx
      refine ⟨Units.mk0 x (Finset.ne_of_mem_erase hx), Finset.mem_univ _, rfl⟩
    · intro _ _
      rfl
  rw [hu]
  exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0:F))

theorem sum_units_le (f : F → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ u : Fˣ, f u ≤ ∑ x : F, f x := by
  apply Finset.sum_le_sum_of_injOn (fun u : Fˣ => (u:F))
  · intro u _ v _ h
    exact Units.ext h
  · exact Finset.subset_univ _
  · intro _ _
    exact le_rfl
  · intro x _ _
    exact hf x

end
end Ostmann.FiniteField

end OAI
