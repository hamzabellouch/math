import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {X : Type*}

def vanishingSubspace (D : Submodule ℝ (X → ℝ)) (F : Set X) : Submodule ℝ D where
  carrier := {u | ∀ x∈F, (u:X → ℝ) x=0}
  zero_mem' := by intro x hx; rfl
  add_mem' := by intro u v hu hv x hx; change u.val x+v.val x=0; rw [hu x hx,hv x hx,add_zero]
  smul_mem' := by intro a u hu x hx; change a*u.val x=0; rw [hu x hx,mul_zero]

lemma vanishingSubspace_antitone (D : Submodule ℝ (X → ℝ)) :
    Antitone (vanishingSubspace D) := by
  intro s t h u hu x hx
  exact hu x (h hx)

theorem exists_detecting_ball (F : ℕ → Set X) (hmono : Monotone F)
    (hex : ∀ x, ∃ n, x∈F n) (D : Submodule ℝ (X → ℝ))
    [FiniteDimensional ℝ D] :
    ∃ n, ∀ u : D, (∀ x∈F n, (u:X → ℝ) x=0) → u=0 := by
  let K : ℕ →o (Submodule ℝ D)ᵒᵈ :=
    ⟨fun n => vanishingSubspace D (F n),
      fun m n h => vanishingSubspace_antitone D (hmono h)⟩
  obtain ⟨n,hn⟩ := IsArtinian.monotone_stabilizes K
  refine ⟨n,?_⟩
  intro u hu
  apply Subtype.ext
  funext x
  obtain ⟨m,hm⟩ := hex x
  have he : vanishingSubspace D (F n)=vanishingSubspace D (F (max n m)) :=
    hn (max n m) (le_max_left _ _)
  have hum : u∈vanishingSubspace D (F (max n m)) := he ▸ hu
  exact hum x (hmono (le_max_right _ _) hm)

def squareMass (F : Finset X) (u : X → ℝ) : ℝ := ∑ x∈F, (u x)^2

lemma squareMass_nonneg (F : Finset X) (u : X → ℝ) : 0≤ squareMass F u :=
  Finset.sum_nonneg (fun vertex _ => sq_nonneg (u vertex))

lemma squareMass_eq_zero_iff (F : Finset X) (u : X → ℝ) :
    squareMass F u=0 ↔ ∀ x∈F, u x=0 := by
  rw [squareMass,Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (u x))]
  simp only [sq_eq_zero_iff]

lemma squareMass_mono {F H : Finset X} (h : F⊆H) (u : X → ℝ) :
    squareMass F u≤ squareMass H u :=
  Finset.sum_le_sum_of_subset_of_nonneg h (by intros; positivity)

lemma squareMass_pos (D : Submodule ℝ (X → ℝ)) (F : Finset X)
    (hF : ∀ u : D, (∀ x∈F, (u:X → ℝ) x=0) → u=0) (u : D) (hu : u≠0) :
    0<squareMass F u := by
  apply lt_of_le_of_ne (squareMass_nonneg _ _)
  intro hz
  exact hu (hF u ((squareMass_eq_zero_iff _ _).mp hz.symm))

end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
