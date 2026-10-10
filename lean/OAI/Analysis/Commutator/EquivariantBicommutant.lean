import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.EquivariantBicommutant

variable {A B : Type*} [Monoid A] [Monoid B]

lemma mem_centralizer_image (e : A ≃* B) (s : Set A) (x : A) :
    e x∈Set.centralizer (e '' s) ↔ x∈Set.centralizer s := by
  constructor
  · intro h y hy
    apply e.injective
    simpa only [map_mul] using h (e y) ⟨y,hy,rfl⟩
  · rintro h _ ⟨y,hy,rfl⟩
    simpa only [map_mul] using congrArg e (h y hy)

lemma centralizer_image (e : A ≃* B) (s : Set A) :
    Set.centralizer (e '' s)=e '' Set.centralizer s := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    apply (mem_centralizer_image e s (e.symm x)).mp
    simpa only [e.apply_symm_apply] using hx
  · rintro ⟨y,hy,rfl⟩
    exact (mem_centralizer_image e s y).mpr hy

lemma bicommutant_image (e : A ≃* B) (s : Set A) :
    Set.centralizer (Set.centralizer (e '' s))=e '' Set.centralizer (Set.centralizer s) := by
  rw [centralizer_image,centralizer_image]

lemma bicommutant_range {C : Type*} (e : A ≃* B) (f : C → A)
    (hf : Set.centralizer (Set.centralizer (Set.range f))=Set.range f) :
    Set.centralizer (Set.centralizer (Set.range (e ∘ f)))=Set.range (e ∘ f) := by
  rw [Set.range_comp,bicommutant_image,hf]

lemma bicommutant_mono {s t : Set A} (h : s⊆t) :
    Set.centralizer (Set.centralizer s)⊆Set.centralizer (Set.centralizer t) := by
  intro x hx y hy
  exact hx y (fun z hz => hy z (h hz))

end Kadison.EquivariantBicommutant

end

end
end

end OAI
