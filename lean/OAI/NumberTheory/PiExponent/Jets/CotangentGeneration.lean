import Mathlib
import OAI.NumberTheory.PiExponent.Jets.GradedGeneration

namespace OAI

namespace PiExponentJets.W24

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

theorem corrections_of_mapCotangent_surjective (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf)) :
    ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2 := by
  intro y hy
  obtain ⟨z, hz⟩ := hs (J.toCotangent ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  rw [Ideal.mapCotangent_toCotangent] at hz
  have he : f x - y ∈ J ^ 2 := J.toCotangent_eq.mp hz
  exact ⟨x, x.property, by simpa only [neg_sub] using (J ^ 2).neg_mem he⟩

theorem algHom_surjective_of_residue_cotangent
    {K : Type*} [CommRing K] (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (ρ : A →+* K) (π : B →+* K) (hρ : Function.Surjective ρ)
    (hcomm : π.comp f.toRingHom = ρ) (hJ : J = RingHom.ker π)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf))
    (d : ℕ) (hd : J ^ d = ⊥) : Function.Surjective f := by
  have hres : ∀ y : B, ∃ x : A, y - f x ∈ J := by
    rw [hJ]
    exact residue_corrections_of_surjective f.toRingHom ρ π hρ hcomm
  have hcor := ideal_power_corrections f.toRingHom I J hf hres
    (corrections_of_mapCotangent_surjective I J f hf hs)
  let : Algebra A B := f.toRingHom.toAlgebra
  apply surjective_of_finite_corrections (Algebra.linearMap A B)
    (fun n => (J ^ n).restrictScalars A) d
  · simp
  · simp [hd]
  · intro n _ y hy
    obtain ⟨x, _, hx⟩ := hcor n y hy
    exact ⟨x, hx⟩

theorem length_le_of_residue_cotangent_map
    {K : Type*} [CommRing K] (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (ρ : A →+* K) (π : B →+* K) (hρ : Function.Surjective ρ)
    (hcomm : π.comp f.toRingHom = ρ) (hJ : J = RingHom.ker π)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf))
    (d : ℕ) (hd : J ^ d = ⊥) : Module.length B B ≤ Module.length A A := by
  have hsurj := algHom_surjective_of_residue_cotangent I J f hf ρ π hρ hcomm hJ hs d hd
  let : Algebra A B := f.toRingHom.toAlgebra
  have hsurj' : Function.Surjective (algebraMap A B) := hsurj
  rw [← Module.length_eq_of_surjective (M := B) hsurj']
  exact Module.length_le_of_surjective (Algebra.linearMap A B) hsurj'

end PiExponentJets.W24

end OAI
