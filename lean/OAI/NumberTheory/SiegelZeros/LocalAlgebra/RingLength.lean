import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Length

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W24

section Modules

variable {R M P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

def filtrationRestriction (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n) (n : ℕ) : F n →ₗ[R] G n :=
  (f.domRestrict (F n)).codRestrict (G n) (fun x => hf n x x.property)

def filtrationLayerMap (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n) (n : ℕ) :
    (F n ⧸ (F (n + 1)).comap (F n).subtype) →ₗ[R]
      (G n ⧸ (G (n + 1)).comap (G n).subtype) :=
  Submodule.mapQ _ _ (filtrationRestriction f F G hf n) (by
    intro x hx
    exact hf (n + 1) x hx)

theorem correction_of_layer_surjective (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n) (n : ℕ)
    (hs : Function.Surjective (filtrationLayerMap f F G hf n))
    (y : P) (hy : y ∈ G n) :
    ∃ x ∈ F n, y - f x ∈ G (n + 1) := by
  obtain ⟨z, hz⟩ := hs (Submodule.Quotient.mk (⟨y, hy⟩ : G n))
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
  have hdiffLayer : filtrationRestriction f F G hf n x - (⟨y, hy⟩ : G n) ∈
      (G (n + 1)).comap (G n).subtype :=
    (Submodule.Quotient.eq ((G (n + 1)).comap (G n).subtype)).mp hz
  have hdiff : f x - y ∈ G (n + 1) := hdiffLayer
  exact ⟨x, x.property, by simpa only [neg_sub] using (G (n + 1)).neg_mem hdiff⟩

theorem surjective_of_finite_corrections (f : M →ₗ[R] P)
    (G : ℕ → Submodule R P) (d : ℕ) (hzero : G 0 = ⊤) (hend : G d = ⊥)
    (hstep : ∀ n < d, ∀ y ∈ G n, ∃ x : M, y - f x ∈ G (n + 1)) :
    Function.Surjective f := by
  intro y
  have hlift : ∀ n, n ≤ d → ∃ x : M, y - f x ∈ G n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨0, by simp [hzero]⟩
    | succ n ih =>
      intro hn
      obtain ⟨x, hx⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨z, hz⟩ := hstep n (Nat.lt_of_succ_le hn) (y - f x) hx
      exact ⟨x + z, by simpa only [map_add, sub_add_eq_sub_sub] using hz⟩
  obtain ⟨x, hx⟩ := hlift d le_rfl
  rw [hend, Submodule.mem_bot] at hx
  exact ⟨x, (sub_eq_zero.mp hx).symm⟩

theorem surjective_of_finite_layers (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n)
    (d : ℕ) (hzero : G 0 = ⊤) (hend : G d = ⊥)
    (hs : ∀ n < d, Function.Surjective (filtrationLayerMap f F G hf n)) :
    Function.Surjective f := by
  apply surjective_of_finite_corrections f G d hzero hend
  intro n hn y hy
  obtain ⟨x, _, hx⟩ := correction_of_layer_surjective f F G hf n (hs n hn) y hy
  exact ⟨x, hx⟩

theorem length_le_of_finite_layers (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n)
    (d : ℕ) (hzero : G 0 = ⊤) (hend : G d = ⊥)
    (hs : ∀ n < d, Function.Surjective (filtrationLayerMap f F G hf n)) :
    Module.length R P ≤ Module.length R M :=
  Module.length_le_of_surjective f
    (surjective_of_finite_layers f F G hf d hzero hend hs)

end Modules

section ResidueScalars

variable {A : Type*} [CommRing A]

theorem scalar_lift_difference (I : Ideal A) (n : ℕ) {a b x : A}
    (hab : a - b ∈ I) (hx : x ∈ I ^ n) :
    a * x - b * x ∈ I ^ (n + 1) := by
  rw [← sub_mul, pow_succ']
  exact Ideal.mul_mem_mul hab hx

end ResidueScalars

end WeightedTorusJets.W24

end

section

namespace WeightedTorusJets.W24

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem ring_length_le_of_finite_layers
    (F : ℕ → Submodule A A) (G : ℕ → Submodule A B)
    (hf : ∀ n, ∀ x ∈ F n, algebraMap A B x ∈ G n)
    (d : ℕ) (hzero : G 0 = ⊤) (hend : G d = ⊥)
    (hs : ∀ n < d, Function.Surjective
      (filtrationLayerMap (Algebra.linearMap A B) F G hf n)) :
    Module.length B B ≤ Module.length A A := by
  have hsurj : Function.Surjective (algebraMap A B) :=
    surjective_of_finite_layers (Algebra.linearMap A B) F G hf d hzero hend hs
  rw [← Module.length_eq_of_surjective (M := B) hsurj]
  exact Module.length_le_of_surjective (Algebra.linearMap A B) hsurj

end WeightedTorusJets.W24

end

end SiegelZeros

end OAI
