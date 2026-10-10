import Mathlib

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
open scoped TensorProduct

namespace ReverseLogKodaira.LocalCanonical

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K]

abbrev Canonical (n : ℕ) := ⋀[A]^n (KaehlerDifferential R A)
abbrev Pluricanonical (n m : ℕ) := ⨂[A] (_ : Fin m), Canonical R A n

 
def alternatingRestriction (n : ℕ) :
    (KaehlerDifferential R K) [⋀^Fin n]→ₗ[A] Canonical R K n where
  toMultilinearMap := (exteriorPower.ιMulti K n).toMultilinearMap.restrictScalars A
  map_eq_zero_of_eq' := (exteriorPower.ιMulti K n).map_eq_zero_of_eq

 
def exteriorPullback (n : ℕ) : Canonical R A n →ₗ[A] Canonical R K n :=
  exteriorPower.alternatingMapLinearEquiv
    ((alternatingRestriction R A K n).compLinearMap (KaehlerDifferential.map R R A K))

 
def pluricanonicalPullback (n m : ℕ) :
    Pluricanonical R A n m →ₗ[A] Pluricanonical R K n m :=
  PiTensorProduct.lift (((PiTensorProduct.tprod K).restrictScalars A).compLinearMap
    fun _ : Fin m => exteriorPullback R A K n)

lemma span_wedges (n : ℕ) :
    Submodule.span A (Set.range fun a : Fin n → A =>
      exteriorPower.ιMulti A n fun i => KaehlerDifferential.D R A (a i)) = ⊤ := by
  have h := exteriorPower.ιMulti_span_of_span A n (KaehlerDifferential R A)
    (KaehlerDifferential.span_range_derivation R A)
  convert h using 2
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨fun i => KaehlerDifferential.D R A (a i), by
      rintro _ ⟨i, rfl⟩; exact ⟨a i, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' : ∀ i, ∃ a, KaehlerDifferential.D R A a = v i :=
      fun i => hv ⟨i, rfl⟩
    choose a ha using hv'
    exact ⟨a, congrArg (exteriorPower.ιMulti A n) (funext ha)⟩

lemma exteriorPullback_wedge (n : ℕ) (a : Fin n → A) :
    exteriorPullback R A K n (exteriorPower.ιMulti A n
      fun i => KaehlerDifferential.D R A (a i)) =
      exteriorPower.ιMulti K n fun i =>
        KaehlerDifferential.D R K (algebraMap A K (a i)) := by
  simp [exteriorPullback, alternatingRestriction]
  rfl

 

theorem range_pluricanonicalPullback (n m : ℕ) :
    LinearMap.range (pluricanonicalPullback R A K n m) =
      Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
        PiTensorProduct.tprod K fun j => exteriorPower.ιMulti K n fun i =>
          KaehlerDifferential.D R K (algebraMap A K (a j i))) := by
  have ht : Submodule.span A (Set.range fun a : Fin m → Fin n → A =>
      PiTensorProduct.tprod A fun j => exteriorPower.ιMulti A n fun i =>
        KaehlerDifferential.D R A (a j i)) = ⊤ :=
    PiTensorProduct.submodule_span_eq_top (R := A)
      (M := fun _ : Fin m => Canonical R A n) (γ := fun _ => Fin n → A)
      (g := fun {i} a => exteriorPower.ιMulti A n fun j => KaehlerDifferential.D R A (a j))
      (fun _ => span_wedges R A n)
  rw [LinearMap.range_eq_map, ← ht, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    simp [pluricanonicalPullback, exteriorPullback_wedge]
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨a, rfl⟩, ?_⟩
    simp [pluricanonicalPullback, exteriorPullback_wedge]

end ReverseLogKodaira.LocalCanonical

end
end

end OAI
