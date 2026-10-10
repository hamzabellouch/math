import OAI.Algebra.Finitistic.Rectification.SourceFiltration
import OAI.Algebra.Finitistic.Localization.SplitComponentExact

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
instance zeroTermSubsingleton (n : ℤ) : Subsingleton ((Z (k := k) (B := B)).X n) := by
  change Subsingleton PUnit
  infer_instance

variable (t : AssemblyData (C := BiComplex k B) (A := A) (J := J) (R := R))
variable (h : Homotopy (t.q ≫ t.p) 0)
variable (hh : ∀ i j, h.hom i j ≫ (biprod.fst : t.L₀ ⟶ t.V₀).f j = 0)

theorem source0_component0 (n : ℤ) :
    Function.Injective ((include1 t h).f₀.f n) ∧
    Function.Exact ((include1 t h).f₀.f n) ((quotient0 t h hh).f₀.f n) ∧
    Function.Surjective ((quotient0 t h hh).f₀.f n) :=
  inr_fst_shortExact t.V₀ (t.V₁ ⊞ t.V₂) n

theorem source0_component1 (n : ℤ) :
    Function.Injective ((include1 t h).f₁.f n) ∧
    Function.Exact ((include1 t h).f₁.f n) ((quotient0 t h hh).f₁.f n) ∧
    Function.Surjective ((quotient0 t h hh).f₁.f n) :=
  inr_fst_shortExact (⨁ t.U) (⨁ t.V) n

theorem source0_component2 (n : ℤ) :
    Function.Injective ((include1 t h).f₂.f n) ∧
    Function.Exact ((include1 t h).f₂.f n) ((quotient0 t h hh).f₂.f n) ∧
    Function.Surjective ((quotient0 t h hh).f₂.f n) :=
  zero_id_shortExact t.L₂ Z (fun _ => inferInstance) n

/-- The actual F>=1 inclusion and source-zero quotient are termwise short exact. -/
theorem source0_shortExact (n : ℤ) :
    Function.Injective ((include1 t h).totalMap.f n) ∧
    Function.Exact ((include1 t h).totalMap.f n) ((quotient0 t h hh).totalMap.f n) ∧
    Function.Surjective ((quotient0 t h hh).totalMap.f n) := by
  exact (include1 t h).totalMap_shortExact (quotient0 t h hh)
    (fun n => (source0_component0 t h hh n).2.1)
    (fun n => (source0_component1 t h hh n).2.1)
    (fun n => (source0_component2 t h hh n).2.1)
    (fun n => (source0_component0 t h hh n).1)
    (fun n => (source0_component1 t h hh n).1)
    (fun n => (source0_component2 t h hh n).1)
    (fun n => (source0_component0 t h hh n).2.2)
    (fun n => (source0_component1 t h hh n).2.2)
    (fun n => (source0_component2 t h hh n).2.2) n

omit [Fintype R] in
theorem source1_component0 (n : ℤ) :
    Function.Injective ((include2 t).f₀.f n) ∧
    Function.Exact ((include2 t).f₀.f n) ((quotient1 t).f₀.f n) ∧
    Function.Surjective ((quotient1 t).f₀.f n) :=
  inr_fst_shortExact t.V₁ t.V₂ n

omit [Fintype R] in
theorem source1_component1 (n : ℤ) :
    Function.Injective ((include2 t).f₁.f n) ∧
    Function.Exact ((include2 t).f₁.f n) ((quotient1 t).f₁.f n) ∧
    Function.Surjective ((quotient1 t).f₁.f n) :=
  zero_id_shortExact (⨁ t.V) Z (fun _ => inferInstance) n

omit [Fintype R] in
theorem source1_component2 (n : ℤ) :
    Function.Injective ((include2 t).f₂.f n) ∧
    Function.Exact ((include2 t).f₂.f n) ((quotient1 t).f₂.f n) ∧
    Function.Surjective ((quotient1 t).f₂.f n) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun x => ⟨x, rfl⟩⟩
  intro x
  exact ⟨fun _ => ⟨x, rfl⟩, fun _ => Subsingleton.elim _ _⟩

omit [Fintype R] in
/-- The actual F>=2 inclusion and source-one quotient are termwise short exact. -/
theorem source1_shortExact (n : ℤ) :
    Function.Injective ((include2 t).totalMap.f n) ∧
    Function.Exact ((include2 t).totalMap.f n) ((quotient1 t).totalMap.f n) ∧
    Function.Surjective ((quotient1 t).totalMap.f n) := by
  exact (include2 t).totalMap_shortExact (quotient1 t)
    (fun n => (source1_component0 t n).2.1)
    (fun n => (source1_component1 t n).2.1)
    (fun n => (source1_component2 t n).2.1)
    (fun n => (source1_component0 t n).1)
    (fun n => (source1_component1 t n).1)
    (fun n => (source1_component2 t n).1)
    (fun n => (source1_component0 t n).2.2)
    (fun n => (source1_component1 t n).2.2)
    (fun n => (source1_component2 t n).2.2) n

variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

/-- No short-exactness or filtration assumption: all component properties are
proved from the actual induced Section 4 sources. -/
theorem induced_source0_shortExact (n : ℤ) :
    Function.Injective ((inducedInclude1 s D₀ D₁ D₂ f g H).totalMap.f n) ∧
    Function.Exact ((inducedInclude1 s D₀ D₁ D₂ f g H).totalMap.f n)
      ((inducedQuotient0 s D₀ D₁ D₂ f g H).totalMap.f n) ∧
    Function.Surjective ((inducedQuotient0 s D₀ D₁ D₂ f g H).totalMap.f n) :=
  source0_shortExact _ _ _ n
end ExternalTensor.Section4.SourceFiltration

end

end OAI
