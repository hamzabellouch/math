import OAI.Algebra.Finitistic.Rectification.SourceFiltrationCone

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open LittleFinitistic.RectificationTotal
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.SourceFiltration.Exactness
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)

abbrev data := inducedData s D₀ D₁ D₂ f g
abbrev P := total (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
  (nullHomotopy s D₀ D₁ D₂ f g H)
abbrev F1 := total (p1 (data s D₀ D₁ D₂ f g)) 0 (h1 (data s D₀ D₁ D₂ f g))
abbrev G0 := total (p0 (data s D₀ D₁ D₂ f g)) (q0 (data s D₀ D₁ D₂ f g))
  (h0 (data s D₀ D₁ D₂ f g))
abbrev G1 := total (pGrade1 (data s D₀ D₁ D₂ f g)) 0
  (hGrade1 (data s D₀ D₁ D₂ f g))

abbrev i1 : F1 s D₀ D₁ D₂ f g ⟶ P s D₀ D₁ D₂ f g H :=
  (inducedInclude1 s D₀ D₁ D₂ f g H).totalMap
abbrev pi0 : P s D₀ D₁ D₂ f g H ⟶ G0 s D₀ D₁ D₂ f g :=
  (inducedQuotient0 s D₀ D₁ D₂ f g H).totalMap
abbrev i2 : (columnComplex k B s.e₂).obj D₂ ⟶ F1 s D₀ D₁ D₂ f g :=
  v2Inclusion (data s D₀ D₁ D₂ f g)
abbrev pi1 : F1 s D₀ D₁ D₂ f g ⟶ G1 s D₀ D₁ D₂ f g :=
  (quotient1 (data s D₀ D₁ D₂ f g)).totalMap

/-- Section 4's actual two nontrivial source-filtration steps. No decomposition,
exactness, extra coherence, vertex equivalence, or main theorem is an input. -/
theorem exact_source_filtration (n : ℤ) :
    (Function.Injective ((i1 s D₀ D₁ D₂ f g H).f n) ∧
     Function.Exact ((i1 s D₀ D₁ D₂ f g H).f n) ((pi0 s D₀ D₁ D₂ f g H).f n) ∧
     Function.Surjective ((pi0 s D₀ D₁ D₂ f g H).f n)) ∧
    (Function.Injective ((i2 s D₀ D₁ D₂ f g).f n) ∧
     Function.Exact ((i2 s D₀ D₁ D₂ f g).f n) ((pi1 s D₀ D₁ D₂ f g).f n) ∧
     Function.Surjective ((pi1 s D₀ D₁ D₂ f g).f n)) ∧
    i2 s D₀ D₁ D₂ f g ≫ i1 s D₀ D₁ D₂ f g H =
      (data s D₀ D₁ D₂ f g).in₂ ≫
        inclusion (p s D₀ D₁ D₂ f g) (q s D₀ D₁ D₂ f g)
          (nullHomotopy s D₀ D₁ D₂ f g H) :=
  ⟨induced_source0_shortExact s D₀ D₁ D₂ f g H n,
   v2_shortExact (data s D₀ D₁ D₂ f g) n,
   v2_nested (data s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)⟩

theorem categorical_source0 (n : ℤ) :
    let E := (exact_source_filtration s D₀ D₁ D₂ f g H n).1
    (ModuleCat.shortComplexOfCompEqZero ((i1 s D₀ D₁ D₂ f g H).f n).hom
      ((pi0 s D₀ D₁ D₂ f g H).f n).hom E.2.1.linearMap_comp_eq_zero).ShortExact := by
  let E := (exact_source_filtration s D₀ D₁ D₂ f g H n).1
  exact ModuleCat.shortComplex_shortExact _ E.2.1 E.1 E.2.2

omit [Fintype R] in
theorem categorical_source1 (n : ℤ) :
    let E := v2_shortExact (data s D₀ D₁ D₂ f g) n
    (ModuleCat.shortComplexOfCompEqZero ((i2 s D₀ D₁ D₂ f g).f n).hom
      ((pi1 s D₀ D₁ D₂ f g).f n).hom E.2.1.linearMap_comp_eq_zero).ShortExact := by
  let E := v2_shortExact (data s D₀ D₁ D₂ f g) n
  exact ModuleCat.shortComplex_shortExact _ E.2.1 E.1 E.2.2
end ExternalTensor.Section4.SourceFiltration.Exactness

end

end OAI
