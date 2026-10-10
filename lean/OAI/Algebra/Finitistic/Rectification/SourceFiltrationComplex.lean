import OAI.Algebra.Finitistic.Rectification.FiltrationExactness
import OAI.Algebra.Finitistic.Bimodule.BimoduleVertex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.ModuleComplexExact
universe u
variable {S : Type u} [Ring S]
variable {X Y Z : CochainComplex (ModuleCat.{u} S) ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem comp_zero (h : ∀ n, Function.Exact (f.f n) (g.f n)) : f ≫ g = 0 := by
  ext n x
  exact (h n).apply_apply_eq_zero x

def sequence (h : ∀ n, Function.Exact (f.f n) (g.f n)) :
    ShortComplex (CochainComplex (ModuleCat.{u} S) ℤ) := .mk f g (comp_zero f g h)

theorem shortExact (h : ∀ n, Function.Injective (f.f n) ∧
    Function.Exact (f.f n) (g.f n) ∧ Function.Surjective (g.f n)) :
    (sequence f g (fun n => (h n).2.1)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact ModuleCat.shortComplex_shortExact _ (h n).2.1 (h n).1 (h n).2.2
end LittleFinitistic.ModuleComplexExact

namespace ExternalTensor.Section4.SourceFiltration.Complex
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {A J R : Type} [Fintype A] [Fintype J] [Fintype R]
variable (s : Quadratic k B (A := A) (J := J) (R := R))
variable (D₀ D₁ D₂ : RightComplex B)
variable (f : A → (D₀ ⟶ D₁)) (g : J → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap s D₀ D₁ D₂ f g r) 0)
open Exactness LittleFinitistic

def source0 := ModuleComplexExact.sequence (i1 s D₀ D₁ D₂ f g H)
  (pi0 s D₀ D₁ D₂ f g H)
  (fun n => (exact_source_filtration s D₀ D₁ D₂ f g H n).1.2.1)

def source1 := ModuleComplexExact.sequence (i2 s D₀ D₁ D₂ f g)
  (pi1 s D₀ D₁ D₂ f g)
  (fun n => (v2_shortExact (data s D₀ D₁ D₂ f g) n).2.1)

theorem source0_shortExact : (source0 s D₀ D₁ D₂ f g H).ShortExact :=
  ModuleComplexExact.shortExact _ _
    (fun n => (exact_source_filtration s D₀ D₁ D₂ f g H n).1)

omit [Fintype R] in
theorem source1_shortExact : (source1 s D₀ D₁ D₂ f g).ShortExact :=
  ModuleComplexExact.shortExact _ _ (v2_shortExact (data s D₀ D₁ D₂ f g))

/-- Every original source filtration remains short exact after taking a left vertex. -/
theorem vertex_shortExact (e : B) (he : e*e=e)
    (S : ShortComplex (BiComplex k B)) (hS : S.ShortExact) :
    (S.map ((BimoduleVertex.functor k B e).mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact BimoduleVertex.map_shortExact k B e he
    (S.map (HomologicalComplex.eval _ _ n))
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n)
end ExternalTensor.Section4.SourceFiltration.Complex

end

end OAI
