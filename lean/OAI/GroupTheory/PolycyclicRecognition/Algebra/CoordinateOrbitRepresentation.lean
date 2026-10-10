import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Linearizing a group through its translated coordinate functions

Right translates of separating coordinates span a faithful representation.
A uniform finite-dimensional space containing those translates makes the
representation finite dimensional; polynomial multiplication will supply it.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G I : Type*} [Group G] (q : I → G → ℝ)

def rightTranslateLinear (g : G) : (G → ℝ) →ₗ[ℝ] (G → ℝ) where
  toFun f x := f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinateOrbitSpan : Submodule ℝ (G → ℝ) :=
  Submodule.span ℝ (Set.range (fun p : G × I => fun x => q p.2 (x * p.1)))

theorem coordinate_mem_orbitSpan (i : I) : q i ∈ coordinateOrbitSpan q := by
  apply Submodule.subset_span
  refine ⟨(1, i), ?_⟩
  funext x
  exact congrArg (q i) (mul_one x)

theorem rightTranslate_mem_coordinateOrbitSpan (g : G) {f : G → ℝ}
    (hf : f ∈ coordinateOrbitSpan q) :
    rightTranslateLinear g f ∈ coordinateOrbitSpan q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    funext x
    exact congrArg (q i) (mul_assoc x g h).symm
  | zero => exact (coordinateOrbitSpan q).zero_mem
  | add f h _ _ hf hh => exact (coordinateOrbitSpan q).add_mem hf hh
  | smul a f _ hf => exact (coordinateOrbitSpan q).smul_mem a hf

def coordinateOrbitRepresentation : Representation ℝ G (coordinateOrbitSpan q) where
  toFun g :=
    { toFun f := ⟨rightTranslateLinear g f, rightTranslate_mem_coordinateOrbitSpan q g f.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    exact congrArg (f : G → ℝ) (mul_one x)
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    exact congrArg (f : G → ℝ) (mul_assoc x g h).symm

@[simp] theorem coordinateOrbitRepresentation_apply (g : G)
    (f : coordinateOrbitSpan q) (x : G) :
    (coordinateOrbitRepresentation q g f : G → ℝ) x = (f : G → ℝ) (x * g) := rfl

theorem coordinateOrbitRepresentation_injective
    (hq : Function.Injective (fun g : G => fun i : I => q i g)) :
    Function.Injective (coordinateOrbitRepresentation q) := by
  intro g h he
  apply hq
  funext i
  let f : coordinateOrbitSpan q := ⟨q i, coordinate_mem_orbitSpan q i⟩
  have hf := congrArg (fun A : Module.End ℝ (coordinateOrbitSpan q) =>
    (A f : G → ℝ) 1) he
  simpa only [coordinateOrbitRepresentation_apply, one_mul] using hf

theorem finiteDimensional_coordinateOrbitSpan {J : Type*} [Finite J]
    (b : J → G → ℝ)
    (hb : ∀ (g : G) (i : I), (fun x => q i (x * g)) ∈ Submodule.span ℝ (Set.range b)) :
    FiniteDimensional ℝ (coordinateOrbitSpan q) := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ (Set.range b))
  apply Submodule.span_le.mpr
  rintro f ⟨⟨g, i⟩, rfl⟩
  exact hb g i

end PolycyclicRecognition

end

end OAI
