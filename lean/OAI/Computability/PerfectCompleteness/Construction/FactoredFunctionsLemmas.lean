import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

namespace OAI


namespace PerfectCompleteness.FactoredFunctions

variable {𝕜 Ω Z I J : Type*} [Field 𝕜]

def factoringSpace (other : Ω → Z) : Submodule 𝕜 (Ω → 𝕜) where
  carrier := {f | ∀ x y, other x = other y → f x = f y}
  zero_mem' := by intro x y _; rfl
  add_mem' := by
    intro f g hf hg x y h
    change f x + g x = f y + g y
    rw [hf x y h, hg x y h]
  smul_mem' := by
    intro c f hf x y h
    change c • f x = c • f y
    rw [hf x y h]

@[simp] theorem mem_factoringSpace (other : Ω → Z) (f : Ω → 𝕜) :
    f ∈ factoringSpace other ↔ ∀ x y, other x = other y → f x = f y := Iff.rfl

theorem mem_factoringSpace_iff_exists_factor (other : Ω → Z) (f : Ω → 𝕜) :
    f ∈ factoringSpace other ↔ ∃ g : Z → 𝕜, ∀ x, f x = g (other x) := by
  classical
  constructor
  · intro hf
    let g : Z → 𝕜 := fun z =>
      if h : ∃ x, other x = z then f (Classical.choose h) else 0
    refine ⟨g, ?_⟩
    intro x
    have hx : ∃ y, other y = other x := ⟨x, rfl⟩
    change f x = if h : ∃ y, other y = other x then f (Classical.choose h) else 0
    rw [dite_eq_left hx]
    exact hf x _ (Classical.choose_spec hx).symm
  · rintro ⟨g, hg⟩ x y h
    rw [hg x, hg y, h]

theorem const_mem_factoringSpace (other : Ω → Z) (c : 𝕜) :
    (fun _ : Ω => c) ∈ factoringSpace other := by
  intro x y _
  rfl

theorem one_mem_factoringSpace (other : Ω → Z) :
    (1 : Ω → 𝕜) ∈ factoringSpace other :=
  const_mem_factoringSpace other 1

theorem mul_mem_factoringSpace (other : Ω → Z) {f g : Ω → 𝕜}
    (hf : f ∈ factoringSpace other) (hg : g ∈ factoringSpace other) :
    f * g ∈ factoringSpace other := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y h, hg x y h]

theorem coordinate_mem_factoringSpace (lower : Ω → I → J → 𝕜) (i : I) (t : J) :
    (fun x => lower x i t) ∈ factoringSpace lower := by
  intro x y h
  exact congrFun (congrFun h i) t

def quadraticSpan (lower : Ω → I → J → 𝕜) : Submodule 𝕜 (Ω → 𝕜) :=
  Submodule.span 𝕜 {f | f = 1 ∨
    ∃ (i : I) (t u : J), f = fun x => lower x i t * lower x i u}

theorem one_mem_quadraticSpan (lower : Ω → I → J → 𝕜) :
    (1 : Ω → 𝕜) ∈ quadraticSpan lower :=
  Submodule.subset_span (Or.inl rfl)

theorem product_mem_quadraticSpan (lower : Ω → I → J → 𝕜) (i : I) (t u : J) :
    (fun x => lower x i t * lower x i u) ∈ quadraticSpan lower :=
  Submodule.subset_span (Or.inr ⟨i, t, u, rfl⟩)

theorem quadraticSpan_le_factoringSpace (lower : Ω → I → J → 𝕜) :
    quadraticSpan lower ≤ factoringSpace lower := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨i, t, u, rfl⟩
  · exact one_mem_factoringSpace lower
  · exact mul_mem_factoringSpace lower
      (coordinate_mem_factoringSpace lower i t) (coordinate_mem_factoringSpace lower i u)

noncomputable section

def realizer (other : Ω → Z) (z : Set.range other) : Ω :=
  Classical.choose z.property

theorem realizer_spec (other : Ω → Z) (z : Set.range other) :
    other (realizer other z) = z.val :=
  Classical.choose_spec z.property

def evaluation {other : Ω → Z} {B : Submodule 𝕜 (Ω → 𝕜)}
    (_hB : B ≤ factoringSpace other) (z : Set.range other) : B →ₗ[𝕜] 𝕜 :=
  (LinearMap.proj (realizer other z)).comp B.subtype

@[simp] theorem evaluation_apply {other : Ω → Z} {B : Submodule 𝕜 (Ω → 𝕜)}
    (hB : B ≤ factoringSpace other) (z : Set.range other) (b : B) :
    evaluation hB z b = b.val (realizer other z) := rfl

theorem evaluation_apply_of_eq {other : Ω → Z} {B : Submodule 𝕜 (Ω → 𝕜)}
    (hB : B ≤ factoringSpace other) (z : Set.range other) (x : Ω)
    (hx : other x = z.val) (b : B) : evaluation hB z b = b.val x :=
  hB b.property (realizer other z) x ((realizer_spec other z).trans hx.symm)

theorem evaluation_eq_pointEvaluation {other : Ω → Z} {B : Submodule 𝕜 (Ω → 𝕜)}
    (hB : B ≤ factoringSpace other) (z : Set.range other) (x : Ω)
    (hx : other x = z.val) :
    evaluation hB z = (LinearMap.proj x).comp B.subtype := by
  apply LinearMap.ext
  intro b
  exact evaluation_apply_of_eq hB z x hx b

@[simp] theorem evaluation_at_image {other : Ω → Z} {B : Submodule 𝕜 (Ω → 𝕜)}
    (hB : B ≤ factoringSpace other) (x : Ω) (b : B) :
    evaluation hB ⟨other x, ⟨x, rfl⟩⟩ b = b.val x :=
  evaluation_apply_of_eq hB _ x rfl b

theorem evaluation_one {other : Ω → Z} {B : Submodule 𝕜 (Ω → 𝕜)}
    (hB : B ≤ factoringSpace other) (z : Set.range other) (h1 : (1 : Ω → 𝕜) ∈ B) :
    evaluation hB z ⟨1, h1⟩ = 1 := rfl

end
end PerfectCompleteness.FactoredFunctions



namespace PerfectCompleteness.FactoredFunctionsDependent

open PerfectCompleteness.FactoredFunctions

variable {𝕜 Ω I : Type*} [Field 𝕜] {J : I → Type*}

theorem coordinate_mem_factoringSpace (lower : Ω → (i : I) → J i → 𝕜)
    (i : I) (t : J i) :
    (fun x => lower x i t) ∈ factoringSpace lower := by
  intro x y h
  exact congrFun (congrFun h i) t

def dependentQuadraticSpan (lower : Ω → (i : I) → J i → 𝕜) :
    Submodule 𝕜 (Ω → 𝕜) :=
  Submodule.span 𝕜 {f | f = 1 ∨
    ∃ (i : I) (t u : J i), f = fun x => lower x i t * lower x i u}

theorem one_mem_dependentQuadraticSpan (lower : Ω → (i : I) → J i → 𝕜) :
    (1 : Ω → 𝕜) ∈ dependentQuadraticSpan lower :=
  Submodule.subset_span (Or.inl rfl)

theorem product_mem_dependentQuadraticSpan (lower : Ω → (i : I) → J i → 𝕜)
    (i : I) (t u : J i) :
    (fun x => lower x i t * lower x i u) ∈ dependentQuadraticSpan lower :=
  Submodule.subset_span (Or.inr ⟨i, t, u, rfl⟩)

theorem dependentQuadraticSpan_le_factoringSpace (lower : Ω → (i : I) → J i → 𝕜) :
    dependentQuadraticSpan lower ≤ factoringSpace lower := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨i, t, u, rfl⟩
  · exact one_mem_factoringSpace lower
  · exact mul_mem_factoringSpace lower
      (coordinate_mem_factoringSpace lower i t) (coordinate_mem_factoringSpace lower i u)

end PerfectCompleteness.FactoredFunctionsDependent

end OAI
