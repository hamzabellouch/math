import Mathlib.LinearAlgebra.DFinsupp
import OAI.Computability.PerfectCompleteness.Algebra.UniformLinearImage
import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaces

namespace OAI


namespace PerfectCompleteness.UniformChildSum

open scoped BigOperators
open PointwiseSpaces RecursiveSpaces UniformLinearImage
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {𝕜 X J : Type*} [Field 𝕜] [Fintype J]
  {D : J → Type*}

def childSum (r : ∀ i, X → D i) (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) :
    (∀ i, squareSpace (H i)) →ₗ[𝕜] childSpace r H where
  toFun f := ⟨∑ i, pullback 𝕜 (r i) (f i),
    Submodule.sum_mem_iSup (fun i => Submodule.mem_map_of_mem (f i).property)⟩
  map_add' f g := by
    apply Subtype.ext
    simp only [Pi.add_apply, Submodule.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    simp only [Pi.smul_apply, Submodule.coe_smul, map_smul, Finset.smul_sum,
      RingHom.id_apply]

@[simp] theorem childSum_apply (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (f : ∀ i, squareSpace (H i)) :
    (childSum r H f).val = ∑ i, pullback 𝕜 (r i) (f i) := rfl

theorem childSum_surjective (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) : Function.Surjective (childSum r H) := by
  classical
  intro u
  let p : J → Submodule 𝕜 (X → 𝕜) :=
    fun i => (squareSpace (H i)).map (pullback 𝕜 (r i))
  have hu : (u : X → 𝕜) ∈ ⨆ i ∈ (Finset.univ : Finset J), p i := by
    simpa [p, childSpace] using u.property
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (s := Finset.univ) p (u : X → 𝕜)).mp hu
  have hx : ∀ i, ∃ w : squareSpace (H i),
      pullback 𝕜 (r i) (w : D i → 𝕜) = (v i : X → 𝕜) := by
    intro i
    obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp (v i).property
    exact ⟨⟨w, hw⟩, heq⟩
  choose w hw using hx
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change (∑ i, pullback 𝕜 (r i) (w i : D i → 𝕜)) = (u : X → 𝕜)
  calc
    _ = ∑ i, (v i : X → 𝕜) := Finset.sum_congr rfl (fun i _ => hw i)
    _ = _ := hv

theorem uniform_childSum [DecidableEq J] (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜))
    [∀ i, Fintype (squareSpace (H i))] [Fintype (childSpace r H)] :
    (FiniteProduct.law (fun i => FiniteDistribution.uniform (squareSpace (H i)))).pushforward
        (childSum r H) = FiniteDistribution.uniform (childSpace r H) :=
  product_uniform_linear_image (childSum r H) (childSum_surjective r H)


variable {branch : Nat → Nat} {n : Nat}

def recursiveSum (A : Slots branch (n + 1) → Type*) :
    (∀ i : Fin (branch n), squareSpace (space 𝕜 branch n (childFamily A i))) →ₗ[𝕜]
      space 𝕜 branch (n + 1) A :=
  childSum (childRestriction A) (fun i => space 𝕜 branch n (childFamily A i))

theorem recursiveSum_surjective (A : Slots branch (n + 1) → Type*) :
    Function.Surjective (recursiveSum (𝕜 := 𝕜) A) :=
  childSum_surjective (childRestriction A) (fun i => space 𝕜 branch n (childFamily A i))

theorem uniform_recursiveSum (A : Slots branch (n + 1) → Type*)
    [∀ i : Fin (branch n), Fintype (squareSpace (space 𝕜 branch n (childFamily A i)))]
    [Fintype (space 𝕜 branch (n + 1) A)] :
    (FiniteProduct.law (fun i : Fin (branch n) =>
      FiniteDistribution.uniform (squareSpace (space 𝕜 branch n (childFamily A i))))).pushforward
        (recursiveSum (𝕜 := 𝕜) A) = FiniteDistribution.uniform (space 𝕜 branch (n + 1) A) :=
  product_uniform_linear_image
    (I := Fin (branch n))
    (Ω := fun i => squareSpace (space 𝕜 branch n (childFamily A i)))
    (R := 𝕜) (V := space 𝕜 branch (n + 1) A)
    (recursiveSum (𝕜 := 𝕜) A) (recursiveSum_surjective (𝕜 := 𝕜) A)

end
end PerfectCompleteness.UniformChildSum

end OAI
