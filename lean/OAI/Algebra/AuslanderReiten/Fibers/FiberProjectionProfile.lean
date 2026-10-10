import OAI.Algebra.AuslanderReiten.Homology.TriangleGradedSequence

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
include hT

theorem first_injective_of_previous_surjective (n : ℤ)
    (hs : Function.Surjective (second k T X n)) :
    Function.Injective (first k T X (n+1)) := by
  have hc : connecting k T X n = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x ∈ LinearMap.range (second k T X n) := hs x
    rw [exact_top k T X hT n] at hx
    exact hx
  rw [← LinearMap.ker_eq_bot, ← exact_next k T X hT n, hc, LinearMap.range_zero]

theorem first_surjective_of_top_subsingleton (n : ℤ) [Subsingleton (Top T X n)] :
    Function.Surjective (first k T X n) := by
  rw [← LinearMap.range_eq_top, exact_middle k T X hT n]
  apply top_unique
  intro x _
  exact Subsingleton.elim _ _

omit hT [Limits.HasZeroObject C] [Pretriangulated C] in

theorem second_surjective_of_top_subsingleton (n : ℤ) [Subsingleton (Top T X n)] :
    Function.Surjective (second k T X n) := by
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

theorem first_positive_bijective
    (hpos : ∀ n : ℤ, 0 < n → Subsingleton (Top T X n))
    (hs₀ : Function.Surjective (second k T X 0)) (n : ℤ) (hn : 0 < n) :
    Function.Bijective (first k T X n) := by
  constructor
  · have hs : Function.Surjective (second k T X (n-1)) := by
      by_cases h1 : n = 1
      · subst n
        exact hs₀
      · let := hpos (n-1) (by omega)
        exact second_surjective_of_top_subsingleton k T X (n-1)
    generalize hm : n - 1 = m at hs
    have he : n = m + 1 := by omega
    subst n
    exact first_injective_of_previous_surjective k T hT X m hs
  · let := hpos n hn
    exact first_surjective_of_top_subsingleton k T hT X n

def firstPositiveEquiv
    (hpos : ∀ n : ℤ, 0 < n → Subsingleton (Top T X n))
    (hs₀ : Function.Surjective (second k T X 0)) (n : ℤ) (hn : 0 < n) :
    Bottom T X n ≃ₗ[k] Middle T X n :=
  LinearEquiv.ofBijective (first k T X n) (first_positive_bijective k T hT X hpos hs₀ n hn)

theorem first_zero_injective [Subsingleton (Top T X (-1))] :
    Function.Injective (first k T X 0) := by
  have hinj := first_injective_of_previous_surjective k T hT X (-1)
    (second_surjective_of_top_subsingleton k T X (-1))
  exact hinj

end ArExplicit.TriangleGradedSequence

end

end OAI
