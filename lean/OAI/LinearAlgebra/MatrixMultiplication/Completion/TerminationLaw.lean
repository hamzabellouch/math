import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Entropy
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.IndependentConditioning

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionTerminationLaw

open MatrixMultiplication.Foundation CompletionLabels CompletionColorLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

theorem retained_mass_one (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    eventMass (colorMix S first second pf ps a ha ha')
      (fun w => leafColor S w = first ∨ leafColor S w = second) = 1 := by
  rw [eventMass, sum_subtype_indicator]
  calc
    _ = ∑ w, (colorMix S first second pf ps a ha ha').mass w := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs with h
      · rfl
      · exact (colorMix_mass_zero S first second pf ps a ha ha' w
          (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))).symm
    _ = _ := (colorMix S first second pf ps a ha ha').total

def retainedEquiv (S : FlaggedTensor X Y Z) (first second : Color) :
    {w : Leaf S // leafColor S w = first ∨ leafColor S w = second} ≃
      RetainedLeaf S first second := Equiv.refl _

theorem retained_sum (S : FlaggedTensor X Y Z) (first second : Color) (f : Leaf S → ℝ) :
    (∑ w : RetainedLeaf S first second, f w.val) =
      ∑ w : {w : Leaf S // leafColor S w = first ∨ leafColor S w = second}, f w.val := by
  exact ((retainedEquiv S first second).sum_comp
    (fun w : RetainedLeaf S first second => f w.val)).symm

def law (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    FiniteLaw (RetainedLeaf S first second) where
  mass w := (colorMix S first second pf ps a ha ha').mass w.val
  nonneg w := (colorMix S first second pf ps a ha ha').nonneg w.val
  total := by
    rw [retained_sum]
    exact retained_mass_one S first second pf ps a ha ha'

theorem law_mass (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (w : RetainedLeaf S first second) :
    (law S first second pf ps a ha ha').mass w =
      (colorMix S first second pf ps a ha ha').mass w.val := rfl

theorem law_map_mass {U : Type*} [Fintype U]
    (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) (f : Leaf S → U) (u : U) :
    ((law S first second pf ps a ha ha').map (fun w => f w.val)).mass u =
      ((colorMix S first second pf ps a ha ha').map f).mass u := by
  rw [FiniteLaw.map_mass]
  simp only [law_mass]
  rw [retained_sum S first second
    (fun w => if f w = u then (colorMix S first second pf ps a ha ha').mass w else 0)]
  rw [sum_subtype_indicator (fun w : Leaf S =>
    leafColor S w = first ∨ leafColor S w = second)
    (fun w => if f w = u then (colorMix S first second pf ps a ha ha').mass w else 0)]
  rw [FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : leafColor S w = first ∨ leafColor S w = second
  · simp [h]
  · have hz := colorMix_mass_zero S first second pf ps a ha ha' w
      (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))
    simp [h, hz]

theorem law_entropy (S : FlaggedTensor X Y Z) (first second : Color)
    (hne : first ≠ second)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    finiteEntropy (law S first second pf ps a ha ha').mass =
      entropyTerm a + entropyTerm (1 - a) +
        a * finiteEntropy pf.mass + (1 - a) * finiteEntropy ps.mass := by
  have hmap : ((law S first second pf ps a ha ha').map Subtype.val).mass =
      (colorMix S first second pf ps a ha ha').mass := by
    funext w
    exact (law_map_mass S first second pf ps a ha ha' id w).trans
      ((colorMix S first second pf ps a ha ha').map_mass_apply id Function.injective_id w)
  rw [← (law S first second pf ps a ha ha').map_entropy_of_injective
    Subtype.val Subtype.val_injective, hmap]
  exact colorMix_entropy S first second hne pf ps a ha ha'

end MatrixMultiplication.CompletionTerminationLaw

end

end OAI
