import OAI.Computability.StarHeight.Recognition

namespace OAI

namespace GeneralizedStarHeight

universe u

theorem main {Alphabet : Type u} [Finite Alphabet] (L : Language Alphabet) (hL : L.IsRegular) :
    HasHeightAtMost L 3 := by
  classical
  rcases isEmpty_or_nonempty Alphabet with h|h
  · let : IsEmpty Alphabet := h
    apply HasHeightAtMost.finite L _ 3
    apply (Set.finite_singleton ([] : List Alphabet)).subset
    intro w _
    cases w with
    | nil => rfl
    | cons a w => exact isEmptyElim a
  · let : Nonempty Alphabet := h
    obtain ⟨M,hM,hfin,T,F,hTF⟩ := FiniteRecognition.of_regular hL
    let : Monoid M := hM
    let : Fintype M := hfin
    have heq : L=({w | T (FreeMonoid.ofList w)∈F} : Language Alphabet) := by
      ext w
      exact hTF w
    rw [heq]
    exact FiniteRecognition.recognized_height_three T F

end GeneralizedStarHeight

end OAI
