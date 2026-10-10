import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation

namespace OAI

/-! Restricting either algebra preserves scalar freeness. -/

namespace KadisonSimilarity
variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  {τ : A →ₗ[ℂ] ℂ} {P Q P' Q' : StarSubalgebra ℂ A}

theorem AlternatingCenteredWord.mono (hP : P ≤ P') (hQ : Q ≤ Q')
    {side : Bool} {xs : List A} (h : AlternatingCenteredWord τ P Q side xs) :
    AlternatingCenteredWord τ P' Q' side xs := by
  induction h with
  | nil side => exact .nil side
  | @cons side x xs hm hz _ ih =>
    refine .cons ?_ hz ih
    cases side
    · exact hQ hm
    · exact hP hm

theorem ScalarFree.mono (hf : ScalarFree τ P' Q') (hP : P ≤ P') (hQ : Q ≤ Q') :
    ScalarFree τ P Q := by
  intro side x xs h
  exact hf side x xs (h.mono hP hQ)

end KadisonSimilarity

end OAI
