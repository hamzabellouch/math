import OAI.Analysis.Nuclearity.CommutingMatrixPositive

namespace OAI

/-! Positivity on algebraic tensor squares for a completely positive map
whose range commutes with a representation of the second factor. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {B C E I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [NonUnitalCStarAlgebra E] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder E] [StarOrderedRing E] [Fintype I] [DecidableEq I]

lemma cstar_finite_gram_nonneg (b : I → B) :
    0 ≤ (CStarMatrix.ofMatrix (fun i j => star (b i) * b j) : CStarMatrix I I B) := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    have he : (CStarMatrix.ofMatrix (fun i j => star (b i) * b j) : CStarMatrix I I B) = 0 := by
      ext i
      exact h.false i |>.elim
    rw [he]
  | inr h =>
    let i₀ : I := Classical.choice h
    let V : CStarMatrix I I B := CStarMatrix.ofMatrix (fun i j => if i = i₀ then b j else 0)
    have he : star V * V = CStarMatrix.ofMatrix (fun i j => star (b i) * b j) := by
      ext i j
      change (∑ k, star (if k = i₀ then b i else 0) * (if k = i₀ then b j else 0)) =
        star (b i) * b j
      simp
    rw [← he]
    exact star_mul_self_nonneg V

theorem commuting_cp_gram_nonneg (f : B →L[ℂ] E) (hf : CompletelyPositive f)
    (η : C →⋆ₙₐ[ℂ] E) (hc : ∀ b c, Commute (f b) (η c)) (b : I → B) (c : I → C) :
    0 ≤ ∑ i, ∑ j, f (star (b i) * b j) * η (star (c i) * c j) := by
  let Y := matrixLinearMap f (CStarMatrix.ofMatrix (fun i j => star (b i) * b j))
  have hY : 0 ≤ Y := matrixLinearMap_nonneg hf (cstar_finite_gram_nonneg b)
  have hp := matrix_quadratic_nonneg Y hY (fun i => η (c i))
  have he (i j : I) : f (star (b i) * b j) * η (star (c i) * c j) =
      star (η (c i)) * Y i j * η (c j) := by
    change f (star (b i) * b j) * η (star (c i) * c j) =
      star (η (c i)) * f (star (b i) * b j) * η (c j)
    rw [map_mul η, ← map_star η, ← mul_assoc, (hc _ (star (c i))).eq]
  simpa only [he] using hp

end WeakPureInfiniteness

end

end OAI
