import OAI.Analysis.PureInfiniteness.FiniteFamilyAbelianization

namespace OAI

/-! Polynomial conditions encoding fixation and pairwise commutation. -/

noncomputable section

namespace WeakPureInfiniteness

abbrev AbelianizationRelation := ℕ ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℕ))

def abelianizationHeight : AbelianizationRelation → ℕ
  | .inl i => i
  | .inr (.inl (i, j)) => max i j
  | .inr (.inr (i, j)) => max i j

variable {D E : Type*} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E]

def abelianizationRelation (a b : ℕ → D) (v : D) : AbelianizationRelation → D
  | .inl i => star v * a i * v - a i
  | .inr (.inl (i, j)) => a i * (star v * b j * v) - (star v * b j * v) * a i
  | .inr (.inr (i, j)) => (star v * b i * v) * (star v * b j * v) -
      (star v * b j * v) * (star v * b i * v)

lemma map_abelianizationRelation (φ : D →⋆ₙₐ[ℂ] E) (a b : ℕ → D) (v : D)
    (j : AbelianizationRelation) :
    φ (abelianizationRelation a b v j) =
      abelianizationRelation (fun i => φ (a i)) (fun i => φ (b i)) (φ v) j := by
  rcases j with i | (⟨i, j⟩ | ⟨i, j⟩) <;>
    simp only [abelianizationRelation, map_sub, map_mul, map_star]

lemma abelianizationRelation_eq_zero_of_finite (a b : ℕ → D) (v : D) (m : ℕ)
    (hfix : ∀ i : Fin (m + 1), star v * a i * v = a i)
    (hcomm : ∀ i j : Fin (m + 1), Commute (a i) (star v * b j * v))
    (hpair : ∀ i j : Fin (m + 1), Commute (star v * b i * v) (star v * b j * v))
    (j : AbelianizationRelation) (hj : abelianizationHeight j ≤ m) :
    abelianizationRelation a b v j = 0 := by
  rcases j with i | (⟨i, j⟩ | ⟨i, j⟩)
  · exact sub_eq_zero.mpr (hfix ⟨i, by change i ≤ m at hj; omega⟩)
  · have hi : i < m + 1 := by change max i j ≤ m at hj; omega
    have hj' : j < m + 1 := by change max i j ≤ m at hj; omega
    exact sub_eq_zero.mpr (hcomm ⟨i, hi⟩ ⟨j, hj'⟩).eq
  · have hi : i < m + 1 := by change max i j ≤ m at hj; omega
    have hj' : j < m + 1 := by change max i j ≤ m at hj; omega
    exact sub_eq_zero.mpr (hpair ⟨i, hi⟩ ⟨j, hj'⟩).eq

end WeakPureInfiniteness

end

end OAI
