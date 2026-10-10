import OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginGeometry

namespace OAI

/-! The support of four simultaneous short windows has size `O(X H³)`. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_origin_interval_card (c H : ℕ) :
    (Icc (c - H) (c + 2 * H)).card ≤ 3 * H + 1 := by
  rw [Nat.card_Icc]
  omega

/-- Only the first origin costs `X`; each of the other three origins
costs at most `3H+1`, independently of the prime quadruple. -/
theorem minor_arc_origin_quadruples (X H A B C D : ℕ) (hA : 0 < A)
    (hB : B ≤ 2 * A) (hC : C ≤ 2 * A) (hD : D ≤ 2 * A)
    (T : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hT : ∀ v ∈ T, v.1.1 < X ∧ ∃ m : ℕ,
      (v.1.1 < A * m ∧ A * m ≤ v.1.1 + H) ∧
      (v.1.2 < B * m ∧ B * m ≤ v.1.2 + H) ∧
      (v.2.1 < C * m ∧ C * m ≤ v.2.1 + H) ∧
      (v.2.2 < D * m ∧ D * m ≤ v.2.2 + H)) :
    T.card ≤ X * (3 * H + 1) ^ 3 := by
  let box := fun k =>
    ({k} ×ˢ Icc ((B * k) / A - H) ((B * k) / A + 2 * H)) ×ˢ
      (Icc ((C * k) / A - H) ((C * k) / A + 2 * H) ×ˢ
        Icc ((D * k) / A - H) ((D * k) / A + 2 * H))
  have hsub : T ⊆ (range X).biUnion box := by
    rintro ⟨⟨k, l⟩, ⟨r, s⟩⟩ hv
    obtain ⟨hkX, m, hk, hl, hr, hs⟩ := hT _ hv
    apply mem_biUnion.mpr
    refine ⟨k, mem_range.mpr hkX, ?_⟩
    dsimp [box]
    simp only [mem_product, mem_singleton, mem_Icc]
    exact ⟨⟨True.intro, minor_arc_origin_bounds A B H k l m hA hB hk hl⟩,
      minor_arc_origin_bounds A C H k r m hA hC hk hr,
      minor_arc_origin_bounds A D H k s m hA hD hk hs⟩
  have hbox (k : ℕ) : (box k).card ≤ (3 * H + 1) ^ 3 := by
    dsimp [box]
    simp only [card_product, card_singleton, one_mul]
    have h₁ := minor_arc_origin_interval_card ((B * k) / A) H
    have h₂ := minor_arc_origin_interval_card ((C * k) / A) H
    have h₃ := minor_arc_origin_interval_card ((D * k) / A) H
    calc
      _ ≤ (3 * H + 1) * ((3 * H + 1) * (3 * H + 1)) :=
        Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂ h₃)
      _ = _ := by ring
  calc
    T.card ≤ ((range X).biUnion box).card := card_le_card hsub
    _ ≤ ∑ k ∈ range X, (box k).card := card_biUnion_le
    _ ≤ ∑ _k ∈ range X, (3 * H + 1) ^ 3 := sum_le_sum (fun k _ => hbox k)
    _ = X * (3 * H + 1) ^ 3 := by simp

end TwoPointCorrelations

end OAI
