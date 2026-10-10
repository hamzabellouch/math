import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeLeadingWords

namespace OAI

/-! The complement of the words starting in one factor consists exactly of
the nonempty words starting in the other factor. -/

noncomputable section
namespace KadisonSimilarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem orthogonal_eq_of_dense_sup (S T : ClosedSubmodule ℂ E)
    (ho : ∀ (x : S) (y : T), inner ℂ (x : E) (y : E) = 0)
    (hd : (S.toSubmodule ⊔ T.toSubmodule).topologicalClosure = ⊤) :
    S.toSubmoduleᗮ = T.toSubmodule := by
  apply le_antisymm
  · intro x hx
    let r := x - T.toSubmodule.starProjection x
    have hT : r ∈ T.toSubmoduleᗮ := T.toSubmodule.sub_starProjection_mem_orthogonal x
    have hp : T.toSubmodule.starProjection x ∈ S.toSubmoduleᗮ := by
      intro y hy
      exact ho ⟨y, hy⟩ ⟨_, T.toSubmodule.starProjection_apply_mem x⟩
    have hS : r ∈ S.toSubmoduleᗮ := S.toSubmoduleᗮ.sub_mem hx hp
    have hker : S.toSubmodule ⊔ T.toSubmodule ≤ (innerSL ℂ r).ker := by
      apply sup_le
      · intro y hy
        exact Submodule.inner_left_of_mem_orthogonal hy hS
      · intro y hy
        exact Submodule.inner_left_of_mem_orthogonal hy hT
    have hc := (S.toSubmodule ⊔ T.toSubmodule).topologicalClosure_minimal hker
      (innerSL ℂ r).isClosed_ker
    rw [hd] at hc
    have hz : r = 0 := inner_self_eq_zero.mp (hc (Submodule.mem_top : r ∈ (⊤ : Submodule ℂ E)))
    have he : x = T.toSubmodule.starProjection x := sub_eq_zero.mp hz
    rw [he]
    exact T.toSubmodule.starProjection_apply_mem x
  · intro y hy x hx
    exact ho ⟨x, hx⟩ ⟨y, hy⟩

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

theorem centeredFreeWordSpan_le_sides (side : Bool) :
    centeredFreeWordSpan G A D ≤ (centeredWordSpace G A D side).toSubmodule ⊔
      (leadingWordSpace G A D (!side)).toSubmodule := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, xs, hxs, rfl⟩
  by_cases h : s = side
  · subst s
    exact Submodule.mem_sup_left (closedFamilyVector (centeredWordFamily G A D side)
      ⟨xs, hxs⟩).property
  · have he : s = !side := by cases s <;> cases side <;> simp_all
    subst s
    by_cases hn : xs = []
    · subst xs
      exact Submodule.mem_sup_left (vacuum_mem_centeredWordSpace G A D side)
    · exact Submodule.mem_sup_right (closedFamilyVector (leadingWordFamily G A D (!side))
        ⟨⟨xs, hxs⟩, hn⟩).property

theorem centeredWordSpace_orthogonal (hτ : G.trace 1 = 1)
    (hf : ScalarFree G.trace A D) (hgen : ReducedWordGenerated G A D) (side : Bool) :
    (centeredWordSpace G A D side).toSubmoduleᗮ = (leadingWordSpace G A D (!side)).toSubmodule := by
  apply orthogonal_eq_of_dense_sup
  · intro x y
    cases side <;> exact inner_eq_zero_symm.mp (inner_leading_opposite_space G A D hf _ y x)
  · apply top_unique
    rw [← centeredFreeWordSpan_dense G A D hτ hgen]
    exact Submodule.topologicalClosure_mono (centeredFreeWordSpan_le_sides G A D side)

end KadisonSimilarity

end

end OAI
