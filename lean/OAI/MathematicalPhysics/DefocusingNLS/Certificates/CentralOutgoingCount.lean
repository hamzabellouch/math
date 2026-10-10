import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CentralZeroTailCount

namespace OAI

/-! # Conditional numerical outgoing counts at the certified central parameters -/

namespace DefocusingNLS

/-- The actual outgoing determinant has the certified count, with multiplicity,
in every sufficiently tall rectangle. Only the published rectangle Rouché
proposition is assumed. -/
theorem exists_central_outgoing_rectangle_count (hR : RectangleRouche) (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ W : ℝ, V < W →
      rectangleZeroCount W
        (spectralSlowDeterminant ell (33477607 / 100000000) (270506819 / 100000000)) =
          (SeparatorArithmetic.positiveRootCount ell : ℕ∞) := by
  obtain ⟨V₁, hV₁, hb⟩ := exists_spectral_counting_boundary ell
  obtain ⟨V₂, hV₂, hz⟩ := SeparatorArithmetic.exists_central_zeroTail_rectangle_count ell
  refine ⟨max V₁ V₂, lt_of_lt_of_le hV₁ (le_max_left _ _), ?_⟩
  intro W hW
  have hW₁ : V₁ < W := lt_of_le_of_lt (le_max_left _ _) hW
  have hW₂ : V₂ < W := lt_of_le_of_lt (le_max_right _ _) hW
  have hW0 : 0 < W := hV₁.trans hW₁
  have hZ : (270506819 / 100000000 : ℝ) ≠ 0 := by norm_num
  have he : rectangleZeroCount W
      (spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000) 0) =
      rectangleZeroCount W
      (spectralHomotopyDeterminant ell (33477607 / 100000000) (270506819 / 100000000) 1) := by
    apply rectangleZeroCount_homotopy hR W hW0
    · intro a ha z hz
      exact analyticAt_spectralHomotopyDeterminant ell _ _ a z hZ hz.1
    · intro a ha z hz
      exact continuousAt_joint_spectralHomotopyDeterminant ell _ _ a z hZ hz.1.1
    · intro a ha z hz
      apply hb (33477607 / 100000000) (270506819 / 100000000) a z
        (by norm_num) (by norm_num) ha.1 ha.2
      obtain ⟨hrect, hedge⟩ := (mem_countingRectangleBoundary_iff W z).mp hz
      rcases hedge with hleft | hright | hbottom | htop
      · exact Or.inl hleft
      · exact Or.inr (Or.inl hright.ge)
      · exact Or.inr (Or.inr ⟨hrect.1, by
          rw [hbottom, abs_neg, abs_of_pos hW0]
          exact hW₁⟩)
      · exact Or.inr (Or.inr ⟨hrect.1, by
          rw [htop, abs_of_pos hW0]
          exact hW₁⟩)
  exact (he.trans (rectangleZeroCount_spectralHomotopy_endpoint ell _ _ W hZ)).symm.trans
    (hz W hW₂)

end DefocusingNLS

end OAI
