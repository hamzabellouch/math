import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ParameterBoxHomotopy
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.OutgoingHalfPlaneCount

namespace OAI

/-! # Certified outgoing determinant counts throughout the parameter box -/

open Set

namespace DefocusingNLS

attribute [local irreducible] spectralHomotopyDeterminant spectralSlowDeterminant

/-- Tail homotopy transport works in every sufficiently tall counting rectangle,
uniformly over the certified real parameter box. -/
theorem exists_spectral_rectangle_homotopy_count_above (hR : RectangleRouche)
    (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ W : ℝ, V < W → ∀ b Z : ℝ,
      |100000000 * b - 33477607| ≤ 2 → |100000000 * Z - 270506819| ≤ 2 →
      rectangleZeroCount W (spectralHomotopyDeterminant ell b Z 0) =
        rectangleZeroCount W (spectralHomotopyDeterminant ell b Z 1) := by
  obtain ⟨V, hV, he⟩ := exists_spectral_counting_boundary ell
  refine ⟨V, hV, ?_⟩
  intro W hW b Z hb hZ
  have hZ0 : Z ≠ 0 := by intro h; norm_num [h] at hZ
  apply rectangleZeroCount_homotopy hR W (hV.trans hW)
  · intro a ha z hz
    exact analyticAt_spectralHomotopyDeterminant ell b Z a z hZ0 hz.1
  · intro a ha z hz
    exact continuousAt_joint_spectralHomotopyDeterminant ell b Z a z hZ0 hz.1.1
  · intro a ha z hz
    apply he b Z a z hb hZ ha.1 ha.2
    rcases (mem_countingRectangleBoundary_iff W z).mp hz with ⟨hrect, hedge⟩
    rcases hedge with hleft | hright | hbottom | htop
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright.ge)
    · exact Or.inr (Or.inr ⟨hrect.1, by
        rw [hbottom, abs_neg, abs_of_pos (hV.trans hW)]
        exact hW⟩)
    · exact Or.inr (Or.inr ⟨hrect.1, by
        rw [htop, abs_of_pos (hV.trans hW)]
        exact hW⟩)

/-- The full outgoing determinant count is 2, 1, 0, 0 for every parameter pair
in the manuscript's certified box. The only hypothesis is the precisely cited
rectangle specialization of the published Rouché theorem. -/
theorem outgoing_halfPlane_count (hR : RectangleRouche) (ell : Fin 4)
    (b Z : ℝ) (hb : |100000000 * b - 33477607| ≤ 2)
    (hZ : |100000000 * Z - 270506819| ≤ 2) :
    countingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z) =
      (SeparatorArithmetic.positiveRootCount ell : ℕ∞) := by
  obtain ⟨V₁, hV₁, hfull⟩ := exists_countingHalfPlaneZeroCount_eq_rectangle ell
  obtain ⟨V₂, hV₂, hzero⟩ := SeparatorArithmetic.exists_central_zeroTail_rectangle_count ell
  obtain ⟨V₃, hV₃, hpar⟩ := exists_zeroTail_parameter_count hR ell
  obtain ⟨V₄, hV₄, htail⟩ := exists_spectral_rectangle_homotopy_count_above hR ell
  let W := max (max V₁ V₂) (max V₃ V₄) + 1
  have hW₁ : V₁ < W := by
    dsimp [W]
    linarith [le_max_left V₁ V₂, le_max_left (max V₁ V₂) (max V₃ V₄)]
  have hW₂ : V₂ < W := by
    dsimp [W]
    linarith [le_max_right V₁ V₂, le_max_left (max V₁ V₂) (max V₃ V₄)]
  have hW₃ : V₃ < W := by
    dsimp [W]
    linarith [le_max_left V₃ V₄, le_max_right (max V₁ V₂) (max V₃ V₄)]
  have hW₄ : V₄ < W := by
    dsimp [W]
    linarith [le_max_right V₃ V₄, le_max_right (max V₁ V₂) (max V₃ V₄)]
  have hZ0 : Z ≠ 0 := by intro h; norm_num [h] at hZ
  have hc : rectangleZeroCount W (spectralHomotopyDeterminant ell b Z 0) =
      (SeparatorArithmetic.positiveRootCount ell : ℕ∞) :=
    (hpar W hW₃ b Z hb hZ).symm.trans (hzero W hW₂)
  calc
    countingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z) =
        rectangleZeroCount W (spectralSlowDeterminant ell b Z) := hfull W hW₁ b Z hb hZ
    _ = rectangleZeroCount W (spectralHomotopyDeterminant ell b Z 1) :=
      (rectangleZeroCount_spectralHomotopy_endpoint ell b Z W hZ0).symm
    _ = rectangleZeroCount W (spectralHomotopyDeterminant ell b Z 0) :=
      (htail W hW₄ b Z hb hZ).symm
    _ = (SeparatorArithmetic.positiveRootCount ell : ℕ∞) := hc

end DefocusingNLS

end OAI
