import OAI.MathematicalPhysics.DefocusingNLS.Certificates.CentralOutgoingCount

namespace OAI

/-! # Numerical outgoing counts in the full counting half-plane -/

open Set

namespace DefocusingNLS

noncomputable def countingHalfPlaneZeroCount (f : ℂ → ℂ) : ℕ∞ :=
  ∑' z : {z : ℂ | -(1 / 32 : ℝ) < z.re}, analyticOrderAt f z.1

theorem countingHalfPlaneZeroCount_eq_rectangle (f : ℂ → ℂ) (V : ℝ)
    (hn : ∀ z : ℂ, -(1 / 32 : ℝ) < z.re → z ∉ countingRectangle V → f z ≠ 0) :
    countingHalfPlaneZeroCount f = rectangleZeroCount V f := by
  classical
  unfold countingHalfPlaneZeroCount rectangleZeroCount
  rw [tsum_subtype, tsum_subtype]
  apply tsum_congr
  intro z
  by_cases hz : z ∈ countingRectangle V
  · have hr : -(1 / 32 : ℝ) < z.re := hz.1
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hz, ite_eq_left hr]
  · by_cases hr : -(1 / 32 : ℝ) < z.re
    · have ho : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hn z hr hz))
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hz, ite_eq_left hr, ho]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hz, ite_eq_right hr]

theorem spectralSlowDeterminant_ne_zero_of_endpoint (ell : ℕ) (b Z : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re)
    (hn : spectralHomotopyDeterminant ell b Z 1 z ≠ 0) :
    spectralSlowDeterminant ell b Z z ≠ 0 := by
  intro h
  exact hn (by rw [spectralHomotopy_endpoint_factor ell b Z z hZ hz, h, mul_zero])

theorem exists_countingHalfPlaneZeroCount_eq_rectangle (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ W : ℝ, V < W → ∀ b Z : ℝ,
      |100000000 * b - 33477607| ≤ 2 → |100000000 * Z - 270506819| ≤ 2 →
      countingHalfPlaneZeroCount (spectralSlowDeterminant ell b Z) =
        rectangleZeroCount W (spectralSlowDeterminant ell b Z) := by
  obtain ⟨V, hV, hb⟩ := exists_spectral_counting_boundary ell
  refine ⟨V, hV, ?_⟩
  intro W hW b Z hb0 hZ0
  have hZ : Z ≠ 0 := by intro h; norm_num [h] at hZ0
  apply countingHalfPlaneZeroCount_eq_rectangle
  intro z hz hnrect
  apply spectralSlowDeterminant_ne_zero_of_endpoint ell b Z z hZ hz.le
  apply hb b Z 1 z hb0 hZ0 (by norm_num) le_rfl
  by_cases hright : 8 ≤ z.re
  · exact Or.inr (Or.inl hright)
  · have hRe : z.re < 8 := lt_of_not_ge hright
    have hheight : W ≤ |z.im| := by
      by_contra h
      have hlt : |z.im| < W := lt_of_not_ge h
      exact hnrect ⟨hz, hRe, (abs_lt.mp hlt).1, (abs_lt.mp hlt).2⟩
    exact Or.inr (Or.inr ⟨hz.le, hW.trans_le hheight⟩)

/-- The central outgoing determinant has zero count 2, 1, 0, 0 in
the half-plane Re(z)>-1/32, conditional only on Ahlfors's Rouché corollary. -/
theorem central_outgoing_halfPlane_count (hR : RectangleRouche) (ell : Fin 4) :
    countingHalfPlaneZeroCount
      (spectralSlowDeterminant ell (33477607 / 100000000) (270506819 / 100000000)) =
        (SeparatorArithmetic.positiveRootCount ell : ℕ∞) := by
  obtain ⟨V₁, hV₁, hc⟩ := exists_countingHalfPlaneZeroCount_eq_rectangle ell
  obtain ⟨V₂, hV₂, hn⟩ := exists_central_outgoing_rectangle_count hR ell
  let W := max V₁ V₂ + 1
  have hW₁ : V₁ < W := by dsimp [W]; linarith [le_max_left V₁ V₂]
  have hW₂ : V₂ < W := by dsimp [W]; linarith [le_max_right V₁ V₂]
  exact (hc W hW₁ _ _ (by norm_num) (by norm_num)).trans (hn W hW₂)

end DefocusingNLS

end OAI
