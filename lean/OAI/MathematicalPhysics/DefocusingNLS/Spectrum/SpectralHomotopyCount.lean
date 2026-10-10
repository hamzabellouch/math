import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHomotopyContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleHomotopyCount

namespace OAI

/-! # Conditional transport of the spectral zero count -/

namespace DefocusingNLS

/-- The certified zero-free boundary and joint continuity transport the actual
analytic zero count from the zero tail to the outgoing endpoint. The only
conditional input is the published rectangle case of Rouché's theorem. -/
theorem exists_spectral_rectangle_homotopy_count (hR : RectangleRouche) (ell : Fin 4) :
    ∃ V : ℝ, 0 < V ∧ ∀ b Z : ℝ,
      |100000000 * b - 33477607| ≤ 2 → |100000000 * Z - 270506819| ≤ 2 →
      rectangleZeroCount V (spectralHomotopyDeterminant ell b Z 0) =
        rectangleZeroCount V (spectralHomotopyDeterminant ell b Z 1) := by
  obtain ⟨V, hV, he⟩ := exists_spectral_counting_boundary ell
  refine ⟨V + 1, by linarith, ?_⟩
  intro b Z hb hZ
  have hZ0 : Z ≠ 0 := by
    intro h
    norm_num [h] at hZ
  apply rectangleZeroCount_homotopy hR (V + 1) (by linarith)
  · intro a ha z hz
    exact analyticAt_spectralHomotopyDeterminant ell b Z a z hZ0 hz.1
  · intro a ha z hz
    exact continuousAt_joint_spectralHomotopyDeterminant ell b Z a z hZ0 hz.1.1
  · intro a ha z hz
    apply he b Z a z hb hZ ha.1 ha.2
    rcases (mem_countingRectangleBoundary_iff (V + 1) z).mp hz with ⟨hrect, hedge⟩
    rcases hedge with hleft | hright | hbottom | htop
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright.ge)
    · right; right
      exact ⟨hrect.1, by rw [hbottom, abs_neg, abs_of_pos (by linarith)]; linarith⟩
    · right; right
      exact ⟨hrect.1, by rw [htop, abs_of_pos (by linarith)]; linarith⟩

end DefocusingNLS

end OAI
