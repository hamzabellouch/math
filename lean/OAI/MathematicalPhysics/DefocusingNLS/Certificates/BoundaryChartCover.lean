import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEvenPolynomial

namespace OAI

/-! # The three positive half-line charts cover every squared frequency -/

namespace DefocusingNLS.BoundaryCertificate

theorem nonnegative_chart_cover (w : ℝ) (hw : 0 ≤ w) :
    (∃ t : ℝ, 0 ≤ t ∧ w = t / (1 + t)) ∨
    (∃ t : ℝ, 0 ≤ t ∧ w = (1 + 10 * t) / (1 + t)) ∨
    (∃ t : ℝ, 0 ≤ t ∧ w = 10 + t) := by
  by_cases h₁ : w < 1
  · left
    refine ⟨w / (1 - w), div_nonneg hw (by linarith), ?_⟩
    have hd : 1 - w ≠ 0 := by linarith
    have ht : 1 + w / (1 - w) ≠ 0 := by positivity
    field_simp
    ring
  · by_cases h₁₀ : w < 10
    · right; left
      refine ⟨(w - 1) / (10 - w), div_nonneg (by linarith) (by linarith), ?_⟩
      have hd : 10 - w ≠ 0 := by linarith
      have hq : 0 ≤ (w - 1) / (10 - w) := div_nonneg (by linarith) (by linarith)
      have ht : 1 + (w - 1) / (10 - w) ≠ 0 := by linarith
      field_simp
      ring
    · right; right
      exact ⟨w - 10, by linarith, by ring⟩

end DefocusingNLS.BoundaryCertificate

end OAI
