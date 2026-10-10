import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HorizontalContinuity

namespace OAI

/-! # A uniform positive neighborhood at inverse frequency zero -/

open Filter Topology Set Metric

namespace DefocusingNLS

noncomputable def horizontalParameterBox (R b₀ b₁ Z₀ Z₁ : ℝ) : Set HorizontalParameters :=
  Icc (-(1 / 32 : ℝ)) R ×ˢ Icc b₀ b₁ ×ˢ Icc Z₀ Z₁ ×ˢ sphere (0 : ℂ × ℂ) 1

theorem isCompact_horizontalParameterBox (R b₀ b₁ Z₀ Z₁ : ℝ) :
    IsCompact (horizontalParameterBox R b₀ b₁ Z₀ Z₁) :=
  isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_sphere _ _)))

theorem horizontalParameterBox_nonzero {R b₀ b₁ Z₀ Z₁ : ℝ} {p : HorizontalParameters}
    (hp : p ∈ horizontalParameterBox R b₀ b₁ Z₀ Z₁) :
    p.2.2.2.1 ≠ 0 ∨ p.2.2.2.2 ≠ 0 := by
  by_contra h
  push Not at h
  have hz : p.2.2.2 = (0 : ℂ × ℂ) := Prod.ext h.1 h.2
  have hs := hp.2.2.2
  rw [mem_sphere, hz, dist_self] at hs
  norm_num at hs

/-- One inverse-frequency neighborhood works for the full parameter box and
all unit initial vectors. The estimate is symmetric in positive/negative frequency. -/
theorem exists_horizontal_positive_neighborhood (ell : ℕ) (R b₀ b₁ Z₀ Z₁ : ℝ)
    (hZ : 0 < Z₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : ℝ, |τ| < ε →
      ∀ p ∈ horizontalParameterBox R b₀ b₁ Z₀ Z₁, 0 < horizontalFormAt ell (τ, p) := by
  have hev := eventually_horizontalForm_positive ell
    (horizontalParameterBox R b₀ b₁ Z₀ Z₁)
    (isCompact_horizontalParameterBox R b₀ b₁ Z₀ Z₁)
    (fun p hp => hp.1.1)
    (fun p hp => ne_of_gt (lt_of_lt_of_le hZ hp.2.2.1.1))
    (fun p hp => horizontalParameterBox_nonzero hp)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε, hε, fun τ hτ => he ?_⟩
  simpa only [Real.dist_eq, sub_zero] using hτ

end DefocusingNLS

end OAI
