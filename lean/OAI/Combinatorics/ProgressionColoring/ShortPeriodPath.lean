import OAI.Combinatorics.ProgressionColoring.ShortPeriodLift

namespace OAI

/-!
# Short-period lifting from a rational return path

When the return period divides the dilation, the rational rotation contributes
an integer in every coordinate. The remaining real step is the dilated return
error divided by the period. This connects the actual rational-path identity
to the centered affine lift.
-/

namespace QuantitativeVanDerWaerden

/-- Divisibility of the dilation kills the integer numerator of a rational
return path modulo one. The resulting step is congruent to the actual cyclic
step; the integer witness follows by comparing the two path identities at
index one. -/
theorem rational_path_short_step_congr {q D dilation h : ℕ} (hq : 0 < q)
    (n d : CyclicGroup q D) (t : Fin D → ℤ) (u : Fin D → ℝ)
    (hh : 0 < h) (hdiv : h ∣ dilation)
    (hpath : ∀ (j : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D dilation (n + j • d) i - yRep q D dilation n i -
        (j : ℝ) / h * ((dilation : ℝ) * ((t i : ℝ) + u i)) = z) :
    ∀ i, ∃ z : ℤ,
      yRep q D dilation d i - (dilation : ℝ) * u i / h = z := by
  obtain ⟨c, hc⟩ := hdiv
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hcR : (dilation : ℝ) = (h : ℝ) * (c : ℝ) := by exact_mod_cast hc
  intro i
  obtain ⟨z₁, h₁⟩ := hpath 1 i
  obtain ⟨z₂, h₂⟩ := yRep_ap_congr hq dilation n d 1 i
  simp only [Nat.cast_one, one_mul] at h₁ h₂
  have hrotation : (1 / (h : ℝ)) * ((dilation : ℝ) * ((t i : ℝ) + u i)) -
      (dilation : ℝ) * u i / h = (c : ℝ) * (t i : ℝ) := by
    rw [hcR]
    field_simp [hhR]
    ring
  refine ⟨(c : ℤ) * t i + z₁ - z₂, ?_⟩
  push_cast
  linarith

/-- The short-period affine lift with its step congruence supplied by the
actual rational return path. The numerator need not satisfy additional
primitivity or range hypotheses for this branch. -/
theorem AdaptiveMesh.short_period_path_lift (M : AdaptiveMesh)
    {q D dilation h k a b : ℕ} (hq : 0 < q)
    (n d : CyclicGroup q D) (t : Fin D → ℤ) (u : Fin D → ℝ)
    (hh : 0 < h) (hdiv : h ∣ dilation)
    (hpath : ∀ (j : ℕ) (i : Fin D), ∃ z : ℤ,
      yRep q D dilation (n + j • d) i - yRep q D dilation n i -
        (j : ℝ) / h * ((dilation : ℝ) * ((t i : ℝ) + u i)) = z)
    (halpha : M.alpha ≤ 1 / (q : ℝ) ^ D)
    (hmotion : ∀ i, (k : ℝ) * |(dilation : ℝ) * u i / h| < 1 / 2)
    (hsmall : 2 * M.H * ((k : ℝ) + 1) < 1)
    (hab : a ≠ b) (hak : a < k) (hbk : b < k)
    (hsame : ∀ i, M.meshLabel (yRep q D dilation (n + a • d) i) =
      M.meshLabel (yRep q D dilation (n + b • d) i)) :
    ∀ j, j < k → yRep q D dilation (n + j • d) =
      fun i => yRep q D dilation n i +
        (j : ℝ) * ((dilation : ℝ) * u i / h) := by
  exact M.short_period_cyclic_lift hq n d
    (fun i => (dilation : ℝ) * u i / h)
    (rational_path_short_step_congr hq n d t u hh hdiv hpath)
    halpha hmotion hsmall hab hak hbk hsame

end QuantitativeVanDerWaerden

end OAI
