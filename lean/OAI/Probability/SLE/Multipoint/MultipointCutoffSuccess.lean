import OAI.Probability.SLE.Multipoint.MultipointLocalizedState

namespace OAI

/-! A successful path remains before the common localization boundary
once its finitely many completion prefixes have strict bounds. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

lemma LocalizedState.at_cutoff_eq_actual
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi M : ℝ} {H : ℝ≥0} {z : ι → ℂ} {τ : ι → Ω → ℝ≥0}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (S : LocalizedState B hm κ lo hi M H z τ γ G) (ω : Ω) (i : ι) :
    S.Q (S.χ ω) ω i =
      logLoewnerCoordinates (G ω) (z i) (min (τ i ω) (S.χ ω) : ℝ≥0) := by
  have ha := (S.actual ω i).2
    (show ((min (τ i ω) (S.χ ω) : ℝ≥0) : ℝ) ∈
      Icc (0 : ℝ) ((min (τ i ω) (S.χ ω) : ℝ≥0) : ℝ) from
      ⟨(min (τ i ω) (S.χ ω)).coe_nonneg,le_rfl⟩)
  by_cases hτχ : τ i ω ≤ S.χ ω
  · rw [min_eq_left hτχ] at ha ⊢
    exact (S.frozen ω (S.χ ω) i hτχ).trans ha
  · have hχτ : S.χ ω ≤ τ i ω := le_of_not_ge hτχ
    simpa only [min_eq_right hχτ] using ha

/-- Every point is monitored only up to its own completion. Once all
completion prefixes satisfy the strict bounds, the localization cannot
occur before the common completion horizon. -/
theorem LocalizedState.cutoff_after_completed
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi M : ℝ} {H : ℝ≥0} {z : ι → ℂ} {τ : ι → Ω → ℝ≥0}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (S : LocalizedState B hm κ lo hi M H z τ γ G) (ω : Ω)
    (T : ℝ≥0) (hT : T < H) (_hτ : ∀ i, τ i ω ≤ T)
    (hB : ∀ t : ℝ≥0, t ≤ T → |B t ω| < M)
    (hheight : ∀ i (t : ℝ≥0), t ≤ τ i ω →
      (logLoewnerCoordinates (G ω) (z i) t).1.im ∈ Ioo lo hi) :
    T < S.χ ω := by
  by_contra hn
  have hχT : S.χ ω ≤ T := le_of_not_gt hn
  have hχH : S.χ ω < H := hχT.trans_lt hT
  have hstrict (i : ι) : (S.Q (S.χ ω) ω i).1.im ∈ Ioo lo hi := by
    rw [S.at_cutoff_eq_actual ω i]
    exact hheight i _ (min_le_left _ _)
  rcases S.boundary ω hχH with ⟨i,hi⟩ | hb
  · rcases hi with hlow | hhigh
    · exact (ne_of_gt (hstrict i).1) hlow
    · exact (ne_of_lt (hstrict i).2) hhigh
  · exact (ne_of_lt (hB (S.χ ω) hχT)) hb

end SLEExactGauge.Multipoint

end

end OAI
