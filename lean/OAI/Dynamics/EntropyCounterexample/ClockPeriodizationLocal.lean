import OAI.Dynamics.EntropyCounterexample.ClockPeriodizationCompatibility

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace Problem340.ClockPeriodization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_tsum_of_locallyFinite {ι : Type*} {f : ι → E → F}
    {n : ℕ∞ω} {s : Set E} (hf : ∀ i, ContDiffOn ℝ n (f i) s)
    (hl : LocallyFinite (fun i => support (f i))) :
    ContDiffOn ℝ n (fun x => ∑' i, f i x) s := by
  have heq : (fun x => ∑' i, f i x) = (fun x => ∑ᶠ i, f i x) := by
    funext x
    exact tsum_eq_finsum (hl.point_finite x)
  rw [heq]
  exact contMDiffOn_iff_contDiffOn.mp (contMDiffOn_finsum hl
    (fun i => contMDiffOn_iff_contDiffOn.mpr (hf i)))

theorem contDiffOn_periodize {P a b : ℝ} {n : ℕ∞ω} {U : Set E}
    (hP : 0 < P) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (univ ×ˢ U))
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiffOn ℝ n (periodize P f) (univ ×ˢ U) := by
  apply contDiffOn_tsum_of_locallyFinite
  · intro k
    exact hf.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun x hx => ⟨mem_univ _, hx.2⟩)
  · exact locallyFinite_translates hP hsupport

end Problem340.ClockPeriodization

namespace Problem340.ClockQuotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_periodize {P a b : ℝ} {n : ℕ∞ω} {U : Set E}
    (hP : 0 < P) {f : ℝ × E → F}
    (hf : ContDiffOn ℝ n f (univ ×ˢ U))
    (hsupport : ∀ x, f x ≠ 0 → x.1 ∈ Icc a b) :
    ContDiffOn ℝ n (periodize P f) (univ ×ˢ U) := by
  rw [periodize_eq_clockPeriodization hP hsupport]
  exact ClockPeriodization.contDiffOn_periodize hP hf hsupport

end Problem340.ClockQuotient

end

end OAI
