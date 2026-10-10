import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Differentiating an interval integral twice on a compact parameter strip.
Joint continuity supplies the uniform derivative bound, so no domination
estimate is added to the geometric hypotheses. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

private theorem continuousOn_rectangle_slice (F : ℝ → ℝ → ℝ)
    {δ a b ε : ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b)) (hε : ε ∈ Icc (-δ) δ) :
    ContinuousOn (F ε) (Icc a b) :=
  hF.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ ht => ⟨hε, ht⟩)

theorem intervalIntegral_hasDerivAt_rectangle (F G : ℝ → ℝ → ℝ)
    {δ a b ε : ℝ} (hab : a ≤ b) (hε : ε ∈ Ioo (-δ) δ)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => F r t) (G s t) s) :
    HasDerivAt (fun s => ∫ t in a..b, F s t) (∫ t in a..b, G ε t) ε := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  have hs : Ioo (-δ) δ ∈ 𝓝 ε := isOpen_Ioo.mem_nhds hε
  have hmeas : ∀ᶠ s in 𝓝 ε, AEStronglyMeasurable (F s) (volume.restrict (Ioc a b)) := by
    filter_upwards [hs] with s hs
    exact ((continuousOn_rectangle_slice F hF ⟨hs.1.le, hs.2.le⟩).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hFint : Integrable (F ε) (volume.restrict (Ioc a b)) :=
    (continuousOn_rectangle_slice F hF ⟨hε.1.le, hε.2.le⟩).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hGmeas : AEStronglyMeasurable (G ε) (volume.restrict (Ioc a b)) :=
    ((continuousOn_rectangle_slice G hG ⟨hε.1.le, hε.2.le⟩).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ s ∈ Ioo (-δ) δ, ‖G s t‖ ≤ C :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht s hs =>
      hC (s, t) ⟨⟨hs.1.le, hs.2.le⟩, ⟨ht.1.le, ht.2⟩⟩
  have hconst : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc a b)) :=
    (continuous_const : Continuous (fun _ : ℝ => C)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ∀ s ∈ Ioo (-δ) δ, HasDerivAt (fun r => F r t) (G s t) s :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht s hs => hd s hs t ⟨ht.1.le, ht.2⟩
  have hi := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas hFint
    hGmeas hbound hconst hdiff).2
  simpa only [intervalIntegral.integral_of_le hab] using hi

theorem intervalIntegral_secondDeriv_rectangle (F G H : ℝ → ℝ → ℝ)
    {δ a b : ℝ} (hδ : 0 < δ) (hab : a ≤ b)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hH : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Icc (-δ) δ ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => F r t) (G s t) s)
    (hdd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => G r t) (H s t) s) :
    HasDerivAt (deriv (fun s => ∫ t in a..b, F s t))
      (∫ t in a..b, H 0 t) 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hi := intervalIntegral_hasDerivAt_rectangle G H hab hzero hG hH hdd
  have heq : deriv (fun s => ∫ t in a..b, F s t) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ∫ t in a..b, G s t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact (intervalIntegral_hasDerivAt_rectangle F G hab hs hF hG hd).deriv
  exact hi.congr_of_eventuallyEq heq

/-- Matching chart boundary values cancel without requiring a global chart. -/
theorem finite_piece_boundary_cancellation (n : ℕ) (E I L R : ℕ → ℝ)
    (hE : ∀ i < n, E i = I i + R i - L i)
    (hjoin : ∀ i < n, R i = L (i + 1)) :
    (∑ i ∈ Finset.range n, E i) = (∑ i ∈ Finset.range n, I i) + L n - L 0 := by
  have hsum : (∑ i ∈ Finset.range n, E i) =
      (∑ i ∈ Finset.range n, I i) +
        ∑ i ∈ Finset.range n, (L (i + 1) - L i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hE i (Finset.mem_range.mp hi), hjoin i (Finset.mem_range.mp hi)]
    ring
  rw [hsum, Finset.sum_range_sub]
  ring

end
end PositiveEinsteinFour.Geometry

end OAI
