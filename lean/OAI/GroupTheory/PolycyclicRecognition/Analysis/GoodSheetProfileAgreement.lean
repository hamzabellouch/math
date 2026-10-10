import OAI.GroupTheory.PolycyclicRecognition.Analysis.SublinearSheetLimits

namespace OAI

/-! # Good sets suffice to compare the limiting values on two sheets -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology NNReal

/-- A good set may have vanishing relative probability. Its nonemptiness,
vanishing profile errors, and the actual short source bridge still identify
the two limiting profile values. -/
theorem good_sheet_profile_values_eq
    {G W Z A : Type*} [Group G] [PseudoMetricSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {K : ℝ≥0} (J : ℕ → G → W) (hJ : ∀ n, LipschitzWith K (J n))
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (x : ℕ → G) (k l : ℕ → A → G) (chart : ℕ → Z → G) (z : Z)
    (Good : ℕ → Set A) (hne : ∀ n, (Good n).Nonempty)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (f g : W)
    (happrox : ∀ᶠ n in atTop, ∀ a ∈ Good n,
      ‖rescaledMapProfile (J n) (x n) (k n a) (Real.log (scale n)) (chart n) z - f‖ ≤ ε n ∧
      ‖rescaledMapProfile (J n) (x n) (l n a) (Real.log (scale n)) (chart n) z - g‖ ≤ ε n)
    (hnear : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ a ∈ Good n,
      dist (x n * k n a * chart n z) (x n * l n a * chart n z) ≤ η * scale n) : f = g := by
  choose a ha using hne
  have hf : Tendsto (fun n => rescaledMapProfile (J n) (x n) (k n (a n))
      (Real.log (scale n)) (chart n) z) atTop (𝓝 f) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [happrox, hε.eventually (gt_mem_nhds hη)] with n hn he
    exact (show dist _ f ≤ ε n from by simpa only [dist_eq_norm] using (hn (a n) (ha n)).1).trans_lt he
  have hg : Tendsto (fun n => rescaledMapProfile (J n) (x n) (l n (a n))
      (Real.log (scale n)) (chart n) z) atTop (𝓝 g) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [happrox, hε.eventually (gt_mem_nhds hη)] with n hn he
    exact (show dist _ g ≤ ε n from by simpa only [dist_eq_norm] using (hn (a n) (ha n)).2).trans_lt he
  exact rescaled_profile_limits_eq_of_sublinear_sheet_distance J hJ scale hscale x
    (fun n => k n (a n)) (fun n => l n (a n)) chart (fun _ => z) f g hf hg
    (fun η hη => (hnear η hη).mono fun n hn => hn (a n) (ha n))

end PolycyclicRecognition

end

end OAI
