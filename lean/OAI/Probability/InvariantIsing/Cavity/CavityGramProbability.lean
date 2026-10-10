import OAI.Probability.InvariantIsing.Cavity.CavityGram

namespace OAI

/-! The nondegenerate Gaussian frames have probability tending to one.
This also supplies the positive mass needed to condition the finite frame
construction, without any assertion about zero sets of polynomials. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma continuous_cavityEmpiricalGram (q n : ℕ) :
    Continuous (fun x : ℕ → Fin q → ℝ => cavityEmpiricalGram x n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold cavityEmpiricalGram
  fun_prop

def cavityGoodGram (q n : ℕ) : Set (ℕ → Fin q → ℝ) :=
  {x | 0 < (cavityEmpiricalGram x n).det}

lemma measurableSet_cavityGoodGram (q n : ℕ) : MeasurableSet (cavityGoodGram q n) :=
  measurableSet_lt measurable_const (continuous_cavityEmpiricalGram q n).matrix_det.measurable

lemma cavityGoodGram_ae_eventually (q : ℕ) :
    ∀ᵐ x ∂cavityGaussianRows q, ∀ᶠ n in atTop, x ∈ cavityGoodGram q n := by
  filter_upwards [cavityEmpiricalGram_eventually_posDef q] with x hx
  filter_upwards [hx] with n hn
  exact hn.det_pos

theorem cavityGoodGram_probability_tendsto (q : ℕ) :
    Tendsto (fun n => (cavityGaussianRows q).real (cavityGoodGram q n)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n => ∫ x, (cavityGoodGram q n).indicator
      (fun _ => (1 : ℝ)) x ∂cavityGaussianRows q) atTop
      (𝓝 (∫ _x, (1 : ℝ) ∂cavityGaussianRows q)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact aestronglyMeasurable_const.indicator (measurableSet_cavityGoodGram q n)
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun x => by
        by_cases hx : x ∈ cavityGoodGram q n <;> simp [hx])
    · filter_upwards [cavityGoodGram_ae_eventually q] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp only [Set.indicator_of_mem hn]
  have he (n : ℕ) : (∫ x, (cavityGoodGram q n).indicator (fun _ => (1 : ℝ)) x
      ∂cavityGaussianRows q) = (cavityGaussianRows q).real (cavityGoodGram q n) :=
    integral_indicator_one (measurableSet_cavityGoodGram q n)
  simp_rw [he] at hi
  simpa using hi

lemma cavityGoodGram_eventually_positive (q : ℕ) :
    ∀ᶠ n in atTop, 0 < (cavityGaussianRows q).real (cavityGoodGram q n) :=
  (cavityGoodGram_probability_tendsto q).eventually
    (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))

end InvariantIsing

end

end OAI
