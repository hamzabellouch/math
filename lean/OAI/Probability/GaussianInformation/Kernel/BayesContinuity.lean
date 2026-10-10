import Mathlib
import OAI.Probability.GaussianInformation.Kernel.PotentialContinuity

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open EntropySupport Coercivity Sphere DriftTools Continuity
lemma tendsto_mass {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (r : ℕ → α → ℝ) (g : α → ℝ) (hr : ∀ n,Measurable (r n))
    (hr0 : ∀ n s,0 ≤ r n s) (hr1 : ∀ n s,r n s ≤ 1)
    (hlim : ∀ᵐ s ∂ν,Tendsto (fun n => r n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => mass ν (r n)) atTop (𝓝 (mass ν g)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ)) (fun n => (hr n).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hr0 n s)]; exact hr1 n s)) hlim

lemma tendsto_weighted_Phi_positive {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H) (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ) (hr : ∀ n,Measurable (r n)) (hg : Measurable g)
    {ε : ℝ} (hε : 0 < ε) (hrε : ∀ n s,ε ≤ r n s) (hgε : ∀ s,ε ≤ g s)
    (hr1 : ∀ n s,r n s ≤ 1) (hg1 : ∀ s,g s ≤ 1)
    (hlim : ∀ᵐ s ∂ν,Tendsto (fun n => r n s) atTop (𝓝 (g s))) :
    Tendsto (fun n => mass ν (r n)*Phi (post ν (r n))) atTop (𝓝 (mass ν g*Phi (post ν g))) := by
  have hr0 (n s) : 0 ≤ r n s := hε.le.trans (hrε n s)
  have hg0 (s) : 0 ≤ g s := hε.le.trans (hgε s)
  have ha (n) : ε ≤ mass ν (r n) := (mass_bounds ν (r n) (hr n) hε (hrε n) (hr1 n)).1
  have hap (n) := hε.trans_le (ha n)
  have hb : ε ≤ mass ν g := (mass_bounds ν g hg hε hgε hg1).1
  have hbp := hε.trans_le hb
  have hmass := tendsto_mass ν r g hr hr0 hr1 hlim
  obtain ⟨f,hf,hf0,hfH,hνf⟩ := bounded_density_representation (sphereProbability d) ν hH hν
  let F := fun n s => f s*r n s/mass ν (r n)
  let G := fun s => f s*g s/mass ν g
  have hF (n) : Measurable (F n) := (hf.mul (hr n)).div_const _
  have hG : Measurable G := (hf.mul hg).div_const _
  have hF0 (n s) : 0 ≤ F n s := div_nonneg (mul_nonneg (hf0 s) (hr0 n s)) (hap n).le
  have hG0 (s) : 0 ≤ G s := div_nonneg (mul_nonneg (hf0 s) (hg0 s)) hbp.le
  have hFb (n s) : F n s ≤ H/ε := by
    apply (div_le_div_of_nonneg_left (mul_nonneg (hf0 s) (hr0 n s)) hε (ha n)).trans
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hr1 n s) (hf0 s)).trans (by simpa using hfH s)) hε.le
  have hGb (s) : G s ≤ H/ε := by
    apply (div_le_div_of_nonneg_left (mul_nonneg (hf0 s) (hg0 s)) hε hb).trans
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left (hg1 s) (hf0 s)).trans (by simpa using hfH s)) hε.le
  have hpost (n) : post ν (r n)=densityLaw (F n) := post_density _ _ f _ hf hf0 (hr n) hνf
  have hpostg : post ν g=densityLaw G := post_density _ _ f _ hf hf0 hg hνf
  have hfp (n) : IsProbabilityMeasure (densityLaw (F n)) := by
    rw [← hpost n]; exact post_probability ν _ (hr n) (hr0 n) (hr1 n) (hap n)
  have hgp : IsProbabilityMeasure (densityLaw G) := by
    rw [← hpostg]; exact post_probability ν _ hg hg0 hg1 hbp
  have hlimf : ∀ᵐ s ∂sphereProbability d,Tendsto (fun n => F n s) atTop (𝓝 (G s)) := by
    rw [hνf,ae_withDensity_iff hf.ennreal_ofReal] at hlim
    filter_upwards [hlim] with s hs
    by_cases hfz : f s=0
    · simp only [F,G,hfz,zero_mul,zero_div]; exact tendsto_const_nhds
    · exact (tendsto_const_nhds.mul (hs (by simpa using (lt_of_le_of_ne (hf0 s) (Ne.symm hfz))))).div hmass hbp.ne'
  have hp := tendsto_Phi hd F G hF hG hF0 hG0 (div_pos hH hε) hFb hGb hfp hgp hlimf
  simp_rw [← hpost,← hpostg] at hp
  exact hmass.mul hp
end KernelPotential.Bayes

end OAI
