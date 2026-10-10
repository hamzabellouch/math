import OAI.NumberTheory.DirichletL.Descent.FullProfile

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma full_density_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    Integrable (fullProfileDensity g b₁ b₂ b₃) := by
  have hc : Continuous (fullProfileDensity g b₁ b₂ b₃) := by
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  simpa only [tripleHeight,coordinateHeight,pow_zero,Finset.prod_const_one,mul_one,one_mul] using
    fullProfileDensity_weighted_integrable g b₁ b₂ b₃ 0

lemma full_density_mode_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun p : Frequency × (ι → ℝ) => fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) := by
  have hc : Continuous (fun p : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y p.1 p.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact (full_density_integrable g b₁ b₂ b₃).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (pureProfileMode_norm a₁ a₂ ak y p.1 p.2).le))

theorem full_density_mode_fubini (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    (∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  let f : Frequency × (ι → ℝ) → ℂ := fun p => fullProfileDensity g b₁ b₂ b₃ p *
    pureProfileMode a₁ a₂ ak y p.1 p.2
  have hf : Integrable f (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak y
  change (∫ p, f p) = _
  rw [Measure.volume_eq_prod, integral_prod _ hf]
  have ht : Integrable (fun t : Frequency => ∫ u, f (t,u)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hf.integral_prod_left
  rw [Measure.volume_eq_prod, integral_prod _ ht]
  apply integral_congr_ae
  filter_upwards [ht.prod_right_ae] with t₁ ht₁
  simpa only [Measure.volume_eq_prod] using integral_prod (fun t : ℝ×ℝ => ∫ u, f ((t₁,t.1,t.2),u)) ht₁

theorem full_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s, c k * ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak (y k) p.1 p.2) =
    ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      ∑ k ∈ s, c k * pureProfileMode a₁ a₂ ak (y k) p.1 p.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk =>
    (full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
