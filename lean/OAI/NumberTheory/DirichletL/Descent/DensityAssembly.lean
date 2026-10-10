import OAI.NumberTheory.DirichletL.Descent.ProfileIntegral

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem integrable_density_mode {ι : Type*} [Fintype ι]
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun z : Frequency × (ι → ℝ) => D z *
      pureProfileMode a₁ a₂ ak y z.1 z.2) := by
  have hc : Continuous (fun z : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y z.1 z.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact hD.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (pureProfileMode_norm a₁ a₂ ak y z.1 z.2).le))

theorem density_finite_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s,c k * ∫ z : Frequency × (ι → ℝ),D z*pureProfileMode a₁ a₂ ak (y k) z.1 z.2) =
    ∫ z : Frequency × (ι → ℝ),D z * ∑ k ∈ s,c k*pureProfileMode a₁ a₂ ak (y k) z.1 z.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk => (integrable_density_mode D hD a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
