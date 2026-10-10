import OAI.Probability.InvariantIsing.Spectral.SpectralTemperatureFunctional

namespace OAI

/-! L1 approximation of the trial path preserves the finite spectral
interaction functional, as required when removing a finite partition. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma finiteTemperatureFunctional_tendsto_of_L1 {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun k => ∫ s, |q k s - p s| ∂pathMeasure) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k => finiteTemperatureFunctional ρ eig hρ hρsum (q k) t) atTop
      (𝓝 (finiteTemperatureFunctional ρ eig hρ hρsum p t)) := by
  let K := ∑ a, |eig a|
  have heig (a : ι) : |eig a| ≤ K :=
    Finset.single_le_sum (fun b _ => abs_nonneg (eig b)) (Finset.mem_univ a)
  have hbound (x : ℝ) : |finiteR ρ eig hρ hρsum x| ≤ K :=
    abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  have hd (r : ℝ) : Tendsto (fun k => deficit (q k) r) atTop (𝓝 (deficit p r)) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm' _ hL
    exact Filter.Eventually.of_forall (fun k => by
      simpa only [Real.norm_eq_abs] using abs_deficit_sub_path_le (q k) p r)
  have hi : Tendsto (fun k => ∫ r, t * finiteR ρ eig hρ hρsum (t * deficit (q k) r)
      ∂pathMeasure) atTop
      (𝓝 (∫ r, t * finiteR ρ eig hρ hρsum (t * deficit p r) ∂pathMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => t * K)
    · intro k
      exact (continuous_const.mul ((continuous_finiteR ρ eig hρ hρsum).comp
        (continuous_const.mul (continuous_deficit (q k))))).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht]
        exact mul_le_mul_of_nonneg_left (hbound _) ht)
    · exact ae_of_all _ (fun r =>
        (((continuous_finiteR ρ eig hρ hρsum).tendsto _).comp ((hd r).const_mul t)).const_mul t)
  simpa only [finiteTemperatureFunctional_eq ρ eig hρ hρsum _ ht,
    spectralFunctional] using hi.const_mul (1 / 2 : ℝ)

end InvariantIsing

end

end OAI
