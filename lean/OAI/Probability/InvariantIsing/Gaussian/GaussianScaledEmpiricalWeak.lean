import OAI.Probability.InvariantIsing.Spectral.EmpiricalLawContinuity

namespace OAI

/-! The full real-coupling empirical MP limit, without cross-dimensional independence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

lemma empiricalSpectralLaw_scale {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) (c : ℝ) :
    (empiricalSpectralLaw hN eig).map (fun x => c*x) =
      empiricalSpectralLaw hN (fun i => c*eig i) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact empiricalSpectralLaw_map hN eig (fun x => c*x) (measurable_const.mul measurable_id)

theorem gaussianPattern_scaled_empirical_weak {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) (c : ℝ) :
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i))) atTop
      (fun _ => LevyProkhorov.ofMeasure (scaledSpectralLaw
        ⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ c)) := by
  have hm (k : ℕ) : AEStronglyMeasurable (fun ω => LevyProkhorov.ofMeasure
      (empiricalSpectralLaw (Nat.succ_pos k) (fun i => c*gaussianPatternEigenvalues (Z (k+1) ω) i))) P := by
    exact (continuous_scaled_gaussianEmpirical (m := gaussianPatternCount α (k+1))
      (Nat.succ_pos k) c).aestronglyMeasurable.comp_aemeasurable (hZ (k+1)).aemeasurable
  apply (exists_seq_tendstoInMeasure_atTop_iff hm).mpr
  intro ns hns
  obtain ⟨u,hu,heu⟩ := ((gaussianPattern_empirical_weak hα P Z hZ).comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨u,hu,?_⟩
  filter_upwards [heu] with ω hω
  have hw := (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto _).comp hω
  have hs := (ProbabilityMeasure.continuous_map
    (show Continuous (fun x : ℝ => c*x) from continuous_const.mul continuous_id)).tendsto _ |>.comp hw
  have hl := (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto _).comp hs
  change Tendsto (fun k => LevyProkhorov.ofMeasure
    ((empiricalSpectralLaw (Nat.succ_pos (ns (u k))) (gaussianPatternEigenvalues (Z (ns (u k)+1) ω))).map
      (fun x => c*x))) atTop
    (𝓝 (LevyProkhorov.ofMeasure (scaledSpectralLaw
      ⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ c))) at hl
  simpa only [empiricalSpectralLaw_scale,scaledSpectralLaw,Function.comp_apply] using hl

end InvariantIsing

end

end OAI
