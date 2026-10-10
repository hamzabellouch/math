import OAI.Probability.SLE.Geometry.HarmonicUniformTails

namespace OAI

/-! Bounded harmonic observables have actual left limits at every finite
domain exit, simultaneously on the original planar Wiener space. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target
namespace SmoothDomainExhaustion
variable {U : Set (ℝ×ℝ)} (e : SmoothDomainExhaustion U 0)

include e in
theorem harmonic_exit_limit
    (W : WienerLaw) (hW : IsWiener W) (T : ℝ≥0) (hU : IsOpen U)
    (u : ℝ×ℝ → ℝ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hhar : ∀ z∈U, planarGenerator u z=0)
    (C : ℝ≥0) (huC : ∀ z∈U, |u z|≤C) :
    ∃ Y : Driver×Driver → ℝ, Measurable Y ∧ (∀ b, |Y b|≤C) ∧
      (∫ b, Y b ∂W.prod W)=u 0 ∧
      (∀ᵐ b ∂W.prod W, Tendsto (fun n => u (planarWiener (e.stop T n b) b)) atTop (𝓝 (Y b))) ∧
      (∀ᵐ b ∂W.prod W, ∀ τ : ℝ≥0, τ ≤ T →
        (∀ t<τ, planarWiener t b∈U) → planarWiener τ b∉U →
          Tendsto (fun t => u (planarWiener t b)) (𝓝[<] τ) (𝓝 (Y b))) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Y,hYm,hYb,hY,hE⟩ := SmoothDomainExhaustion.harmonic_limit_data e W hW T hU u hu hhar C huC
  obtain ⟨N,hN,hgood⟩ := e.harmonic_uniform_tails W hW T hU u hu hhar C huC Y hY hE
  have hI : Tendsto (fun n => ∫ b, u (planarWiener (e.stop T n b) b) ∂W.prod W) atTop
      (𝓝 (∫ b, Y b ∂W.prod W)) := by
    have hM := e.harmonic_stopped_martingale W hW T hU u hu hhar C huC
    apply tendsto_integral_of_dominated_convergence (fun _ => (C:ℝ))
      (fun n => ((hM.1 n).mono ((e.stopFiltration T).le n)).aestronglyMeasurable) (integrable_const _)
    · intro n
      exact Eventually.of_forall fun b => by
        simpa only [Real.norm_eq_abs] using huC _ (e.stop_mem_domain T n b _ le_rfl)
    · exact hY
  have hIn (n) : (∫ b, u (planarWiener (e.stop T n b) b) ∂W.prod W)=u 0 := by
    have hh := planar_local_harmonic_optional W hW U (tsupport (e.cutoff n)) hU
      (e.compact n) (e.supported n) u hu hhar (e.stop T n) (e.stop_stopping T n)
      T (e.stop_le T n) (e.stop_mem_support T n)
    simpa only [planarWiener_zero,integral_const,probReal_univ,one_smul] using hh
  refine ⟨Y,hYm,hYb,?_,hY,?_⟩
  · exact tendsto_nhds_unique hI (by simpa only [hIn] using (tendsto_const_nhds (x := u 0)))
  · filter_upwards [hY,hgood] with b hb hg
    intro τ hτ hp hx
    exact e.boundary_limit_of_uniform_tail T u b (Y b) N hN hb hg τ hτ hp hx

end SmoothDomainExhaustion
end SLEExactGauge

end

end OAI
