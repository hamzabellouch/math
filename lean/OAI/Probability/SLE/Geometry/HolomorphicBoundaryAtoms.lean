import OAI.Probability.SLE.Geometry.DiskPoissonPeaks
import OAI.Probability.SLE.Geometry.HarmonicExitProbability

namespace OAI

/-! Positive harmonic peaks bound the probability that a finite domain
exit maps to a prescribed point on the unit circle. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def planarDiskExitAtom (D : Set ℂ) (F : ℂ → ℂ) (w a : ℂ) (T : ℝ≥0) : Set (Driver×Driver) :=
  {b | ∃ τ : ℝ≥0, 0 < τ ∧ τ ≤ T ∧
    (∀ t<τ, w+Complex.equivRealProdCLM.symm (planarWiener t b)∈D) ∧
    w+Complex.equivRealProdCLM.symm (planarWiener τ b)∉D ∧
    Tendsto (fun t => F (w+Complex.equivRealProdCLM.symm (planarWiener t b))) (𝓝[<] τ) (𝓝 a)}

theorem planarDiskExitAtom_peak_bound
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    (w : ℂ) (hw : w∈D) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D)
    (hFD : MapsTo F D (ball 0 1)) (hF0 : F w=0)
    (a : ℂ) (ha : ‖a‖=1) (T : ℝ≥0) (r : ℝ) (hr : 0 ≤ r) (hr1 : r<1) :
    ENNReal.ofReal ((1+r)/(1-r))*(W.prod W) (planarDiskExitAtom D F w a T) ≤ 1 := by
  let G := diskPeak a r ∘ F
  have hG : DifferentiableOn ℂ G D := (diskPeak_differentiable ha hr hr1).comp hF hFD
  have hU := planarTranslatedDomain_open hD w
  have h0 : (0:ℝ×ℝ)∈planarTranslatedDomain D w := by simpa [planarTranslatedDomain] using hw
  let e := Classical.choice (exists_smoothDomainExhaustion _ hU 0 h0)
  obtain ⟨⟨hu,hhar⟩,_⟩ := holomorphic_planar_components hD hG w
  let u (z : ℝ×ℝ) := (G (w+Complex.equivRealProdCLM.symm z)).re
  have hC : 0 ≤ (1+r)/(1-r) := by positivity
  let C : ℝ≥0 := ⟨(1+r)/(1-r),hC⟩
  have hub (z) (hz : z∈planarTranslatedDomain D w) : |u z|≤C :=
    (Complex.abs_re_le_norm _).trans
      (diskPeak_norm_bound ha hr hr1 (mem_ball_zero_iff.mp (hFD hz)).le)
  have hup (z) (hz : z∈planarTranslatedDomain D w) : 0 ≤ u z :=
    diskPeak_re_nonnegative ha hr hr1 (mem_ball_zero_iff.mp (hFD hz)).le
  have hh := e.nonnegative_harmonic_exit_bound W hW T hU u hu hhar C hub hup
    (planarDiskExitAtom D F w a T) ((1+r)/(1-r)) hC (by
      rintro b ⟨τ,hτ,hτT,hp,hx,hl⟩
      refine ⟨τ,hτ,hτT,hp,hx,?_⟩
      have hpeak := (diskPeak_continuousAt_boundary ha hr hr1 ha.le).tendsto.comp hl
      have hreal := Complex.continuous_re.continuousAt.tendsto.comp hpeak
      change Tendsto (fun t => (diskPeak a r (F (w+Complex.equivRealProdCLM.symm
        (planarWiener t b)))).re) (𝓝[<] τ) (𝓝 (diskPeak a r a).re) at hreal
      simpa only [u,G,Function.comp_apply,diskPeak_at_peak ha,Complex.ofReal_re] using hreal)
  have hu0 : u 0=1 := by simp [u,G,hF0,diskPeak_zero ha]
  simpa only [hu0,ENNReal.ofReal_one] using hh

end SLEExactGauge

end

end OAI
