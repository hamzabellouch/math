import OAI.Probability.SLE.Stochastic.PlanarHarmonicSampling
import OAI.Probability.SLE.Geometry.ComplexHarmonicGenerator

namespace OAI

/-! Bounded holomorphic observables on the physical planar domain give
the two real harmonic tests used for conformal exit limits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def planarTranslatedDomain (D : Set ℂ) (w : ℂ) : Set (ℝ×ℝ) :=
  {z | w+Complex.equivRealProdCLM.symm z∈D}

lemma planarTranslatedDomain_open {D : Set ℂ} (hD : IsOpen D) (w : ℂ) :
    IsOpen (planarTranslatedDomain D w) :=
  hD.preimage (continuous_const.add Complex.equivRealProdCLM.symm.continuous)

lemma holomorphic_planar_components {D : Set ℂ} (hD : IsOpen D)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D) (w : ℂ) :
    (ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (F (w+Complex.equivRealProdCLM.symm z)).re)
      (planarTranslatedDomain D w) ∧
      ∀ z∈planarTranslatedDomain D w,
        planarGenerator (fun z => (F (w+Complex.equivRealProdCLM.symm z)).re) z=0) ∧
    (ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (F (w+Complex.equivRealProdCLM.symm z)).im)
      (planarTranslatedDomain D w) ∧
      ∀ z∈planarTranslatedDomain D w,
        planarGenerator (fun z => (F (w+Complex.equivRealProdCLM.symm z)).im) z=0) := by
  let G (z : ℂ) := F (w+z)
  have hG (z : ℂ) (hz : w+z∈D) : AnalyticAt ℂ G z :=
    (hF.analyticOnNhd hD _ hz).comp (analyticAt_const.add analyticAt_id)
  have hr (z) (hz : z∈planarTranslatedDomain D w) :
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z => (G (Complex.equivRealProdCLM.symm z)).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z
      (((hG _ hz).contDiffAt.restrict_scalars ℝ).comp z
        Complex.equivRealProdCLM.symm.contDiff.contDiffAt)
  have hi (z) (hz : z∈planarTranslatedDomain D w) :
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z => (G (Complex.equivRealProdCLM.symm z)).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z
      (((hG _ hz).contDiffAt.restrict_scalars ℝ).comp z
        Complex.equivRealProdCLM.symm.contDiff.contDiffAt)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact fun z hz => (hr z hz).contDiffWithinAt
  · intro z hz
    exact planarGenerator_harmonicAt (fun v => (G v).re) z (hG _ hz).harmonicAt_re
  · exact fun z hz => (hi z hz).contDiffWithinAt
  · intro z hz
    exact planarGenerator_harmonicAt (fun v => (G v).im) z (hG _ hz).harmonicAt_im

theorem holomorphic_stopped_converges
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    (w : ℂ) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F D)
    (e : SmoothDomainExhaustion (planarTranslatedDomain D w) 0)
    (T : ℝ≥0) (C : ℝ≥0) (hC : ∀ z∈D, ‖F z‖ ≤ C) :
    ∀ᵐ b ∂W.prod W, ∃ c : ℂ,
      Tendsto (fun n => F (w+Complex.equivRealProdCLM.symm (planarWiener (e.stop T n b) b)))
        atTop (𝓝 c) := by
  obtain ⟨⟨hr,hr0⟩,⟨hi,hi0⟩⟩ := holomorphic_planar_components hD hF w
  have hreal := e.harmonic_stopped_converges W hW T (planarTranslatedDomain_open hD w)
    _ hr hr0 C (fun z hz => (Complex.abs_re_le_norm _).trans (hC _ hz))
  have himag := e.harmonic_stopped_converges W hW T (planarTranslatedDomain_open hD w)
    _ hi hi0 C (fun z hz => (Complex.abs_im_le_norm _).trans (hC _ hz))
  filter_upwards [hreal,himag] with b hb hi
  obtain ⟨a,ha⟩ := hb
  obtain ⟨c,hc⟩ := hi
  refine ⟨Complex.equivRealProdCLM.symm (a,c),?_⟩
  have hh := Complex.equivRealProdCLM.symm.continuous.continuousAt.tendsto.comp
    (ha.prodMk_nhds hc)
  change Tendsto (fun n => Complex.equivRealProdCLM.symm
    ((F (w+Complex.equivRealProdCLM.symm (planarWiener (e.stop T n b) b))).re,
     (F (w+Complex.equivRealProdCLM.symm (planarWiener (e.stop T n b) b))).im))
    atTop (𝓝 (Complex.equivRealProdCLM.symm (a,c))) at hh
  simpa only [Complex.equivRealProdCLM_symm_apply,Complex.re_add_im] using hh

end SLEExactGauge

end

end OAI
