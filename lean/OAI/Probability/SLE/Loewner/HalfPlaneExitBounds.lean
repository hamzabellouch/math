import OAI.Probability.SLE.Loewner.HalfPlaneExitWeights
import OAI.Probability.SLE.Geometry.HarmonicExitProbability

namespace OAI

/-! The two half-plane angular upper bounds for finite physical exits. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def planarHalfPlaneExitArc (D : Set ℂ) (g : ℂ → ℂ) (w : ℂ) (T : ℝ≥0) (positive : Bool) :
    Set (Driver×Driver) :=
  {b | ∃ τ : ℝ≥0, 0 < τ ∧ τ ≤ T ∧
    (∀ t<τ, w+Complex.equivRealProdCLM.symm (planarWiener t b)∈D) ∧
    w+Complex.equivRealProdCLM.symm (planarWiener τ b)∉D ∧
    ∃ x : ℝ, (if positive then 0<x else x<0) ∧
      Tendsto (fun t => g (w+Complex.equivRealProdCLM.symm (planarWiener t b))) (𝓝[<] τ) (𝓝 (x:ℂ))}

theorem planarHalfPlaneExitArc_bound
    (W : WienerLaw) (hW : IsWiener W) {D : Set ℂ} (hD : IsOpen D)
    (w : ℂ) (hw : w∈D) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g D)
    (hgH : MapsTo g D upperHalfPlane) (T : ℝ≥0) (positive : Bool) :
    (W.prod W) (planarHalfPlaneExitArc D g w T positive) ≤
      ENNReal.ofReal (halfPlaneExitWeight positive (g w)) := by
  have hU := planarTranslatedDomain_open hD w
  have h0 : (0:ℝ×ℝ)∈planarTranslatedDomain D w := by simpa [planarTranslatedDomain] using hw
  let e := Classical.choice (exists_smoothDomainExhaustion _ hU 0 h0)
  let u (z : ℝ×ℝ) := halfPlaneExitWeight positive (g (w+Complex.equivRealProdCLM.symm z))
  obtain ⟨hu,hhar⟩ := halfPlaneExitWeight_planar positive hD hg hgH w
  have hub (z) (hz : z∈planarTranslatedDomain D w) : |u z|≤(1:ℝ≥0) := by
    have hh := halfPlaneExitWeight_bounds positive (hgH hz)
    rw [abs_of_nonneg hh.1]
    exact hh.2
  have hup (z) (hz : z∈planarTranslatedDomain D w) : 0 ≤ u z :=
    (halfPlaneExitWeight_bounds positive (hgH hz)).1
  have hh := e.nonnegative_harmonic_exit_bound W hW T hU u hu hhar 1 hub hup
    (planarHalfPlaneExitArc D g w T positive) 1 (by norm_num) (by
      rintro b ⟨τ,hτ,hτT,hp,hx,x,hs,hlim⟩
      refine ⟨τ,hτ,hτT,hp,hx,?_⟩
      cases positive
      · have him : ∀ᶠ t in 𝓝[<] τ, 0 ≤ (g (w+Complex.equivRealProdCLM.symm (planarWiener t b))).im :=
          (show ∀ᶠ t in 𝓝[<] τ, t<τ from self_mem_nhdsWithin).mono
            (fun t ht => (hgH (hp t ht)).le)
        exact halfPlaneExitWeight_negative_limit hs him hlim
      · exact halfPlaneExitWeight_positive_limit hs hlim)
  simpa [u] using hh

end SLEExactGauge

end

end OAI
