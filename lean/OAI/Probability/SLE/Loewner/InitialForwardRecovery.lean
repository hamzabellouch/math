import OAI.Probability.SLE.Loewner.InitialForwardLimit

namespace OAI

/-! Recover actual forward coordinates from their compactified limits. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialForward_limit_tendsto (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {A : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (upperHalfPlane \ range p))
    (hlim : TendstoLocallyUniformlyOn
      (fun n z => halfPlaneCayley (initialForwardChart p hi h0 hH (t n) z))
      A atTop (upperHalfPlane \ range p)) {z : ℂ} (hz : z∈upperHalfPlane \ range p) :
    Tendsto (fun n => initialForwardChart p hi h0 hH (t n) z)
      atTop (𝓝 (halfPlaneCayleyInv (A z))) := by
  have hn := initialForwardCayley_limit_interior p hi h0 hH hA hlim z hz
  have hne : A z≠1 := by
    intro he
    simp only [he,norm_one,lt_self_iff_false] at hn
  have hc : ContinuousAt halfPlaneCayleyInv (A z) := by
    apply (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
      (continuousAt_const.sub continuousAt_id)
    exact sub_ne_zero.mpr hne.symm
  have ht := hc.tendsto.comp (hlim.tendsto_at hz)
  apply ht.congr
  intro n
  exact halfPlaneCayleyInv_cayley
    (show 0≤(initialForwardChart p hi h0 hH (t n) z).im from
      (show 0<(initialForwardChart p hi h0 hH (t n) z).im from
        initialForwardChart_mapsTo p hi h0 hH (t n) hz).le)

end SLEExactGauge

end

end OAI
