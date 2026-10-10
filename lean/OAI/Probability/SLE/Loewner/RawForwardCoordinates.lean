import OAI.Probability.SLE.Loewner.RawForwardHeight

namespace OAI

/-! Exact real coordinate equations before a raw survival lifetime. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge.Target

lemma flow_coordinate_derivatives (b : Driver) (z : ℂ) {t S : ℝ}
    (ht : 0 ≤ t) (htS : t < S) (hs : Surviving 1 b z S) :
    HasDerivWithinAt (fun s => (flow 1 b z s).re)
      (2*((flow 1 b z t).re-driverValue b t)/
        (((flow 1 b z t).re-driverValue b t)^2+(flow 1 b z t).im^2)) (Ici t) t ∧
    HasDerivWithinAt (fun s => (flow 1 b z s).im)
      (-2*(flow 1 b z t).im/
        (((flow 1 b z t).re-driverValue b t)^2+(flow 1 b z t).im^2)) (Ici t) t := by
  have hd := (flow_hasDerivWithinAt_of_later_survival 1 b z t S ht htS hs).mono
    (Ici_subset_Ici.mpr ht)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  change HasDerivWithinAt (fun s => (flow 1 b z s).re)
    (((a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))).re) (Ici t) t at hr
  change HasDerivWithinAt (fun s => (flow 1 b z s).im)
    (((a 1 : ℂ)/(flow 1 b z t-(driverValue b t : ℂ))).im) (Ici t) t at hi
  constructor
  · convert! hr using 1
    simp [a,Complex.div_re,Complex.normSq_apply,pow_two]
  · convert! hi using 1
    simp [a,Complex.div_im,Complex.normSq_apply,pow_two]
    ring

lemma flow_continuousOn_before_lifetime (b : Driver) (z : ℂ) {τ : ℝ}
    (hs : ∀ t ∈ Ico 0 τ, Surviving 1 b z t) :
    ContinuousOn (flow 1 b z) (Ico 0 τ) := by
  intro t ht
  let S : ℝ := (t+τ)/2
  have htS : t < S := by dsimp [S]; linarith [ht.2]
  have hSτ : S < τ := by dsimp [S]; linarith [ht.2]
  exact (flow_hasDerivWithinAt_of_later_survival 1 b z t S ht.1 htS
    (hs S ⟨ht.1.trans htS.le,hSτ⟩)).continuousWithinAt.mono Ico_subset_Ici_self

end SLEExactGauge.Target

end

end OAI
