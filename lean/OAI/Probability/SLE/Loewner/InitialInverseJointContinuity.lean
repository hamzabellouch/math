import OAI.Probability.SLE.Loewner.InitialInverseLimitAt

namespace OAI

/-! Joint continuity of the exact inverse charts in time and an interior
half-plane coordinate. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma initialInverse_limit_eq (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (ht : Tendsto t atTop (𝓝 s)) :
    EqOn F (initialInverseChart p hi h0 hH s) upperHalfPlane := by
  by_cases hs : s=0
  · subst s
    intro z hz
    have hzero := ((initialInverseChart_tendsto_identity p hi h0 hH).tendsto_at hz).comp ht
    have he : F z=id z := tendsto_nhds_unique (hlim.tendsto_at hz) hzero
    simpa only [initialInverseChart_zero] using he
  · exact initialInverse_limit_eq_at p hi h0 hH hF hlim hs ht

theorem initialInverseChart_joint_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    Continuous (fun a : unitInterval × upperHalfPlane =>
      initialInverseChart p hi h0 hH a.1 a.2) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_of_subseq_tendsto
  intro v hv
  have ht : Tendsto (fun n => (v n).1) atTop (𝓝 a.1) :=
    (continuous_fst.tendsto a).comp hv
  have hz : Tendsto (fun n => ((v n).2:ℂ)) atTop (𝓝 (a.2:ℂ)) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto a).comp hv
  obtain ⟨φ,F,hφ,hF,hlim⟩ := initialInverseChart_subsequence p hi h0 hH (fun n => (v n).1)
  have he := initialInverse_limit_eq p hi h0 hH hF hlim (ht.comp hφ.tendsto_atTop)
  have heval := locallyUniform_evaluation_tendsto isOpen_upperHalfPlane hF.continuousOn
    hlim a.2.property (hz.comp hφ.tendsto_atTop)
  rw [he a.2.property] at heval
  refine ⟨φ,?_⟩
  exact heval

end SLEExactGauge

end

end OAI
