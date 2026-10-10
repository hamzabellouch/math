import OAI.Probability.SLE.Loewner.InitialForwardTimeContinuity

namespace OAI

/-! The moving slit domain is open, and its actual forward coordinates
depend continuously on both time and the surviving point. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma isOpen_initialSlitDomain (p : C(unitInterval,ℂ)) :
    IsOpen {a : unitInterval × ℂ | a.2∈upperHalfPlane \ range (initialSubarc p a.1)} := by
  have hc : Continuous (fun a : unitInterval × unitInterval => (a.1,p (a.1*a.2))) :=
    continuous_fst.prodMk (p.continuous.comp (continuous_fst.mul continuous_snd))
  have hr : {a : unitInterval × ℂ | a.2∈range (initialSubarc p a.1)}=
      range (fun a : unitInterval × unitInterval => (a.1,p (a.1*a.2))) := by
    ext a
    constructor
    · rintro ⟨u,hu⟩
      exact ⟨(a.1,u),Prod.ext rfl hu⟩
    · rintro ⟨⟨s,u⟩,he⟩
      obtain ⟨hs,hz⟩ := Prod.mk.inj he
      dsimp only at hs hz
      subst s
      exact ⟨u,hz⟩
  have hclosed : IsClosed {a : unitInterval × ℂ | a.2∈range (initialSubarc p a.1)} := by
    rw [hr]
    exact (isCompact_range hc).isClosed
  exact (isOpen_upperHalfPlane.preimage continuous_snd).sdiff hclosed

theorem initialForwardChart_joint_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    Continuous (fun a : {a : unitInterval × ℂ |
      a.2∈upperHalfPlane \ range (initialSubarc p a.1)} =>
        initialForwardChart p hi h0 hH a.1.1 a.1.2) := by
  apply SeqContinuous.continuous
  intro v a hv
  have ht := ((continuous_fst.comp continuous_subtype_val).tendsto a).comp hv
  have hz := ((continuous_snd.comp continuous_subtype_val).tendsto a).comp hv
  exact initialForwardChart_tendsto p hi h0 hH ht hz a.property (fun n => (v n).property)

end SLEExactGauge

end

end OAI
