import OAI.Probability.SLE.Geometry.ClosedComplexUnion

namespace OAI

/-! Replacing one compact arc in a Jordan boundary while fixing the
other arc. The replacement retains the supplied interval parameter. -/
noncomputable section
open Set

namespace SLEExactGauge

def arcParameterHomeomorph (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1))
    (hi : InjOn p (Icc 0 1)) : (Icc (0:ℝ) 1) ≃ₜ (p '' Icc 0 1) := by
  let e := Equiv.Set.imageOfInjOn p (Icc 0 1) hi
  have he : Continuous e := hc.mapsToRestrict (mapsTo_image p (Icc 0 1))
  exact e.toHomeomorphOfContinuousClosed he he.isClosedMap

@[simp] lemma arcParameterHomeomorph_apply
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (s : Icc (0:ℝ) 1) : (arcParameterHomeomorph p hc hi s : ℂ)=p s := rfl

def arcParameterReplacement (p q : ℝ → ℂ)
    (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (hqc : ContinuousOn q (Icc 0 1)) (hqi : InjOn q (Icc 0 1)) :
    (p '' Icc 0 1) ≃ₜ (q '' Icc 0 1) :=
  (arcParameterHomeomorph p hc hi).symm.trans (arcParameterHomeomorph q hqc hqi)

lemma arcParameterReplacement_apply (p q : ℝ → ℂ)
    (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (hqc : ContinuousOn q (Icc 0 1)) (hqi : InjOn q (Icc 0 1))
    (s : ℝ) (hs : s ∈ Icc 0 1) :
    (arcParameterReplacement p q hc hi hqc hqi ⟨p s,mem_image_of_mem p hs⟩ : ℂ)=q s := by
  have hh : arcParameterHomeomorph p hc hi ⟨s,hs⟩ = ⟨p s,mem_image_of_mem p hs⟩ := rfl
  change (arcParameterHomeomorph q hqc hqi
    ((arcParameterHomeomorph p hc hi).symm ⟨p s,mem_image_of_mem p hs⟩) : ℂ)=q s
  rw [← hh,Homeomorph.symm_apply_apply]
  rfl

def fixedArcBoundaryReplacement (p q : ℝ → ℂ) (B : Set ℂ)
    (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (hqc : ContinuousOn q (Icc 0 1)) (hqi : InjOn q (Icc 0 1))
    (hB : IsClosed B) (hzero : q 0=p 0) (hone : q 1=p 1)
    (hpB : ∀ s ∈ Icc 0 1, p s ∈ B → s=0 ∨ s=1)
    (hqB : ∀ s ∈ Icc 0 1, q s ∈ B → s=0 ∨ s=1) :
    ↥(p '' Icc 0 1 ∪ B) ≃ₜ ↥(q '' Icc 0 1 ∪ B) := by
  apply closedComplexUnionHomeomorph (isCompact_Icc.image_of_continuousOn hc).isClosed
    (isCompact_Icc.image_of_continuousOn hqc).isClosed hB
    (arcParameterReplacement p q hc hi hqc hqi)
  · rintro ⟨z,⟨s,hs,rfl⟩⟩ hzB
    rw [arcParameterReplacement_apply p q hc hi hqc hqi s hs]
    rcases hpB s hs hzB with rfl | rfl
    · exact hzero
    · exact hone
  · rintro ⟨z,⟨s,hs,rfl⟩⟩ hzB
    change (arcParameterReplacement q p hqc hqi hc hi
      ⟨q s,mem_image_of_mem q hs⟩ : ℂ)=q s
    rw [arcParameterReplacement_apply q p hqc hqi hc hi s hs]
    rcases hqB s hs hzB with rfl | rfl
    · exact hzero.symm
    · exact hone.symm

end SLEExactGauge

end

end OAI
