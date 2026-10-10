import OAI.Probability.SLE.Geometry.SimplePathConcatenation
import OAI.Probability.SLE.Geometry.SimpleArcPlaneComplement
import OAI.Probability.SLE.Geometry.SimpleSlitConnected

namespace OAI

/-! Reflecting a simple attached arc across the real boundary produces
one simple planar arc, whose entire complement is connected. -/
noncomputable section
open Set Complex Function
open scoped Topology ComplexConjugate unitInterval

namespace SLEExactGauge

def reflectedArcSet (p : C(unitInterval,ℂ)) : Set ℂ :=
  range p ∪ conj '' range p

theorem reflectedArc_is_simple_arc (p : C(unitInterval,ℂ))
    (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    ∃ q : C(unitInterval,ℂ), Injective q ∧ range q=reflectedArcSet p := by
  let r : Path (0:ℂ) (p 1) := ⟨p,h0,rfl⟩
  let l : Path (conj (p 1)) 0 := {
    toFun := fun t => conj (p (unitInterval.symm t))
    continuous_toFun := Complex.continuous_conj.comp (p.continuous.comp unitInterval.continuous_symm)
    source' := by simp
    target' := by simp [h0] }
  have hl : Injective l := by
    intro s t he
    apply unitInterval.symm_bijective.injective
    apply hi
    change conj (p (unitInterval.symm s))=conj (p (unitInterval.symm t)) at he
    simpa only [conj_conj] using congrArg conj he
  have hr : Injective r := hi
  have hc (s t : unitInterval) (he : l s=r t) : s=1 ∧ t=0 := by
    have ht : t=0 := by
      by_contra ht
      have htp := hH t ht
      have hsp : 0 ≤ (p (unitInterval.symm s)).im := by
        by_cases hs : unitInterval.symm s=0
        · simp [hs,h0]
        · exact (hH _ hs).le
      have hh := congrArg Complex.im he
      change -(p (unitInterval.symm s)).im=(p t).im at hh
      change 0 < (p t).im at htp
      linarith
    have hs : s=1 := by
      have hz : p (unitInterval.symm s)=p 0 := by
        have hh : conj (p (unitInterval.symm s))=0 := by simpa [l,r,ht,h0] using he
        have hh' := congrArg conj hh
        simpa [h0] using hh'
      have hsym := hi hz
      simpa using congrArg unitInterval.symm hsym
    exact ⟨hs,ht⟩
  refine ⟨(l.trans r).toContinuousMap,path_trans_injective l r hl hr hc,?_⟩
  rw [Path.coe_toContinuousMap,Path.trans_range]
  have hlrange : range l=conj '' range p := by
    change range (fun t => conj (p (unitInterval.symm t)))=conj '' range p
    exact (unitInterval.symm_bijective.surjective.range_comp
      (fun t => conj (p t))).trans (range_comp conj p)
  rw [hlrange]
  exact union_comm _ _

theorem reflectedArc_complement_connected (p : C(unitInterval,ℂ))
    (hi : Injective p) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    IsConnected (reflectedArcSet p)ᶜ := by
  obtain ⟨q,hq,hqrange⟩ := reflectedArc_is_simple_arc p hi h0 hH
  rw [← hqrange]
  exact simple_arc_plane_complement_connected q hq

end SLEExactGauge

end

end OAI
