import OAI.Probability.SLE.Loewner.MappedFutureSimple
import OAI.Probability.SLE.Loewner.SlitSegmentParameter

namespace OAI

/-! Centering at the proved driving value makes every future segment an
ordinary simple attached slit, to which the existing normalized chart
theorem applies. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

noncomputable def centeredFutureArc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) : C(unitInterval,ℂ) where
  toFun u := mappedFutureArc p hi h0 hH hst ht u-
    (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)
  continuous_toFun := (mappedFutureArc p hi h0 hH hst ht).continuous.sub continuous_const

@[simp] lemma centeredFutureArc_zero (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    centeredFutureArc p hi h0 hH hst ht 0=0 := by
  change mappedFutureArc p hi h0 hH hst ht 0-_=0
  rw [mappedFutureArc_zero,sub_self]

lemma centeredFutureArc_injective (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    Injective (centeredFutureArc p hi h0 hH hst ht) := by
  intro u v he
  exact mappedFutureArc_injective p hi h0 hH hst ht (sub_left_inj.mp he)

lemma centeredFutureArc_upper (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1)
    {u : unitInterval} (hu : u≠0) :
    centeredFutureArc p hi h0 hH hst ht u∈upperHalfPlane := by
  have hh := mappedFutureArc_upper p hi h0 hH hst ht hu
  change 0<(mappedFutureArc p hi h0 hH hst ht u).im at hh
  change 0<(_-(_ : ℂ)).im
  simpa only [sub_im,ofReal_im,sub_zero] using hh

noncomputable def futureSlitChart (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s t : unitInterval} (hst : s<t) (ht : t<1) :
    SimpleSlitChart (centeredFutureArc p hi h0 hH hst ht) :=
  Classical.choice (exists_simpleSlitChart _
    (centeredFutureArc_injective p hi h0 hH hst ht)
    (centeredFutureArc_zero p hi h0 hH hst ht)
    (fun _ hu => centeredFutureArc_upper p hi h0 hH hst ht hu))

end SLEExactGauge

end

end OAI
