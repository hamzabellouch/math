import Mathlib
import OAI.Analysis.BiholderTransport.Convexity.ShortEnvelopeSemibound

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def secondJetPullback (j : F →L[ℝ] ℝ) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (m : E →L[ℝ] F) (r : E →L[ℝ] E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E F ℝ).flip m).comp (h.comp m)+
    (ContinuousLinearMap.compL ℝ E F ℝ j).comp r

lemma secondJetPullback_apply (j : F →L[ℝ] ℝ) (h : F →L[ℝ] F →L[ℝ] ℝ)
    (m : E →L[ℝ] F) (r : E →L[ℝ] E →L[ℝ] F) (v w : E) :
    secondJetPullback j h m r v w=h (m v) (m w)+j (r v w) := rfl

lemma secondJetPullback_tendsto {ι : Type*} {L : Filter ι}
    {j : ι → F →L[ℝ] ℝ} {h : ι → F →L[ℝ] F →L[ℝ] ℝ}
    {m : ι → E →L[ℝ] F} {r : ι → E →L[ℝ] E →L[ℝ] F}
    {j₀ : F →L[ℝ] ℝ} {h₀ : F →L[ℝ] F →L[ℝ] ℝ}
    {m₀ : E →L[ℝ] F} {r₀ : E →L[ℝ] E →L[ℝ] F}
    (hj : Tendsto j L (𝓝 j₀)) (hh : Tendsto h L (𝓝 h₀))
    (hm : Tendsto m L (𝓝 m₀)) (hr : Tendsto r L (𝓝 r₀)) :
    Tendsto (fun i => secondJetPullback (j i) (h i) (m i) (r i)) L
      (𝓝 (secondJetPullback j₀ h₀ m₀ r₀)) := by
  let : NormedAddCommGroup (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hm' := (((ContinuousLinearMap.compL ℝ E F ℝ).flip).continuous.tendsto m₀).comp hm
  have hh' := ((ContinuousLinearMap.compL ℝ E F (F →L[ℝ] ℝ)).continuous₂.tendsto (h₀,m₀)).comp
    (hh.prodMk_nhds hm)
  have hfirst := ((ContinuousLinearMap.compL ℝ E (F →L[ℝ] ℝ) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip) m₀,h₀.comp m₀)).comp (hm'.prodMk_nhds hh')
  have hj' := ((ContinuousLinearMap.compL ℝ E F ℝ).continuous.tendsto j₀).comp hj
  have hsecond := ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] F) (E →L[ℝ] ℝ)).continuous₂.tendsto
    (ContinuousLinearMap.compL ℝ E F ℝ j₀,r₀)).comp (hj'.prodMk_nhds hr)
  exact hfirst.add hsecond

lemma rough_smooth_pullback_limit_semibound {ι : Type*} {L : Filter ι}
    {f q : ι → F → ℝ} {g : ι → E → F} {x : ι → E}
    {j₀ : F →L[ℝ] ℝ} {h₀ : F →L[ℝ] F →L[ℝ] ℝ}
    {m₀ : E →L[ℝ] F} {r₀ : E →L[ℝ] E →L[ℝ] F}
    (hjet : ∀ᶠ i in L,
      (∀ᶠ y in 𝓝 (g i (x i)),DifferentiableAt ℝ (f i) y) ∧
      DifferentiableAt ℝ (fderiv ℝ (f i)) (g i (x i)) ∧
      ContDiffAt ℝ 2 (q i) (g i (x i)) ∧ ContDiffAt ℝ 2 (g i) (x i) ∧
      q i (g i (x i))=f i (g i (x i)) ∧ q i≤ᶠ[𝓝 (g i (x i))] f i)
    (hj : Tendsto (fun i => fderiv ℝ (q i) (g i (x i))) L (𝓝 j₀))
    (hh : Tendsto (fun i => fderiv ℝ (fderiv ℝ (q i)) (g i (x i))) L (𝓝 h₀))
    (hm : Tendsto (fun i => fderiv ℝ (g i) (x i)) L (𝓝 m₀))
    (hr : Tendsto (fun i => fderiv ℝ (fderiv ℝ (g i)) (x i)) L (𝓝 r₀))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i in L,∀ d:E, secondJetPullback j₀ h₀ m₀ r₀ d d-ε*‖d‖^2≤
      fderiv ℝ (fderiv ℝ (fun a => f i (g i a))) (x i) d d := by
  have Hlim := secondJetPullback_tendsto hj hh hm hr
  have Hsmall := ((Metric.tendsto_nhds (α := E →L[ℝ] E →L[ℝ] ℝ)).mp Hlim) ε hε
  filter_upwards [hjet,Hsmall] with i hi hs
  intro d
  have Hle := second_fderiv_comp_minorant_le hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1
    hi.2.2.2.2.1 hi.2.2.2.2.2 d
  rw [second_fderiv_comp_with_acceleration hi.2.2.1 hi.2.2.2.1] at Hle
  have Habs := (abs_le.mp (bilinear_diag_sub_bound
    (secondJetPullback (fderiv ℝ (q i) (g i (x i)))
      (fderiv ℝ (fderiv ℝ (q i)) (g i (x i)))
      (fderiv ℝ (g i) (x i)) (fderiv ℝ (fderiv ℝ (g i)) (x i)))
    (secondJetPullback j₀ h₀ m₀ r₀) d)).1
  rw [dist_eq_norm
    (secondJetPullback (fderiv ℝ (q i) (g i (x i)))
      (fderiv ℝ (fderiv ℝ (q i)) (g i (x i)))
      (fderiv ℝ (g i) (x i)) (fderiv ℝ (fderiv ℝ (g i)) (x i)))
    (secondJetPullback j₀ h₀ m₀ r₀)] at hs
  have Hmul := mul_le_mul_of_nonneg_right hs.le (sq_nonneg ‖d‖)
  rw [secondJetPullback_apply] at Habs
  linarith only [Hle,Habs,Hmul]

end WeakMTWTransport

end

end OAI
