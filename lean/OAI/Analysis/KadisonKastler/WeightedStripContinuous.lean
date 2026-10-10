import OAI.Analysis.KadisonKastler.WeightedStripKernel
import OAI.Analysis.KadisonKastler.ContinuousMapHolomorphic

namespace OAI

/-! # The weighted strip as a holomorphic continuous spectral function -/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private theorem weightedStripKernel_continuous_s {z : ℂ} (hz : |z.re| < 1) :
    Continuous (weightedStripKernel z) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (weightedStripKernel_continuousAt (s := s) hz).comp
    (by fun_prop : ContinuousAt (fun t : ℝ => (z, t)) s)

def weightedStripContinuous (r : C(K, ℝ)) (z : ℂ) : C(K, ℂ) :=
  if hz : |z.re| < 1 then
    ⟨fun k => weightedStripKernel z (r k), (weightedStripKernel_continuous_s hz).comp r.continuous⟩
  else 0

omit [CompactSpace K] in
theorem weightedStripContinuous_apply (r : C(K, ℝ)) {z : ℂ} (hz : |z.re| < 1) (k : K) :
    weightedStripContinuous r z k = weightedStripKernel z (r k) := by
  simp only [weightedStripContinuous, dite_eq_left hz, ContinuousMap.coe_mk]

omit [CompactSpace K] in
theorem weightedStripContinuous_continuousOn (r : C(K, ℝ)) :
    ContinuousOn (weightedStripContinuous r) {z : ℂ | |z.re| < 1} := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  intro p hp
  have hp' : |p.1.re| < 1 := hp.1
  have hc : ContinuousAt (fun q : ℂ × K => weightedStripKernel q.1 (r q.2)) p :=
    (weightedStripKernel_continuousAt hp').comp_of_eq
      (continuous_fst.prodMk (r.continuous.comp continuous_snd)).continuousAt rfl
  have hn : ∀ᶠ q : ℂ × K in 𝓝 p, |q.1.re| < 1 := by
    exact ((isOpen_lt (Complex.continuous_re.comp continuous_fst).abs
      continuous_const).mem_nhds hp')
  have he : (fun q : ℂ × K => weightedStripContinuous r q.1 q.2) =ᶠ[𝓝 p]
      (fun q => weightedStripKernel q.1 (r q.2)) :=
    hn.mono (fun q hq => weightedStripContinuous_apply r hq q.2)
  exact (hc.congr_of_eventuallyEq he).continuousWithinAt

theorem weightedStripContinuous_differentiableOn (r : C(K, ℝ)) :
    DifferentiableOn ℂ (weightedStripContinuous r) {z : ℂ | |z.re| < 1} := by
  apply continuousMap_differentiableOn_of_evaluations _
    (isOpen_lt Complex.continuous_re.abs continuous_const)
    (weightedStripContinuous_continuousOn r)
  intro k z hz
  have hn : ∀ᶠ w in 𝓝 z, |w.re| < 1 :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds hz
  have he : (fun w => weightedStripContinuous r w k) =ᶠ[𝓝 z]
      (fun w => weightedStripKernel w (r k)) :=
    hn.mono (fun w hw => weightedStripContinuous_apply r hw k)
  exact ((weightedStripKernel_differentiableAt (r k) hz).congr_of_eventuallyEq he).differentiableWithinAt

theorem weightedStripContinuous_norm_le (r : C(K, ℝ))
    (hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1) {z : ℂ} (hz : |z.re| ≤ 1 / 2) :
    ‖weightedStripContinuous r z‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro k
  rw [weightedStripContinuous_apply r (lt_of_le_of_lt hz (by norm_num))]
  exact weightedStripKernel_norm_le_one hz (hr k).1 (hr k).2

end

end KadisonKastler

end OAI
