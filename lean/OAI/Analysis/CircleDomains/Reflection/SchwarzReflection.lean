import OAI.Analysis.CircleDomains.Reflection.HolomorphicAcrossRealAxis
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-! Schwarz reflection across a real interval, with continuity and
holomorphy proved for the actual piecewise extension. -/
open Set Function Complex Filter
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

def schwarzReflect (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0≤z.im then f z else conj (f (conj z))

lemma schwarzReflect_eq {f : ℂ → ℂ} {z : ℂ} (hz : 0≤z.im) :
    schwarzReflect f z=f z := ite_eq_left hz

lemma continuousOn_schwarzReflect {U : Set ℂ} {f : ℂ → ℂ}
    (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hr : ∀z∈U,z.im=0 → (f z).im=0) : ContinuousOn (schwarzReflect f) U := by
  have hg : ContinuousOn (fun z => conj (f (conj z))) (U∩{z : ℂ | z.im≤0}) := by
    apply continuous_conj.comp_continuousOn
    apply hc.comp continuous_conj.continuousOn
    intro z hz
    exact ⟨hs z hz.1,by simpa only [mem_ofPred_eq,conj_im,neg_nonneg] using hz.2⟩
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_if_le continuous_const (continuous_im.comp continuous_subtype_val)
  · exact hc.comp continuous_subtype_val.continuousOn (fun z hz => ⟨z.property,hz⟩)
  · exact hg.comp continuous_subtype_val.continuousOn (fun z hz => ⟨z.property,hz⟩)
  · intro z hz
    have hz0 : (z : ℂ).im=0 := hz.symm
    rw [(conj_eq_iff_im.mpr hz0),conj_eq_iff_im.mpr (hr z z.property hz0)]

lemma differentiableOn_schwarzReflect {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hr : ∀z∈U,z.im=0 → (f z).im=0) : DifferentiableOn ℂ (schwarzReflect f) U := by
  apply differentiableOn_of_continuousOn_off_real hU (continuousOn_schwarzReflect hs hc hr)
  intro z hz hn
  rcases lt_or_gt_of_ne hn with hneg|hpos
  · have heq : schwarzReflect f =ᶠ[𝓝 z] fun w => conj (f (conj w)) := by
      filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hneg] with w hw
      exact ite_eq_right (not_le_of_gt hw)
    apply heq.differentiableAt_iff.mpr
    apply differentiableAt_conj_conj_iff.mpr
    exact hd (conj z) (hs z hz) (by simpa only [conj_im,neg_pos] using hneg)
  · have heq : schwarzReflect f =ᶠ[𝓝 z] f := by
      filter_upwards [(isOpen_lt continuous_const continuous_im).mem_nhds hpos] with w hw
      exact ite_eq_left hw.le
    exact heq.differentiableAt_iff.mpr (hd z hz hpos)

lemma schwarzReflect_conj {U : Set ℂ} {f : ℂ → ℂ}
    (hr : ∀z∈U,z.im=0 → (f z).im=0) {z : ℂ} (hz : z∈U) :
    schwarzReflect f (conj z)=conj (schwarzReflect f z) := by
  by_cases hp : 0<z.im
  · simp [schwarzReflect,conj_im,hp.le,not_le_of_gt (neg_neg_of_pos hp)]
  · by_cases hn : z.im<0
    · simp [schwarzReflect,conj_im,hn.le,not_le_of_gt hn]
    · have hz0 : z.im=0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
      rw [conj_eq_iff_im.mpr hz0,schwarzReflect_eq hz0.ge,
        conj_eq_iff_im.mpr (hr z hz hz0)]

end CircleDomainRigidity

end

end OAI
