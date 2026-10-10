import OAI.Analysis.CircleDomains.Reflection.HolomorphicBoundaryInjectivity

namespace OAI

/-! Interior injectivity suffices for the constructed Schwarz reflection.
The open mapping argument gives boundary injectivity and hence the
nonvanishing boundary derivative. -/
open Set Function Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma schwarzReflect_strict_upper_iff {U : Set ℂ} {f : ℂ → ℂ}
    (hs : ∀z∈U,conj z∈U)
    (hr : ∀z∈U,z.im=0 → (f z).im=0)
    (hp : ∀z∈U,0<z.im → 0<(f z).im) {z : ℂ} (hz : z∈U) :
    0<(schwarzReflect f z).im ↔ 0<z.im := by
  by_cases hzpos : 0<z.im
  · rw [schwarzReflect_eq hzpos.le]
    exact iff_of_true (hp z hz hzpos) hzpos
  · have hzn : z.im≤0 := le_of_not_gt hzpos
    by_cases hz0 : z.im=0
    · rw [schwarzReflect_eq hz0.ge,hr z hz hz0]
      exact iff_of_false (lt_irrefl _) hzpos
    · have hzneg : z.im<0 := lt_of_le_of_ne hzn hz0
      have hcp := hp (conj z) (hs z hz) (by simpa only [conj_im,neg_pos] using hzneg)
      simp only [schwarzReflect,ite_eq_right (not_le_of_gt hzneg),conj_im]
      exact iff_of_false (by linarith) hzpos

lemma injOn_schwarzReflect_of_injOn_upper {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hi : InjOn f (U∩{z : ℂ | 0<z.im}))
    (hr : ∀z∈U,z.im=0 → (f z).im=0)
    (hp : ∀z∈U,0<z.im → 0<(f z).im) : InjOn (schwarzReflect f) U := by
  have hFd := differentiableOn_schwarzReflect hU hs hc hd hr
  have hFp : ∀z∈U,0<(schwarzReflect f z).im ↔ 0<z.im :=
    fun _ hz => schwarzReflect_strict_upper_iff hs hr hp hz
  have hFr : ∀z∈U,z.im=0 → (schwarzReflect f z).im=0 := by
    intro z hz hz0
    rw [schwarzReflect_eq hz0.ge,hr z hz hz0]
  have hFi : InjOn (schwarzReflect f) (U∩{z : ℂ | 0<z.im}) := by
    intro z hz w hw he
    rw [schwarzReflect_eq (show 0<z.im from hz.2).le,
      schwarzReflect_eq (show 0<w.im from hw.2).le] at he
    exact hi hz hw he
  have hclosed := holomorphic_injOn_upperClosed hU hFd hFp hFr hFi
  have hic : InjOn f (U∩{z : ℂ | 0≤z.im}) := by
    intro z hz w hw he
    apply hclosed hz hw
    rwa [schwarzReflect_eq hz.2,schwarzReflect_eq hw.2]
  exact injOn_schwarzReflect hs hic hr hp

lemma schwarzReflect_deriv_ne_zero_of_injOn_upper {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hi : InjOn f (U∩{z : ℂ | 0<z.im}))
    (hr : ∀z∈U,z.im=0 → (f z).im=0)
    (hp : ∀z∈U,0<z.im → 0<(f z).im) :
    ∀z∈U,deriv (schwarzReflect f) z≠0 :=
  fun _ hz => holomorphicInjOn_deriv_ne_zero hU
    (differentiableOn_schwarzReflect hU hs hc hd hr)
    (injOn_schwarzReflect_of_injOn_upper hU hs hc hd hi hr hp) hz

end CircleDomainRigidity

end

end OAI
