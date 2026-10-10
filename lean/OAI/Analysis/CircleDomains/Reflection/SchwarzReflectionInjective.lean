import OAI.Analysis.CircleDomains.Reflection.SchwarzReflection
import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative

namespace OAI

/-! Reflection preserves injectivity when the original upper-side map
is injective and preserves the strict side of the boundary. -/
open Set Function Complex
open scoped Topology ComplexConjugate
noncomputable section
namespace CircleDomainRigidity

lemma schwarzReflect_upper_iff {U : Set ℂ} {f : ℂ → ℂ}
    (hs : ∀z∈U,conj z∈U)
    (hr : ∀z∈U,z.im=0 → (f z).im=0)
    (hp : ∀z∈U,0<z.im → 0<(f z).im) {z : ℂ} (hz : z∈U) :
    0≤(schwarzReflect f z).im ↔ 0≤z.im := by
  by_cases h : 0≤z.im
  · rw [schwarzReflect_eq h]
    refine iff_of_true ?_ h
    rcases eq_or_lt_of_le h with he|he
    · exact (hr z hz he.symm).ge
    · exact (hp z hz he).le
  · have hn : z.im<0 := lt_of_not_ge h
    have hc : 0<(f (conj z)).im := hp (conj z) (hs z hz) (by simpa using neg_pos.mpr hn)
    simp only [schwarzReflect,ite_eq_right h,conj_im,neg_nonneg]
    exact iff_of_false (not_le_of_gt hc) h

lemma injOn_schwarzReflect {U : Set ℂ} {f : ℂ → ℂ}
    (hs : ∀z∈U,conj z∈U)
    (hi : InjOn f (U∩{z : ℂ | 0≤z.im}))
    (hr : ∀z∈U,z.im=0 → (f z).im=0)
    (hp : ∀z∈U,0<z.im → 0<(f z).im) : InjOn (schwarzReflect f) U := by
  intro z hz w hw he
  have hside : (0≤z.im) ↔ (0≤w.im) := by
    rw [←schwarzReflect_upper_iff hs hr hp hz,←schwarzReflect_upper_iff hs hr hp hw,he]
  by_cases hzu : 0≤z.im
  · have hwu := hside.mp hzu
    rw [schwarzReflect_eq hzu,schwarzReflect_eq hwu] at he
    exact hi ⟨hz,hzu⟩ ⟨hw,hwu⟩ he
  · have hwu : ¬0≤w.im := fun h => hzu (hside.mpr h)
    have hzcu : 0≤(conj z).im := by simpa only [conj_im,neg_nonneg] using (lt_of_not_ge hzu).le
    have hwcu : 0≤(conj w).im := by simpa only [conj_im,neg_nonneg] using (lt_of_not_ge hwu).le
    simp only [schwarzReflect,ite_eq_right hzu,ite_eq_right hwu] at he
    have he' : f (conj z)=f (conj w) := (starRingEnd ℂ).injective he
    have hzw := hi ⟨hs z hz,hzcu⟩ ⟨hs w hw,hwcu⟩ he'
    simpa only [map_star,starRingEnd_apply,star_star] using congrArg conj hzw

lemma schwarzReflect_deriv_ne_zero {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hs : ∀z∈U,conj z∈U)
    (hc : ContinuousOn f (U∩{z : ℂ | 0≤z.im}))
    (hd : ∀z∈U,0<z.im → DifferentiableAt ℂ f z)
    (hi : InjOn f (U∩{z : ℂ | 0≤z.im}))
    (hr : ∀z∈U,z.im=0 → (f z).im=0)
    (hp : ∀z∈U,0<z.im → 0<(f z).im) :
    ∀z∈U,deriv (schwarzReflect f) z≠0 :=
  fun _ hz => holomorphicInjOn_deriv_ne_zero hU
    (differentiableOn_schwarzReflect hU hs hc hd hr) (injOn_schwarzReflect hs hi hr hp) hz

end CircleDomainRigidity

end

end OAI
