import OAI.Analysis.CircleDomains.Topology.SymmetricCircleAnnulus

namespace OAI

/-! Two distinct points in the exterior half of a symmetric circle collar. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

lemma symmetricCircleAnnulus_outer_nontrivial {R:ℝ} (hR:1<R) :
    (symmetricCircleAnnulus R∩{z:ℂ | 1<‖z‖}).Nontrivial := by
  let δ := (R-1)/4
  have hδ : 0<δ := by dsimp [δ];linarith
  have hm (t:ℝ) (ht:0<t) (htR:t<R-1) :
      ((1+t:ℝ):ℂ)∈symmetricCircleAnnulus R∩{z:ℂ | 1<‖z‖} := by
    have hn : ‖((1+t:ℝ):ℂ)‖=1+t := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    have hInv : R⁻¹<1 := (inv_lt_one₀ (zero_lt_one.trans hR)).mpr hR
    change (R⁻¹<‖((1+t:ℝ):ℂ)‖ ∧ ‖((1+t:ℝ):ℂ)‖<R) ∧ 1<‖((1+t:ℝ):ℂ)‖
    rw [hn]
    exact ⟨⟨by linarith,by linarith⟩,by linarith⟩
  refine ⟨((1+δ:ℝ):ℂ),hm δ hδ (by dsimp [δ];linarith),
    ((1+2*δ:ℝ):ℂ),hm (2*δ) (by linarith) (by dsimp [δ];linarith),?_⟩
  intro he
  have := Complex.ofReal_injective he
  linarith

lemma not_constant_of_injective_outer_annulus {R:ℝ} {f:ℂ→ℂ} (hR:1<R)
    (hi:InjOn f (symmetricCircleAnnulus R∩{z | 1<‖z‖})) :
    ¬∃a:ℂ,∀z∈symmetricCircleAnnulus R,f z=a := by
  rintro ⟨a,ha⟩
  obtain ⟨z,hz,w,hw,hne⟩ := symmetricCircleAnnulus_outer_nontrivial hR
  exact hne (hi hz hw ((ha z hz.1).trans (ha w hw.1).symm))

end CircleDomainRigidity

end

end OAI
