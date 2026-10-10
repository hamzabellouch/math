import OAI.Analysis.CircleDomains.Reflection.UnitCircleIdentityGerm
import OAI.Analysis.CircleDomains.Uniformization.MarkedJointPhaseLimit

namespace OAI

/-! An injective exterior collar cannot have a zero-radius circular
boundary after holomorphic reflection. -/
open Set Function Filter Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma circle_radius_pos_of_injective_outer {R ρ:ℝ} {F:ℂ→ℂ} {a:ℂ}
    (hR:1<R) (hρ:0≤ρ) (hd:DifferentiableOn ℂ F (symmetricCircleAnnulus R))
    (hi:InjOn F (symmetricCircleAnnulus R∩{z | 1<‖z‖}))
    (hc:∀z∈symmetricCircleAnnulus R,‖z‖=1 → ‖F z-a‖=ρ) : 0<ρ := by
  by_contra hpos
  have hzero : ρ=0 := le_antisymm (le_of_not_gt hpos) hρ
  have hconst : ∀ᶠz in 𝓝 (1:ℂ),F z=a :=
    unit_circle_identity_germ (isOpen_symmetricCircleAnnulus R)
      (unit_circle_subset_symmetricCircleAnnulus hR) hd (by
        intro z hz hz1
        have he := hc z hz hz1
        rw [hzero,norm_eq_zero,sub_eq_zero] at he
        exact he)
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hconst
  let δ := min (ε/4) ((R-1)/4)
  have hδ : 0<δ := lt_min (by linarith) (by linarith)
  have hδε : δ≤ε/4 := min_le_left _ _
  have hδR : δ≤(R-1)/4 := min_le_right _ _
  have point (t:ℝ) (ht:0<t) (htε:t<ε) (htR:t<R-1) :
      (((1+t:ℝ):ℂ)∈symmetricCircleAnnulus R∩{z | 1<‖z‖}) ∧ F ((1+t:ℝ):ℂ)=a := by
    have hn : ‖((1+t:ℝ):ℂ)‖=1+t := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    have hInv : R⁻¹<1 := (inv_lt_one₀ (zero_lt_one.trans hR)).mpr hR
    refine ⟨⟨?_,?_⟩,?_⟩
    · change R⁻¹<‖((1+t:ℝ):ℂ)‖ ∧ ‖((1+t:ℝ):ℂ)‖<R
      rw [hn]
      constructor <;> linarith
    · change 1<‖((1+t:ℝ):ℂ)‖
      rw [hn]
      linarith
    · apply hεsub
      rw [mem_ball,dist_eq_norm]
      have he : ((1+t:ℝ):ℂ)-1=(t:ℂ) := by push_cast;ring
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
      exact htε
  obtain ⟨hp,hpa⟩ := point δ hδ (by linarith) (by linarith)
  obtain ⟨hq,hqa⟩ := point (2*δ) (by linarith) (by linarith) (by linarith)
  have he := hi hp hq (hpa.trans hqa.symm)
  have hreal := Complex.ofReal_injective he
  linarith

end CircleDomainRigidity

end

end OAI
