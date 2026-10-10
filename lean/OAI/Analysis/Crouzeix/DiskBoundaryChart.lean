import Mathlib
import OAI.Analysis.Crouzeix.ConvexCoordinates

namespace OAI

/-! Disk Boundary Chart. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

def localCayley (z : ℂ) : ℂ := (I - z) / (I + z)

@[simp] theorem localCayley_zero : localCayley 0 = 1 := by simp [localCayley]

theorem localCayley_injOn : InjOn localCayley {z | I + z ≠ 0} := by
  intro z hz w hw he
  have hm := (div_eq_div_iff hz hw).mp he
  have he' : (z - w) * (2 * I) = 0 := by linear_combination -hm
  exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right (mul_ne_zero (by norm_num) I_ne_zero))

theorem localCayley_norm_lt_one {z : ℂ} (hz : I + z ≠ 0) :
    ‖localCayley z‖ < 1 ↔ 0 < z.im := by
  rw [localCayley, norm_div, div_lt_one (norm_pos_iff.mpr hz)]
  have he : ‖I + z‖ ^ 2 - ‖I - z‖ ^ 2 = 4 * z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
    ring
  constructor <;> intro h <;> nlinarith [norm_nonneg (I + z), norm_nonneg (I - z)]

theorem localCayley_norm_le_one {z : ℂ} (hz : I + z ≠ 0) :
    ‖localCayley z‖ ≤ 1 ↔ 0 ≤ z.im := by
  rw [localCayley, norm_div, div_le_one (norm_pos_iff.mpr hz)]
  have he : ‖I + z‖ ^ 2 - ‖I - z‖ ^ 2 = 4 * z.im := by
    simp only [Complex.sq_norm, Complex.normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
    ring
  constructor <;> intro h <;> nlinarith [norm_nonneg (I + z), norm_nonneg (I - z)]

theorem analyticAt_localCayley {z : ℂ} (hz : I + z ≠ 0) :
    AnalyticAt ℂ localCayley z :=
  (analyticAt_const.sub analyticAt_id).div (analyticAt_const.add analyticAt_id) hz

theorem analyticOnNhd_symm (e : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ e e.source) : AnalyticOnNhd ℂ e.symm e.target := by
  apply DifferentiableOn.analyticOnNhd _ e.open_target
  intro z hz
  exact (e.hasStrictDerivAt_symm hz
    (deriv_ne_zero_of_injOn e.open_source he.differentiableOn e.injOn (e.map_target hz))
    (he _ (e.map_target hz)).hasStrictDerivAt).hasDerivAt.differentiableAt.differentiableWithinAt

theorem closure_image_subdisk {h : ℂ → ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hh : ContinuousOn h (ball 0 R)) :
    closure (h '' ball 0 r) = h '' closedBall 0 r := by
  have hc : ContinuousOn h (closedBall 0 r) := hh.mono (closedBall_subset_ball hrR)
  apply Subset.antisymm
  · apply closure_minimal (image_mono ball_subset_closedBall)
    exact ((isCompact_closedBall (0 : ℂ) r).image_of_continuousOn hc).isClosed
  · have hcl : closure (ball (0 : ℂ) r) = closedBall 0 r := closure_ball _ hr.ne'
    rw [← hcl] at hc ⊢
    exact hc.image_closure

theorem boundaryChart_image_subdisk {h : ℂ → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn h (ball 0 R)) {p : ℂ} (hp : p ∈ frontier (h '' ball 0 r)) :
    Nonempty (BoundaryChart (h '' ball 0 r) p) := by
  have hclosed := closure_image_subdisk hr hrR hh.continuousOn
  have hopen := isOpen_image_of_univalent isOpen_ball (hh.mono (ball_subset_ball hrR.le))
    (hi.mono (ball_subset_ball hrR.le))
  obtain ⟨v, hv, rfl⟩ := hclosed ▸ hp.1
  have hvn : ‖v‖ = r := by
    apply le_antisymm (mem_closedBall_zero_iff.mp hv)
    by_contra hn
    have hvb : v ∈ ball 0 r := mem_ball_zero_iff.mpr (lt_of_not_ge hn)
    exact hp.2 (by rw [hopen.interior_eq]; exact ⟨v, hvb, rfl⟩)
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (hvn ▸ hr.ne')
  have hvR : v ∈ ball 0 R := (closedBall_subset_ball hrR) hv
  let N : Set ℂ := {z | I + z ≠ 0} ∩ {z | v * localCayley z ∈ ball 0 R}
  have hNo : IsOpen N := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact inter_mem
      ((continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
        (isClosed_singleton.isOpen_compl.mem_nhds hz.1))
      ((continuousAt_const.mul (analyticAt_localCayley hz.1).continuousAt).preimage_mem_nhds
        (isOpen_ball.mem_nhds hz.2))
  have hN0 : (0 : ℂ) ∈ N := by
    simp only [N, mem_inter_iff, mem_ofPred_eq, add_zero, localCayley_zero, mul_one]
    exact ⟨I_ne_zero, hvR⟩
  let χ : ℂ → ℂ := fun z => h (v * localCayley z)
  have hχa : AnalyticOnNhd ℂ χ N := by
    intro z hz
    have hc : AnalyticAt ℂ (fun w => v * localCayley w) z :=
      analyticAt_const.mul (analyticAt_localCayley hz.1)
    exact (hh _ hz.2).comp (f := fun w => v * localCayley w) (x := z) hc
  have hχi : InjOn χ N := by
    intro z hz w hw he
    exact localCayley_injOn hz.1 hw.1 (mul_left_cancel₀ hv0 (hi hz.2 hw.2 he))
  let d := (hχa 0 hN0).hasStrictDerivAt.hasStrictFDerivAt_equiv
    (deriv_ne_zero_of_injOn hNo hχa.differentiableOn hχi hN0)
  let e := (d.toOpenPartialHomeomorph χ).restrOpen N hNo
  have heN : e.source ⊆ N := inter_subset_right
  have hea : AnalyticOnNhd ℂ e e.source := hχa.mono heN
  have he0 : (0 : ℂ) ∈ e.source := ⟨d.mem_toOpenPartialHomeomorph_source, hN0⟩
  refine ⟨⟨e, he0, ?_, hea, analyticOnNhd_symm e hea, ?_, ?_⟩⟩
  · change h (v * localCayley 0) = h v
    simp only [localCayley_zero, mul_one]
  · intro z hz
    have hzN := heN hz
    have hm : h (v * localCayley z) ∈ h '' ball 0 r ↔ v * localCayley z ∈ ball 0 r := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact hi ((ball_subset_ball hrR.le) hw) hzN.2 he ▸ hw
      · exact fun hw => ⟨_, hw, rfl⟩
    change h (v * localCayley z) ∈ h '' ball 0 r ↔ _
    rw [hm, mem_ball_zero_iff, norm_mul, hvn, mul_lt_iff_lt_one_right hr]
    exact localCayley_norm_lt_one hzN.1
  · intro z hz
    have hzN := heN hz
    have hm : h (v * localCayley z) ∈ h '' closedBall 0 r ↔ v * localCayley z ∈ closedBall 0 r := by
      constructor
      · rintro ⟨w, hw, he⟩
        exact hi ((closedBall_subset_ball hrR) hw) hzN.2 he ▸ hw
      · exact fun hw => ⟨_, hw, rfl⟩
    change h (v * localCayley z) ∈ closure (h '' ball 0 r) ↔ _
    rw [hclosed, hm, mem_closedBall_zero_iff, norm_mul, hvn, mul_le_iff_le_one_right hr]
    exact localCayley_norm_le_one hzN.1

end CrouzeixHilbert.Conformal

end

end OAI
