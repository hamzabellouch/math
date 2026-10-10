import OAI.Analysis.CircleDomains.Uniformization.AnalyticCapShrink
import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothExtension

namespace OAI

/-! Round one analytic Jordan cap by an actual compactly supported smooth
plane diffeomorphism inside any prescribed open neighborhood. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_smooth_analytic_cap_rounding {H : ℂ ≃ₜ ℂ} (ha : IsAnalyticJordanCap H)
    {O : Set ℂ} (hO : IsOpen O) (hHO : closure (jordanInterior H)⊆O) :
    ∃ (G : ℂ ≃ₜ ℂ) (c : ℂ) (r : ℝ),0<r ∧
      ContDiff ℝ ∞ (G : ℂ → ℂ) ∧ ContDiff ℝ ∞ (G.symm : ℂ → ℂ) ∧
      (∀z∉O,G z=z) ∧ G '' closure (jordanInterior H)=closedBall c r := by
  obtain ⟨β,S,K,hS,hDS,hβ,hi,hK,hKO,hclosed,hshrink⟩ := exists_analytic_cap_shrinker ha hO hHO
  have hzero : (0:ℂ)∈S := hDS (mem_closedBall_self zero_le_one)
  let d := deriv β 0
  have hd : d≠0 := holomorphicInjOn_deriv_ne_zero hS hβ hi hzero
  have hdn : 0<‖d‖ := norm_pos_iff.mpr hd
  let L : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ d hd).trans (Homeomorph.addRight (β 0))
  have hL (z : ℂ) : L z=d*z+β 0 := rfl
  have hLi (z : ℂ) : L.symm z=(z-β 0)/d := by
    apply L.injective
    rw [L.apply_symm_apply,hL,mul_div_cancel₀ _ hd,sub_add_cancel]
  have hLs : ContDiff ℝ ∞ (L : ℂ → ℂ) := contDiff_const.mul contDiff_id |>.add contDiff_const
  have hLis : ContDiff ℝ ∞ (L.symm : ℂ → ℂ) := by
    have he : (L.symm : ℂ → ℂ)=(fun z => (z-β 0)/d) := funext hLi
    rw [he]
    exact (contDiff_id.sub contDiff_const).div_const d
  let f : ℂ → ℂ := fun z => (β z-β 0)/d-z
  have hβs : ContDiffOn ℝ ∞ β S := holomorphicPlaneChart_smooth hS hβ hi
  have hfs : ContDiffOn ℝ ∞ f S :=
    ((hβs.sub contDiffOn_const).div_const d).sub contDiffOn_id
  have hf0 : f 0=0 := by simp [f]
  have hdf : HasDerivAt f 0 0 := by
    have hb := ((hβ 0 hzero).differentiableAt (hS.mem_nhds hzero)).hasDerivAt
    have hh := ((hb.sub_const (β 0)).div_const d).sub (hasDerivAt_id (0:ℂ))
    convert hh using 1 <;> simp [f,d,div_self hd]
    rfl
  have hdf0 : fderiv ℝ f 0=0 := by
    rw [(hdf.hasFDerivAt.restrictScalars ℝ).fderiv]
    ext z
    simp
  have hcO : β 0∈O := hHO (hclosed ▸ mem_image_of_mem β (mem_closedBall_self zero_le_one))
  obtain ⟨ρ,hρ,hρO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hcO)
  let ε := min 1 (ρ/‖d‖)
  have hε : 0<ε := lt_min zero_lt_one (div_pos hρ hdn)
  obtain ⟨t,ht,htε,Q,hQs,hQis,hQin,hQout⟩ :=
    exists_smooth_local_error_extension hS hzero hfs hf0 hdf0 hε
  have ht1 : t≤1 := by dsimp [ε] at htε;linarith [min_le_left (1:ℝ) (ρ/‖d‖)]
  obtain ⟨T,hTs,hTis,hTout,hTimage⟩ := hshrink t ht ht1
  let P := L.symm.trans (Q.trans L)
  have hPs : ContDiff ℝ ∞ (P : ℂ → ℂ) := hLs.comp (hQs.comp hLis)
  have hPis : ContDiff ℝ ∞ (P.symm : ℂ → ℂ) := hLs.comp (hQis.comp hLis)
  have hPout (z : ℂ) (hz : z∉O) : P z=z := by
    have hdist : ρ≤‖z-β 0‖ := le_of_not_gt (fun hh => hz (hρO (mem_ball_iff_norm.mpr hh)))
    have hnorm : ‖z-β 0‖=‖d‖*‖L.symm z‖ := by
      have he := hL (L.symm z)
      rw [L.apply_symm_apply] at he
      calc
        ‖z-β 0‖=‖d*L.symm z‖ := by congr 1;linear_combination he
        _=‖d‖*‖L.symm z‖ := norm_mul _ _
    have hsmall : 2*t<ρ/‖d‖ := htε.trans_le (min_le_right _ _)
    have hlarge : 2*t≤‖L.symm z‖ := by
      rw [lt_div_iff₀ hdn] at hsmall
      nlinarith
    change L (Q (L.symm z))=z
    rw [hQout _ hlarge,L.apply_symm_apply]
  have hPimage : P '' (L '' closedBall 0 t)=β '' closedBall 0 t := by
    rw [image_image]
    apply image_congr
    intro z hz
    change L (Q (L.symm (L z)))=β z
    rw [L.symm_apply_apply,hQin z hz,hL]
    dsimp [f]
    field_simp
    ring
  have hLimage : L '' closedBall 0 t=closedBall (β 0) (‖d‖*t) := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      apply mem_closedBall_iff_norm.mpr
      rw [hL,add_sub_cancel_right,norm_mul]
      exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hdn.le
    · intro z hz
      refine ⟨L.symm z,?_,L.apply_symm_apply z⟩
      apply mem_closedBall_zero_iff.mpr
      have hh : ‖z-β 0‖=‖d‖*‖L.symm z‖ := by
        conv_lhs => rw [←L.apply_symm_apply z,hL,add_sub_cancel_right,norm_mul]
      rw [mem_closedBall_iff_norm,hh] at hz
      nlinarith
  refine ⟨T.trans P.symm,β 0,‖d‖*t,mul_pos hdn ht,hPis.comp hTs,hTis.comp hPs,?_,?_⟩
  · intro z hz
    change P.symm (T z)=z
    rw [hTout z (fun h => hz (hKO h))]
    exact homeomorph_symm_eq_of_fixed (hPout z hz)
  · change (P.symm ∘ T) '' closure (jordanInterior H)=_
    rw [image_comp,hTimage,←hPimage,image_image]
    simpa only [P.symm_apply_apply,image_id'] using hLimage

end CircleDomainRigidity

end

end OAI
