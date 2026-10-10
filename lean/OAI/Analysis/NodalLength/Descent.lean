import OAI.Analysis.NodalLength.Subdivision

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma profile_zero_of_inner_rate {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x ≤ 0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0<S j)
    (hinner : Tendsto (fun j =>logRate (S j)
      (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))) atTop (𝓝 0)) :
    ∀x∈Metric.ball (0:Plane) 1000,V x=0 := by
  have hsub : Metric.closedBall (0:Plane) 1 ⊆ Metric.ball 0 1000 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨a,ha,hmax⟩ := (hV.upperSemicontinuousOn (Metric.closedBall 0 1)).exists_isMaxOn
    ⟨0,Metric.mem_closedBall_self (by norm_num)⟩ (isCompact_closedBall 0 1)
  have hu := hp.upper 0 continuousOn_const _ (isCompact_closedBall 0 1) hsub
  have hl := limsup_le_limsup (f := atTop) (Eventually.of_forall (fun j =>
    logRate_mono (hS j) (tiltedMass_mono_set (S j) (B j) (U j) (d j) 0 (Metric.ball_subset_closedBall (x := (0:Plane)) (ε := 1)))))
  rw [hinner.limsup_eq] at hl
  have hmax' : (⨆x∈Metric.closedBall (0:Plane) 1,V x+(0:EReal)) ≤ V a :=
    iSup₂_le (fun x hx =>by simpa using hmax hx)
  have ha0 : V a=0 := le_antisymm (hneg a (hsub ha)) (hl.trans (hu.trans (by simpa using hmax')))
  exact profile_strong_maximum Metric.isOpen_ball (convex_ball (0:Plane) 1000).isPreconnected
    hV hneg htest (hsub ha) ha0

lemma tiltedMass_linear_centered (S : ℝ) (B e : Plane) (U : Plane → ℝ) {d : ℝ}
    (hd : 0 ≤ d) (r : ℝ) :
    tiltedMass S B U d (fun x =>inner ℝ e x) (Metric.ball 0 r)=
      ENNReal.ofReal d*centeredMass (B-S • e) U 0 r := by
  simpa only [sub_zero,inner_neg_left,neg_neg,inner_zero_right,mul_zero,neg_zero,
    Real.exp_zero,mul_one,smul_neg,← sub_eq_add_neg] using
    tiltedMass_centered S B (-e) U d hd 0 r

lemma zero_profile_forces_growth {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hzero : ∀x∈Metric.ball (0:Plane) 1000,V x=0)
    (hS : ∀j,0<S j) (hd : ∀j,0<d j)
    (hm0 : ∀j,centeredMass (B j) (U j) 0 1≠0)
    (hmt : ∀j,centeredMass (B j) (U j) 0 1000≠⊤)
    {e : Plane} (he : ‖e‖=1) :
    ∀ᶠj in atTop, 1 <
      massExcess (centeredMass (B j-S j • e) (U j) 0 1000)
        (centeredMass (B j-S j • e) (U j) 0 1)/S j := by
  let f : Plane → ℝ := fun x => inner ℝ e x
  have hf : Continuous f := continuous_const.inner continuous_id
  have hF : Metric.closedBall (0:Plane) 1 ⊆ Metric.ball 0 1000 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hG : Metric.ball (0:Plane) 4 ⊆ Metric.ball 0 1000 :=
    Metric.ball_subset_ball (by norm_num)
  have hu := hp.upper f hf.continuousOn _ (isCompact_closedBall 0 1) hF
  have hl := hp.lower f hf.continuousOn _ Metric.isOpen_ball hG
  have hup : (⨆x∈Metric.closedBall (0:Plane) 1,V x+(f x:EReal)) ≤ (1:EReal) := by
    apply iSup₂_le
    intro x hx
    rw [hzero x (hF hx),zero_add]
    apply EReal.coe_le_coe_iff.mpr
    have hh : ‖x‖ ≤ 1 := by simpa using hx
    calc
      inner ℝ e x ≤ ‖e‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ 1 := by simpa [he] using hh
  have hlow : (3:EReal) ≤ (⨆x∈Metric.ball (0:Plane) 4,V x+(f x:EReal)) := by
    have hx : (3:ℝ) • e∈Metric.ball (0:Plane) 4 := by
      norm_num [Metric.mem_ball,norm_smul,dist_zero_right,he]
    apply le_iSup₂_of_le ((3:ℝ) • e) hx
    rw [hzero _ (hG hx),zero_add]
    have hval : f ((3:ℝ) • e)=3 := by
      simp only [f,inner_smul_right,real_inner_self_eq_norm_sq,he,one_pow,mul_one]
    rw [hval]
    rfl
  have huu := eventually_lt_of_limsup_lt ((hu.trans hup).trans_lt (EReal.coe_lt_coe_iff.mpr (by norm_num : (1:ℝ) < 3/2)))
  have hll := eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.mpr (by norm_num : (5/2:ℝ) < 3)).trans_le (hlow.trans hl))
  filter_upwards [huu,hll] with j hjU hjL
  let T : Plane := B j-S j • e
  let a := tiltedMass (S j) (B j) (U j) (d j) f (Metric.ball 0 1000)
  let b := tiltedMass (S j) (B j) (U j) (d j) f (Metric.ball 0 1)
  have hbU : logRate (S j) b<((3/2:ℝ):EReal) :=
    (logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ Metric.ball_subset_closedBall)).trans_lt hjU
  have haL : ((5/2:ℝ):EReal)<logRate (S j) a := hjL.trans_le
    (logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ (Metric.ball_subset_ball (by norm_num))))
  have hT0 : centeredMass T (U j) 0 1≠0 := centeredMass_ne_zero_of (hm0 j)
  have hTt : centeredMass T (U j) 0 1000≠⊤ := centeredMass_ne_top_of (hmt j)
  have hab := centeredMass_mono T (U j) 0 (show (1:ℝ) ≤ 1000 by norm_num)
  have ha0 : a≠0 := by
    rw [show a=ENNReal.ofReal (d j)*centeredMass T (U j) 0 1000 from
      tiltedMass_linear_centered _ _ _ _ (hd j).le _]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (hd j))
      (ne_of_gt ((pos_iff_ne_zero.mpr hT0).trans_le hab))
  have hat : a≠⊤ := by
    rw [show a=ENNReal.ofReal (d j)*centeredMass T (U j) 0 1000 from
      tiltedMass_linear_centered _ _ _ _ (hd j).le _]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTt
  have hb0 : b≠0 := by
    rw [show b=ENNReal.ofReal (d j)*centeredMass T (U j) 0 1 from
      tiltedMass_linear_centered _ _ _ _ (hd j).le _]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (hd j)) hT0
  have hbt : b≠⊤ := ne_top_of_le_ne_top hat
    (tiltedMass_mono_set _ _ _ _ _ (Metric.ball_subset_ball (by norm_num)))
  rw [logRate_real ha0 hat] at haL
  rw [logRate_real hb0 hbt] at hbU
  have hexc : 1 < massExcess a b/S j := by
    rw [massExcess_div (hS j).ne' ha0 hat hb0 hbt]
    have h1 := EReal.coe_lt_coe_iff.mp haL
    have h2 := EReal.coe_lt_coe_iff.mp hbU
    linarith
  have heq : massExcess a b=massExcess (centeredMass T (U j) 0 1000) (centeredMass T (U j) 0 1) := by
    dsimp only [a,b,f]
    rw [tiltedMass_linear_centered _ _ _ _ (hd j).le,tiltedMass_linear_centered _ _ _ _ (hd j).le]
    exact massExcess_mul_left _ _ _ (ENNReal.ofReal_ne_zero_iff.mpr (hd j)) ENNReal.ofReal_ne_top
  rw [heq] at hexc
  exact hexc

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma zero_profile_tilt_contradiction {V : Plane → EReal} {S d : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hzero : ∀x∈Metric.ball (0:Plane) 1000,V x=0)
    (hS : ∀j,0<S j) (hd : ∀j,0<d j) (hB : ∀j,‖B j‖=S j)
    (hm0 : ∀j,centeredMass (B j) (U j) 0 1≠0)
    (hmt : ∀j,centeredMass (B j) (U j) 0 1000≠⊤)
    (hsmall : Tendsto (fun j =>massExcess (centeredMass 0 (U j) 0 1000)
      (centeredMass 0 (U j) 0 1)/S j) atTop (𝓝 0)) : False := by
  let e : ℕ → Plane := fun j =>(S j)⁻¹ • B j
  have henorm (j : ℕ) : ‖e j‖=1 := by
    simp [e,norm_smul,Real.norm_eq_abs,abs_of_pos (hS j),hB,inv_mul_cancel₀ (hS j).ne']
  obtain ⟨v,_hv,φ,hφ,hlim⟩ := (isCompact_closedBall (0:Plane) 1).tendsto_subseq
    (fun j =>show e j∈Metric.closedBall (0:Plane) 1 by simp [Metric.mem_closedBall,dist_zero_right,henorm])
  have hvnorm : ‖v‖=1 := tendsto_nhds_unique hlim.norm
    (by simpa only [Function.comp_apply,henorm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ =>(1:ℝ)) atTop (𝓝 1)))
  have hgrowth := zero_profile_forces_growth (hp.subseq hφ.tendsto_atTop) hzero
    (fun j =>hS (φ j)) (fun j =>hd (φ j)) (fun j =>hm0 (φ j)) (fun j =>hmt (φ j)) hvnorm
  have hres (j : ℕ) : ‖B (φ j)-S (φ j) • v‖=S (φ j)*‖e (φ j)-v‖ := by
    rw [show B (φ j)-S (φ j) • v=S (φ j) • (e (φ j)-v) by
      simp [e,smul_sub,smul_inv_smul₀ (hS (φ j)).ne'],norm_smul,
      Real.norm_eq_abs,abs_of_pos (hS (φ j))]
  have hupper (j : ℕ) :
      massExcess (centeredMass (B (φ j)-S (φ j) • v) (U (φ j)) 0 1000)
        (centeredMass (B (φ j)-S (φ j) • v) (U (φ j)) 0 1)/S (φ j) ≤
      massExcess (centeredMass 0 (U (φ j)) 0 1000)
        (centeredMass 0 (U (φ j)) 0 1)/S (φ j)+1001*‖e (φ j)-v‖ := by
    have hh := centered_excess_weight_bound (T:=B (φ j)-S (φ j) • v) (T':=0)
      (show (1:ℝ) ≤ 1000 by norm_num) (centeredMass_ne_zero_of (hm0 (φ j)))
      (centeredMass_ne_top_of (hmt (φ j)))
    simp only [sub_zero,hres] at hh
    have hh' := div_le_div_of_nonneg_right hh (hS (φ j)).le
    convert hh' using 1; first | rfl | (field_simp [(hS (φ j)).ne']; ring)
  have hright : Tendsto (fun j =>massExcess (centeredMass 0 (U (φ j)) 0 1000)
      (centeredMass 0 (U (φ j)) 0 1)/S (φ j)+1001*‖e (φ j)-v‖) atTop (𝓝 0) := by
    simpa using (hsmall.comp hφ.tendsto_atTop).add
      ((tendsto_const_nhds (x:=(1001:ℝ))).mul (hlim.sub (tendsto_const_nhds (x:=v))).norm)
  have hlt := hright.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨j,hjG,hjU⟩ := (hgrowth.and hlt).exists
  have := hupper j
  exact (not_lt_of_ge (this.trans hjU.le)) hjG

theorem sequence_large_slope_impossible
    (p U : ℕ → Plane → ℝ) (B : ℕ → Plane) (S K err : ℕ → ℝ) (Cp : ℝ)
    (hp : ∀j,ContDiffOn ℝ ∞ (p j) (Metric.ball 0 1000))
    (hU : ∀j,ContDiffOn ℝ ∞ (U j) (Metric.ball 0 1000))
    (hS : ∀j,0<S j) (hSinf : Tendsto S atTop atTop) (hB : ∀j,‖B j‖=S j)
    (hK : Tendsto (fun j =>K j/(S j+‖B j‖)) atTop (𝓝 0))
    (hpb : ∀j x,x∈Metric.ball (0:Plane) 1000 → |p j x|≤Cp)
    (herr : Tendsto err atTop (𝓝 0))
    (hpd : ∀j i x,x∈Metric.ball (0:Plane) 1000 →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤err j)
    (hPDE : ∀j x,x∈Metric.ball (0:Plane) 1000 →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0)
    (hm0 : ∀j,centeredMass (B j) (U j) 0 1≠0)
    (hmt : ∀j,centeredMass (B j) (U j) 0 1000≠⊤)
    (htilt : Tendsto (fun j =>massExcess (centeredMass (B j) (U j) 0 1000)
      (centeredMass (B j) (U j) 0 1)/S j) atTop (𝓝 0))
    (hsmall : Tendsto (fun j =>massExcess (centeredMass 0 (U j) 0 1000)
      (centeredMass 0 (U j) 0 1)/S j) atTop (𝓝 0)) : False := by
  let d : ℕ → ℝ := fun j =>(tiltedMass (S j) (B j) (U j) 1 0 (Metric.ball 0 1000)).toReal⁻¹
  have hmass (j : ℕ) (r : ℝ) : tiltedMass (S j) (B j) (U j) 1 0 (Metric.ball 0 r)=
      centeredMass (B j) (U j) 0 r := by
    simpa using tiltedMass_zero_center (S j) (B j) (U j) 1 r (by norm_num)
  have hnorm (j : ℕ) : 0<d j ∧ tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1000)=1 := by
    apply tiltedMass_normalized
    · rw [hmass]
      exact ne_of_gt ((pos_iff_ne_zero.mpr (hm0 j)).trans_le
        (centeredMass_mono _ _ _ (by norm_num : (1:ℝ)≤1000)))
    · simpa only [hmass] using hmt j
  obtain ⟨V,φ,hφ,hV,hneg,hprof⟩ := extract_tilted_profile Metric.isOpen_ball S B U d
    hS hSinf (fun j =>(hU j).continuousOn) (fun j =>(hnorm j).2.le)
  have htest := full_test_of_profile Metric.isOpen_ball (fun j =>hp (φ j))
    (fun j =>hU (φ j)) (fun j =>hS (φ j)) (hSinf.comp hφ.tendsto_atTop)
    (fun j =>(hnorm (φ j)).1) (hK.comp hφ.tendsto_atTop) (fun j =>hpb (φ j))
    (herr.comp hφ.tendsto_atTop) (fun j =>hpd (φ j)) (fun j =>hPDE (φ j))
    (hV.upperSemicontinuousOn _) hprof
  have hinner : Tendsto (fun j =>logRate (S j)
      (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))) atTop (𝓝 0) := by
    have heq (j : ℕ) := normalized_inner_rate_eq (S:=S j) (B:=B j) (U:=U j)
      (Metric.ball_subset_ball (x:=(0:Plane)) (by norm_num : (1:ℝ)≤1000))
      (by simpa only [hmass] using hm0 j) (by simpa only [hmass] using hmt j)
    simp only [hmass,neg_div] at heq
    simp_rw [show ∀j,logRate (S j) (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))=
      ((-(massExcess (centeredMass (B j) (U j) 0 1000) (centeredMass (B j) (U j) 0 1)/S j):ℝ):EReal)
      from fun j =>by simpa only [d,hmass] using heq j]
    simpa using EReal.tendsto_coe.mpr htilt.neg
  have hzero := profile_zero_of_inner_rate hV (fun x _ =>hneg x) htest hprof
    (fun j =>hS (φ j)) (hinner.comp hφ.tendsto_atTop)
  exact zero_profile_tilt_contradiction hprof hzero (fun j =>hS (φ j))
    (fun j =>(hnorm (φ j)).1) (fun j =>hB (φ j)) (fun j =>hm0 (φ j))
    (fun j =>hmt (φ j)) (hsmall.comp hφ.tendsto_atTop)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

structure UnitWave (Cp a₀ : ℝ) where
  p : Plane → ℝ
  U : Plane → ℝ
  K : ℝ
  frequency_lower : a₀ ≤ K
  smooth_p : ContDiffOn ℝ ∞ p (Metric.ball 0 1000)
  smooth_U : ContDiffOn ℝ ∞ U (Metric.ball 0 1000)
  coefficient_bound : ∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp
  derivative_bound : ∀i x,x∈Metric.ball (0:Plane) 1000 → |coordPartial p i x|≤Cp
  equation : ∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0
  inner_nonzero : centeredMass 0 U 0 1≠0
  outer_finite : centeredMass 0 U 0 1000≠⊤

def UnitWave.excess {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) : ℝ :=
  massExcess (centeredMass (D.K • b) D.U 0 1000) (centeredMass (D.K • b) D.U 0 1)

def UnitWave.growth {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) : ℝ :=
  D.excess b/D.K

lemma UnitWave.excess_nonneg {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) :
    0≤D.excess b :=
  centered_excess_nonneg (by norm_num) (centeredMass_ne_zero_of D.inner_nonzero)
    (centeredMass_ne_top_of D.outer_finite)

theorem large_slope_forces_growth {Cp a₀ : ℝ} (hCp : 0≤Cp) (ha₀ : 0<a₀)
    (L : ℝ) (hL : 0≤L) :
    ∃Bstar η : ℝ,1≤Bstar ∧ 0<η ∧ ∀(D : UnitWave Cp a₀) (b : Plane),
      Bstar≤‖b‖ → D.growth b≤η*‖b‖ → L<D.growth 0 := by
  by_contra hn
  push Not at hn
  have hf (j : ℕ) := hn ((j:ℝ)+1) ((j:ℝ)+1)⁻¹ (by have := Nat.cast_nonneg (α:=ℝ) j; linarith) (by positivity)
  choose D b hb hg hbad using hf
  let n : ℕ → ℝ := fun j =>(j:ℝ)+1
  let S : ℕ → ℝ := fun j =>(D j).K*‖b j‖
  let B : ℕ → Plane := fun j =>(D j).K • b j
  have hnpos (j : ℕ) : 0<n j := by dsimp [n]; positivity
  have hn1 (j : ℕ) : 1≤n j := by dsimp [n]; have := Nat.cast_nonneg (α:=ℝ) j; linarith
  have hKpos (j : ℕ) : 0<(D j).K := ha₀.trans_le (D j).frequency_lower
  have hbpos (j : ℕ) : 0<‖b j‖ := (hnpos j).trans_le (hb j)
  have hSpos (j : ℕ) : 0<S j := mul_pos (hKpos j) (hbpos j)
  have hB (j : ℕ) : ‖B j‖=S j := by
    simp only [B,S,norm_smul,Real.norm_eq_abs,abs_of_pos (hKpos j)]
  have hT : Tendsto n atTop atTop :=
    tendsto_atTop_mono (fun _ =>le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun j =>(n j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hT
  have hSinf : Tendsto S atTop atTop := by
    apply tendsto_atTop_mono _ (hT.const_mul_atTop ha₀)
    intro j
    exact mul_le_mul (D j).frequency_lower (hb j) (hnpos j).le (hKpos j).le
  have hratio (j : ℕ) : (D j).K/(S j+‖B j‖)=1/(2*‖b j‖) := by
    rw [hB]
    dsimp [S]
    field_simp [(hKpos j).ne', (hbpos j).ne']
    ring
  have hratioBound (j : ℕ) : |(D j).K/(S j+‖B j‖)|≤(n j)⁻¹ := by
    rw [hratio,abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num) (hbpos j))),one_div]
    exact inv_anti₀ (hnpos j) (by linarith [hb j])
  have hratioLim : Tendsto (fun j =>(D j).K/(S j+‖B j‖)) atTop (𝓝 0) :=
    squeeze_zero_norm (by simpa only [Real.norm_eq_abs] using hratioBound) hinv
  have herrLim : Tendsto (fun j =>Cp*(n j)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul Cp
  have hgrad (j : ℕ) (i : Fin 2) (x : Plane) (hx : x∈Metric.ball (0:Plane) 1000) :
      |(D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖B j‖))|≤Cp*(n j)⁻¹ := by
    have heq : (D j).K^2*coordPartial (D j).p i x/(S j*(S j+‖B j‖))=
        coordPartial (D j).p i x/(2*‖b j‖^2) := by
      rw [hB]
      dsimp [S]
      field_simp [(hKpos j).ne', (hbpos j).ne']
      ring
    rw [heq,abs_div,abs_of_pos (mul_pos (by norm_num) (sq_pos_of_pos (hbpos j)))]
    calc
      _ ≤ Cp/(2*‖b j‖^2) := div_le_div_of_nonneg_right ((D j).derivative_bound i x hx) (by positivity)
      _ ≤ Cp/(n j) := div_le_div_of_nonneg_left hCp (hnpos j) (by nlinarith [hb j,hn1 j])
      _ = _ := div_eq_mul_inv _ _
  have htilt : Tendsto (fun j =>(D j).excess (b j)/S j) atTop (𝓝 0) := by
    apply squeeze_zero _ _ hinv
    · intro j
      exact div_nonneg ((D j).excess_nonneg _) (hSpos j).le
    · intro j
      have hh := (div_le_iff₀ (hbpos j)).mpr (hg j)
      change (D j).excess (b j)/((D j).K*‖b j‖)≤(n j)⁻¹
      simpa only [UnitWave.growth,div_div] using hh
  have huntilt : Tendsto (fun j =>(D j).excess 0/S j) atTop (𝓝 0) := by
    have hlim : Tendsto (fun j =>L*(n j)⁻¹) atTop (𝓝 0) := by simpa using hinv.const_mul L
    apply squeeze_zero _ _ hlim
    · intro j
      exact div_nonneg ((D j).excess_nonneg _) (hSpos j).le
    · intro j
      change (D j).excess 0/((D j).K*‖b j‖)≤_
      rw [← div_div]
      exact (div_le_div_of_nonneg_right (hbad j) (hbpos j).le).trans
        (by simpa only [div_eq_mul_inv] using div_le_div_of_nonneg_left hL (hnpos j) (hb j))
  apply sequence_large_slope_impossible (fun j =>(D j).p) (fun j =>(D j).U) B S
    (fun j =>(D j).K) (fun j =>Cp*(n j)⁻¹) Cp
    (fun j =>(D j).smooth_p) (fun j =>(D j).smooth_U) hSpos hSinf hB hratioLim
    (fun j =>(D j).coefficient_bound) herrLim hgrad (fun j =>(D j).equation)
    (fun j =>centeredMass_ne_zero_of (T':=B j) (D j).inner_nonzero)
    (fun j =>centeredMass_ne_top_of (T':=B j) (D j).outer_finite) htilt
  simpa only [UnitWave.excess,smul_zero] using huntilt

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma descent_smallness {C K s E E₀ t : ℝ} (hC : 0<C) (hK : 0<K) (hs : 0 ≤ s)
    (hE : 0≤E) (ht : 0≤t) (hcomp : E₀ ≤ E+1001*K*t)
    (hlarge : 2*(C+1)*1001<E₀/K ∨ 2*(C+1)*1001<t) :
    let S:=E+(C+1)+K*s
    C≤S ∧ E≤S ∧ K/(S+K*t)≤C⁻¹ ∧ K^2*s/(S*(S+K*t))≤C⁻¹ := by
  dsimp only
  have hS : 0<E+(C+1)+K*s := by positivity
  have hSK : K*s≤E+(C+1)+K*s := by linarith
  have hden : 0<E+(C+1)+K*s+K*t := by positivity
  have hmajor : C*K≤E+(C+1)+K*s+K*t := by
    rcases hlarge with h | h
    · have hh := (lt_div_iff₀ hK).mp h
      have hEs : E≤E+(C+1)+K*s := by nlinarith [mul_nonneg hK.le hs]
      have hE' : E≤1001*(E+(C+1)+K*s) := by nlinarith
      nlinarith [mul_pos hC hK]
    · have hh := mul_lt_mul_of_pos_left h hK
      nlinarith [mul_nonneg hK.le hs,mul_pos hC hK]
  have hrat : K/(E+(C+1)+K*s+K*t)≤C⁻¹ := by
    apply (div_le_iff₀ hden).mpr
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hC).mpr (by nlinarith only [hmajor])
  refine ⟨by nlinarith [mul_nonneg hK.le hs],by nlinarith [mul_nonneg hK.le hs],hrat,?_⟩
  apply le_trans _ hrat
  apply (div_le_div_iff₀ (mul_pos hS hden) hden).mpr
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSK hK.le) hden.le
  nlinarith only [hh]

theorem one_step_descent : ∃A : ℕ,10000<A ∧ ∃C₁ : ℝ,0<C₁ ∧
    ∀Cp : ℝ,0≤Cp → ∃C₀ L : ℝ,1≤C₀ ∧ 0<L ∧
    ∀(p U : Plane → ℝ) (b : Plane) (K s : ℝ),
    ContDiffOn ℝ ∞ p (Metric.ball 0 1000) →
    ContDiffOn ℝ ∞ U (Metric.ball 0 1000) → 0<K → 0 ≤ s →
    (∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp) →
    (∀i x,x∈Metric.ball (0:Plane) 1000 → |coordPartial p i x|≤Cp*s) →
    (∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0) →
    centeredMass 0 U 0 1≠0 → centeredMass 0 U 0 1000≠⊤ →
    (L < massExcess (centeredMass 0 U 0 1000) (centeredMass 0 U 0 1)/K ∨ L<‖b‖) →
    let m:=massExcess (centeredMass (K • b) U 0 1000) (centeredMass (K • b) U 0 1)/K
    let f:=C₀/K+s
    ∃b' : Plane → Plane,
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖b' y-b‖)≤C₁*(m+f) ∧
      (∀y∈gridCenters A,centeredMass (K • b' y) U y ((A:ℝ)⁻¹)≠0 ∧
        centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹)≠⊤) ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,
        massExcess (centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹))
          (centeredMass (K • b' y) U y ((A:ℝ)⁻¹))/(K*(A:ℝ)⁻¹))≤(m+f)/2 := by
  obtain ⟨A,hA,C₁,hC₁,hsub⟩ := one_subdivision
  refine ⟨A,hA,C₁,hC₁,?_⟩
  intro Cp hCp
  obtain ⟨C,hC,hsub⟩ := hsub Cp hCp
  refine ⟨C+1,2*(C+1)*1001,by linarith,by positivity,?_⟩
  intro p U b K s hp hU hK hs hpb hpd hPDE hm0 hmt hlarge
  dsimp only
  have hb0 : centeredMass (K • b) U 0 1≠0 := centeredMass_ne_zero_of hm0
  have hbt : centeredMass (K • b) U 0 1000≠⊤ := centeredMass_ne_top_of hmt
  let E:=massExcess (centeredMass (K • b) U 0 1000) (centeredMass (K • b) U 0 1)
  have hE : 0≤E := centered_excess_nonneg (by norm_num) hb0 hbt
  have hnorm : ‖K • b‖=K*‖b‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hK]
  have hc := centered_excess_weight_bound (T':=K • b) (by norm_num : (1:ℝ)≤1000) hm0 hmt
  simp only [zero_sub,norm_neg,hnorm] at hc
  obtain ⟨hmin,hEs,hrat,hrat'⟩ := descent_smallness hC hK hs hE (norm_nonneg b)
    (by dsimp [E]; nlinarith only [hc]) hlarge
  rw [← hnorm] at hrat hrat'
  obtain ⟨b',hinc,hfinite,hdec⟩ := hsub p U b K (E+(C+1)+K*s) s hp hU hK hs hmin
    hpb hpd hPDE hb0 hbt hEs hrat hrat'
  refine ⟨b',?_,hfinite,?_⟩
  · convert hinc using 1
    dsimp [E]
    field_simp
    ring
  · convert hdec using 1
    dsimp [E]
    field_simp
    ring

end SharpNodal.Profiles

end
end
end
end

end OAI
