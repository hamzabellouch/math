import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ConeRadius

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_annulus_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec→W} {ε R : ℝ} (hε : 0<ε)
    (hg : IntegrableOn g (ball (0:Vec) R \ ball (0:Vec) ε)) :
    (∫z in ball (0:Vec) R \ ball (0:Vec) ε,g z)=
      ∫n : Sphere,∫r in Ico ε R,r^2 • g (r • n.1) ∂volume ∂sphereMeasure := by
  classical
  let H := (ball (0:Vec) R \ ball (0:Vec) ε).indicator g
  have hm : MeasurableSet (ball (0:Vec) R \ ball (0:Vec) ε) := measurableSet_ball.diff measurableSet_ball
  have hi : Integrable H := (integrable_indicator_iff hm).mpr hg
  rw [←integral_indicator hm]
  change (∫z,H z)=_
  rw [integral_polar hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    have he : ∀r∈Ioi (0:ℝ),r^2 • H (r • n.1)=
        (Ico ε R).indicator (fun r=>r^2 • g (r • n.1)) r := by
      intro r hr
      have hnorm : ‖r • n.1‖=r := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]
      have hmem : r • n.1∈ball (0:Vec) R \ ball (0:Vec) ε ↔ r∈Ico ε R := by
        simp only [Set.mem_sdiff,mem_ball_zero_iff,hnorm,mem_Ico,not_lt]
        exact and_comm
      by_cases h : r∈Ico ε R
      · rw [show H (r • n.1)=g (r • n.1) from indicator_of_mem (hmem.mpr h) g,
          indicator_of_mem h]
      · rw [show H (r • n.1)=0 from indicator_of_notMem (fun hh => h (hmem.mp hh)) g,
          smul_zero,indicator_of_notMem h]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ico]
    have hset : Ioi (0:ℝ) ∩ Ico ε R=Ico ε R := by
      ext r
      simp only [mem_inter_iff,mem_Ioi,mem_Ico]
      exact ⟨fun h => h.2,fun h => ⟨hε.trans_le h.1,h⟩⟩
    rw [hset])

lemma fderiv_degree_neg_two {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=(r^2)⁻¹ • F z)
    {r : ℝ} (hr : 0<r) {z : Vec}
    (hz : DifferentiableAt ℝ F z) (hrz : DifferentiableAt ℝ F (r • z)) (e : Vec) :
    fderiv ℝ F (r • z) e=(r^3)⁻¹ • fderiv ℝ F z e := by
  have hm : HasFDerivAt (fun y : Vec => r • y) (r • ContinuousLinearMap.id ℝ Vec) z :=
    (hasFDerivAt_id z).const_smul r
  have h₁ := hrz.hasFDerivAt.comp z hm
  have h₂ := hz.hasFDerivAt.const_smul ((r^2)⁻¹)
  have heq : (fun y : Vec => F (r • y))=(fun y : Vec => (r^2)⁻¹ • F y) := funext (hh r hr)
  change HasFDerivAt (fun y : Vec => F (r • y)) _ _ at h₁
  rw [heq] at h₁
  have hv := congrArg (fun L : Vec →L[ℝ] Vec => L e) (h₁.unique h₂)
  change fderiv ℝ F (r • z) (r • e)=(r^2)⁻¹ • fderiv ℝ F z e at hv
  rw [map_smul] at hv
  have hv' := congrArg (fun a : Vec => r⁻¹ • a) hv
  simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
    show r⁻¹*(r^2)⁻¹=(r^3)⁻¹ by field_simp] using hv'

lemma divergence_degree_neg_two {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=(r^2)⁻¹ • F z)
    (hF : ∀ z≠0, DifferentiableAt ℝ F z) {r : ℝ} (hr : 0<r) {z : Vec} (hz : z≠0) :
    divergence F (r • z)=(r^3)⁻¹*divergence F z := by
  have hrz : r • z≠0 := smul_ne_zero hr.ne' hz
  have hc (y : Vec) (hy : y≠0) (i : Fin 3) :
      fderiv ℝ (fun x => F x i) y = (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y) := by
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y (hF y hy).hasFDerivAt).fderiv
  unfold divergence spatialPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc _ hrz i,hc _ hz i]
  change (fderiv ℝ F (r • z) (basis i)) i = (r^3)⁻¹*(fderiv ℝ F z (basis i)) i
  rw [fderiv_degree_neg_two hh hr (hF _ hz) (hF _ hrz)]
  rfl

lemma angular_mean_divergence_degree_neg_two {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0<r → ∀ z, F (r • z)=(r^2)⁻¹ • F z)
    (hF : ∀ z≠0, ContDiffAt ℝ 1 F z) :
    (∫ n : Sphere, divergence F n.1 ∂sphereMeasure)=0 := by
  have hd : ∀ z≠0, DifferentiableAt ℝ F z := fun z hz => (hF z hz).differentiableAt (by simp)
  have hz (n : Sphere) : n.1≠0 := by
    intro h
    have := sphere_norm n
    rw [h,norm_zero] at this
    norm_num at this
  have hG := contDiff_holeCutoff_smul (F:=F) (by norm_num : (0:ℝ)<1) hF
  have hc := continuous_divergence hG
  have hi : IntegrableOn (divergence F) (ball (0:Vec) 2 \ ball (0:Vec) 1) := by
    apply ((hc.continuousOn.integrableOn_compact (isCompact_closedBall (0:Vec) 2)).mono_set
      (s:=ball (0:Vec) 2 \ ball (0:Vec) 1) (fun z hz => ball_subset_closedBall hz.1)).congr_fun
    · intro z hz
      apply divergence_holeCutoff (by norm_num : (0:ℝ)<1)
      have hn : 1≤‖z‖ := by simpa only [mem_ball_zero_iff,not_lt] using hz.2
      linarith
    · exact measurableSet_ball.diff measurableSet_ball
  have ha := divergence_annulus (F:=F) (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤2) hF
  have hflux (n : Sphere) : (2:ℝ)^2*dot n.1 (F ((2:ℝ) • n.1))=
      (1:ℝ)^2*dot n.1 (F ((1:ℝ) • n.1)) := by
    rw [hh 2 (by norm_num),one_smul,dot_smul_right]
    ring
  have ha0 : (∫z in ball (0:Vec) 2 \ ball (0:Vec) 1,divergence F z)=0 := by
    rw [ha,show (∫n : Sphere,(2:ℝ)^2*dot n.1 (F ((2:ℝ) • n.1)) ∂sphereMeasure)=
      (∫n : Sphere,(1:ℝ)^2*dot n.1 (F ((1:ℝ) • n.1)) ∂sphereMeasure) from integral_congr_ae (ae_of_all _ hflux),sub_self]
  rw [integral_annulus_polar (by norm_num : (0:ℝ)<1) hi] at ha0
  have hir (n : Sphere) : (∫r in Ico (1:ℝ) 2,r^2 • divergence F (r • n.1))=
      Real.log 2*divergence F n.1 := by
    rw [setIntegral_congr_fun measurableSet_Ico (g:=fun r => r⁻¹*divergence F n.1)]
    · rw [integral_mul_const,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),
        integral_inv_of_pos (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)]
      simp
    · intro r hr
      have hr0 : 0<r := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hr.1
      dsimp only
      rw [divergence_degree_neg_two (r:=r) (z:=n.1) hh hd hr0 (hz n),smul_eq_mul]
      field_simp
  simp_rw [hir] at ha0
  rw [integral_const_mul] at ha0
  exact (mul_eq_zero.mp ha0).resolve_left (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def transportAngularCore (n u : Vec) : Vec :=
  ((1-dot u u)/(1-dot n u)^2) • (n-u)

def sourceAngularCore (n u b : Vec) : Vec :=
  ((1-dot n u)^2)⁻¹ • ((dot n b) • (n-u)-(1-dot n u) • b)

lemma physicalElectricKernel_eulerian_split {r : ℝ} {n u : Vec} (b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    (1-dot n u) • physicalElectricKernel r n u b =
      (r^2)⁻¹ • transportAngularCore n u+r⁻¹ • sourceAngularCore n u b := by
  ext i
  simp only [physicalElectricKernel,transportAngularCore,sourceAngularCore,
    PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma coneRadius_zero_smul {r : ℝ} (hr : 0<r) (z : Vec) :
    coneRadius 0 (r • z)=r*coneRadius 0 z := by
  simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr]

lemma coneDirection_zero_smul {r : ℝ} (hr : 0<r) (z : Vec) :
    coneDirection 0 (r • z)=coneDirection 0 z := by
  rw [coneDirection,coneRadius_zero_smul hr,zero_sub,←smul_neg,
    mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ hr.ne',mul_one]
  simp only [coneDirection,zero_sub]

lemma contDiffAt_transportAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => transportAngularCore (n w) (u w)) z := by
  have hdu := contDiff_dot_pair.contDiffAt.comp z (hu.prodMk hu)
  have hdn := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hu)
  exact ((contDiffAt_const.sub hdu).div ((contDiffAt_const.sub hdn).pow 2)
    (pow_ne_zero 2 hd)).smul (hn.sub hu)

lemma contDiffAt_coneSpatialLift {k : ℕ∞ω} {x y v e : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (fun z : Vec => coneSpatialLift x z v e) y := by
  have hn := contDiffAt_coneDirection (k:=k) hxy
  have hde := contDiff_dot_pair.contDiffAt.comp y (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp y (hn.prodMk (contDiffAt_const (c:=velocity v)))
  have hc : ContDiffAt ℝ k (fun z : Vec => coneSpatialCoefficient x z v e) y :=
    hde.div (contDiffAt_const.sub hdu) (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  exact contDiffAt_const.add (hc.smul contDiffAt_const)

def transportSpatialFlux (v e : Vec) (i : Fin 3) (z : Vec) : Vec :=
  (((coneRadius 0 z)^2)⁻¹*transportAngularCore (coneDirection 0 z) (velocity v) i) •
    coneSpatialLift 0 z v e

lemma transportSpatialFlux_contDiffAt (v e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (transportSpatialFlux v e i) z := by
  have h0z : (0:Vec)≠z := Ne.symm hz
  have hr := contDiffAt_coneRadius (k:=1) h0z
  have hn := contDiffAt_coneDirection (k:=1) h0z
  have hu : ContDiffAt ℝ 1 (fun _ : Vec => velocity v) z := contDiffAt_const
  have hc := contDiffAt_transportAngularCore hn hu
    (cone_denom_pos v _ (coneDirection_norm h0z)).ne'
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp z hc
  exact (((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h0z)))).mul hi).smul
    (contDiffAt_coneSpatialLift (v:=v) (e:=e) h0z)

lemma transportSpatialFlux_homogeneous (v e : Vec) (i : Fin 3) {r : ℝ} (hr : 0<r) (z : Vec) :
    transportSpatialFlux v e i (r • z)=(r^2)⁻¹ • transportSpatialFlux v e i z := by
  simp only [transportSpatialFlux,coneSpatialLift,coneSpatialCoefficient,
    coneRadius_zero_smul hr,coneDirection_zero_smul hr,smul_smul]
  congr 1
  ring

lemma transportSpatialFlux_angular_mean_zero (v e : Vec) (i : Fin 3) :
    (∫ n : Sphere, divergence (transportSpatialFlux v e i) n.1 ∂sphereMeasure)=0 := by
  exact angular_mean_divergence_degree_neg_two
    (fun r hr z => transportSpatialFlux_homogeneous v e i hr z)
    (fun z hz => transportSpatialFlux_contDiffAt v e i hz)

end RVM

end

end OAI
