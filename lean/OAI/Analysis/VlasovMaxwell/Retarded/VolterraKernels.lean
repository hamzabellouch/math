import Mathlib
import OAI.Analysis.VlasovMaxwell.Continuation.GlobalBoundaryBound
import OAI.Analysis.VlasovMaxwell.Regularity.PhysicalC0
import OAI.Analysis.VlasovMaxwell.Population.TransportSingularBulk

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma integral_symmetric_annulus_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t : ℝ} (ht : 0<t) (hF : IntegrableOn F (ball (0:Vec) t)) :
    Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) (t-a) \ ball (0:Vec) a,F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t,F z)) := by
  have hh : Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) t,
      (ball (0:Vec) (t-a) \ ball (0:Vec) a).indicator F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t,F z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    · exact Eventually.of_forall (fun a => hF.aestronglyMeasurable.indicator (measurableSet_ball.diff measurableSet_ball))
    · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => norm_indicator_le_norm_self _ _))
    · exact hF.norm
    · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
      have hn : ‖z‖<t := by simpa only [mem_ball_zero_iff] using hz
      have hn0 : 0<‖z‖ := norm_pos_iff.mpr hz0
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (lt_min hn0 (show 0<t-‖z‖ by linarith))] with a ha
      symm
      apply indicator_of_mem
      simp only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt]
      exact ⟨by linarith [ha.2.trans_le (min_le_right _ _)],(ha.2.trans_le (min_le_left _ _)).le⟩
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  rw [setIntegral_indicator (measurableSet_ball.diff measurableSet_ball),inter_eq_right.mpr]
  intro z hz
  exact ball_subset_ball (by linarith [ha.1] : t-a≤t) hz.1

lemma norm_integral_ball_of_annulus_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t C : ℝ} (ht : 0<t) (hF : IntegrableOn F (ball (0:Vec) t))
    (hb : ∀ ε R : ℝ, 0<ε → ε≤R → R<t → ‖∫ z in ball (0:Vec) R \ ball (0:Vec) ε,F z‖≤C) :
    ‖∫ z in ball (0:Vec) t,F z‖≤C := by
  apply le_of_tendsto (integral_symmetric_annulus_tendsto ht hF).norm
  filter_upwards [Ioo_mem_nhdsGT (half_pos ht)] with a ha
  exact hb a (t-a) ha.1 (by linarith [ha.2]) (by linarith [ha.1])

lemma particle_spatial_fderiv {f : Particle} {u : ℝ} {y v : Vec}
    (hf : DifferentiableAt ℝ f (u,y,v)) (e : Vec) :
    fderiv ℝ (fun z => f (u,z,v)) y e=fderiv ℝ f (u,y,v) (0,e,0) := by
  have hm : HasFDerivAt (fun z : Vec => (u,z,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) y :=
    (hasFDerivAt_const u y).prodMk ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const v y))
  have hh := hf.hasFDerivAt.comp (f:=fun z : Vec => (u,z,v)) y hm
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma transportConeCoefficient_uniform_bound (P : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z v : Vec, z≠0 → ‖v‖≤P →
      |transportConeCoefficient i (z,v)|≤C/‖z‖^2 := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => transportAngularCore p.1 (velocity p.2) i) K := by
    intro p hp
    have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
    have hh := contDiffAt_transportAngularCore (k:=1) (z:=p) contDiffAt_fst
      (contDiff_velocity.contDiffAt.comp p contDiffAt_snd) (cone_denom_pos p.2 p.1 hn).ne'
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp hh.continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z v hz hv
  have hb := hC (coneDirection 0 z,v) ⟨by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩
  unfold transportConeCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (inv_nonneg.mpr (sq_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma transport_derivative_integrable {s : Solution} {U t P N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,transportConeCoefficient i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => transportConeCoefficient i p*
    fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0)
  let A := ball (0:Vec) t \ ({0} : Set Vec)
  have hzprop {z : Vec} (hz : z∈A) : z≠0 ∧ 0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hzr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact ⟨hz.2,by simpa [coneRadius] using sub_pos.mpr hzr,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-z)]⟩
  have hfc : ContinuousOn F (A ×ˢ univ) := by
    intro p hp
    have hh := hzprop hp.1
    have hr := (contDiffAt_coneRadius (k:=1) hh.1.symm).comp p contDiffAt_fst
    have hm : ContinuousAt (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2)) p :=
      ((contDiffAt_const.sub hr).prodMk ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd)).continuousAt
    have hdf : ContinuousAt (fun q : Phase => fderiv ℝ s.f (t-coneRadius 0 q.1,x+q.1,q.2)) p :=
      ((particle_contDiffAt_positive hf hh.2.1 (x+p.1) p.2).continuousAt_fderiv (by simp)).comp (f:=fun q : Phase => (t-coneRadius 0 q.1,x+q.1,q.2)) hm
    exact ((transportConeCoefficient_contDiffAt i hh.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖^2)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv))
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma magnetic_transport_gradient_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) t, ∫ v,
        transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨B,C,D,hB,hC,hD,hbound⟩ := magnetic_transport_annulus_gradient_bound P A M H e i hA hH
  refine ⟨B,C,D,hB,hC,hD,?_⟩
  intro s U t N x ht htU hUH hN hf hE hB hc heq hfA hP hEB hfN
  apply norm_integral_ball_of_annulus_bound ht (transport_derivative_integrable x e i ht htU hf hN hP hfN)
  intro ε R hε hεR hRt
  exact hbound s U t N ε R x ht htU hUH hN hε hεR hRt hf hE hB hc heq hfA hP hEB hfN

lemma particle_fixed_time_contDiff {s : Solution} {k : ℕ∞ω} {u : ℝ}
    (hf : ContDiffOn ℝ k s.f particleHalfSpace) (hu : 0≤u) :
    ContDiff ℝ k (fun p : Phase => s.f (u,p)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => hu)

lemma transport_kernel_velocity_contDiff (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiff ℝ 1 (fun v => transportConeCoefficient i (z,v)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  exact (transportConeCoefficient_contDiffAt i hz).comp v (contDiffAt_const.prodMk contDiffAt_id)

lemma hasDerivAt_transport_particle_line {s : Solution} {u P : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hu : 0<u)
    (hP : ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (x e z : Vec) (hz : z≠0) (i : Fin 3) (a : ℝ) :
    HasDerivAt (fun q : ℝ => ∫ v,transportConeCoefficient i (z,v)*s.f (u,x+q • e,v))
      (∫ v,transportConeCoefficient i (z,v)*fderiv ℝ s.f (u,x+a • e,v) (0,e,0)) a := by
  let F : ℝ × Vec → ℝ := fun p => s.f (u,x+p.1 • e,p.2)
  let w : Vec → ℝ := fun v => transportConeCoefficient i (z,v)
  have hF : ContDiff ℝ 1 F := (particle_fixed_time_contDiff hf hu.le).comp
    ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)
  have hw : ContDiff ℝ 1 w := transport_kernel_velocity_contDiff i hz
  have hzero (a : ℝ) (_ : a∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (a,v)=0 :=
    hP _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hG : ContDiffOn ℝ 1 (fun p : ℝ × Vec => w p.2*F p) (univ ×ˢ univ) :=
    ((hw.comp contDiff_snd).mul hF).contDiffOn
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG (by intro q hq v hv; rw [hzero q hq v hv,mul_zero])).differentiableAt.hasDerivAt
  rw [show deriv (fun x => ∫ v, w v*F (x,v)) a = fderiv ℝ (fun x => ∫ v,w v*F (x,v)) a 1 from rfl,fderiv_weighted_integral_uniform_support_apply isOpen_univ
    (isCompact_closedBall (0:Vec) P) (mem_univ a) hF.contDiffOn hw hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    apply congrArg (fun r : ℝ => w v*r)
    have hm : HasFDerivAt (fun p : ℝ × Vec => (u,x+p.1 • e,p.2))
        ((0 : (ℝ × Vec) →L[ℝ] ℝ).prod
          (((ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ Vec) e)).prod
            (ContinuousLinearMap.snd ℝ ℝ Vec))) (a,v) := by
      convert (hasFDerivAt_const u (a,v)).prodMk
        (((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
          (hasFDerivAt_snd (𝕜:=ℝ))) using 1
      first | rfl | simp
    have hh := (particle_differentiableAt_positive hf hu _ v).hasFDerivAt.comp
      (f:=fun p : ℝ × Vec => (u,x+p.1 • e,p.2)) (a,v) hm
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      zero_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',one_smul,F,Function.comp_def] using
      congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv)

lemma norm_transport_velocity_integral_le {P C A : ℝ} {z : Vec} {i : Fin 3}
    {g : Vec → ℝ} (_hA : 0≤A)
    (hk : ∀ v, ‖v‖≤P → |transportConeCoefficient i (z,v)|≤C/‖z‖^2)
    (hzero : ∀ v, P<‖v‖ → g v=0) (hg : ∀ v, |g v|≤A) :
    ‖∫ v,transportConeCoefficient i (z,v)*g v‖≤volume.real (closedBall (0:Vec) P)*C*A/‖z‖^2 := by
  have heq : (∫ v,transportConeCoefficient i (z,v)*g v)=
      ∫ v in closedBall (0:Vec) P,transportConeCoefficient i (z,v)*g v := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),mul_zero]
  rw [heq]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => transportConeCoefficient i (z,v)*g v) (C:=(C/‖z‖^2)*A) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hk v (by simpa only [mem_closedBall,dist_zero_right] using hv)) (hg v)
        (abs_nonneg _) (le_trans (abs_nonneg _) (hk v (by simpa only [mem_closedBall,dist_zero_right] using hv))))
  exact hb.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ]; ring)

lemma transport_density_integrable {s : Solution} {U t P A : ℝ} (x : Vec) (i : Fin 3)
    (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) :
    IntegrableOn (fun z => ∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))
      (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => transportConeCoefficient i p*s.f (t-coneRadius 0 p.1,x+p.1,p.2)
  let U₀ := retardedSpaceDomain t 0
  have htime {z : Vec} (hz : z∈U₀) : t-coneRadius 0 z∈Icc (0:ℝ) U :=
    ⟨hz.2.le,(sub_le_self _ (norm_nonneg _)).trans htU⟩
  have hk : ContinuousOn (transportConeCoefficient i) (U₀ ×ˢ univ) := by
    intro p hp
    exact (transportConeCoefficient_contDiffAt i hp.1.1.symm).continuousAt.continuousWithinAt
  have hfc : ContinuousOn F (U₀ ×ˢ univ) := hk.mul
      (shifted_particle_continuousOn x htU (hf.continuousOn.mono (fun p hp => hp.1)))
  have hzero (z : Vec) (hz : z∈U₀) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    dsimp [F]
    rw [hP _ (htime hz) _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),mul_zero]
  have hsub : ball (0:Vec) t \ ({0} : Set Vec)⊆U₀ := by
    intro z hz
    exact ⟨(show z≠0 from hz.2).symm,by simpa only [coneRadius,zero_sub,norm_neg] using
      (sub_pos.mpr (show ‖z‖<t by simpa only [mem_ball,dist_zero_right] using hz.1))⟩
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=volume.real (closedBall (0:Vec) P)*C*A)
    (by norm_num) ((continuousOn_integral_uniform_support (isCompact_closedBall _ _) hfc hzero).mono hsub)
  intro z hz hzt
  have hzu : z∈U₀ := hsub ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hb := norm_transport_velocity_integral_le hA (fun v hv => hcb z v (norm_pos_iff.mp hz) hv)
    (hP _ (htime hzu) (x+z)) (hfA _ (htime hzu) (x+z))
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_two,div_eq_mul_inv] using hb

lemma hasDerivAt_magnetic_transport_integral {s : Solution} {U t P A N : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ)
    (ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hA : 0≤A) (hN : 0≤N)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
      transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t, ∫ v,transportConeCoefficient i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,(x+a • e)+z,v) (0,e,0)) a := by
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have htime {z : Vec} (hz : z∈ball (0:Vec) t) :
      0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    exact ⟨by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hr,
      (sub_le_self _ (norm_nonneg _)).trans htU⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => D*‖z‖^(-(2:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (transport_density_integrable (x+q • e) i htU hf hA hP hfA).aestronglyMeasurable))
    (transport_density_integrable (x+a • e) i htU hf hA hP hfA)
    (transport_derivative_integrable (x+a • e) e i ht htU hf hN hP hfN).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (2:ℝ)<3 by norm_num)).const_mul D) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    intro q _
    have htz := htime hz
    refine (norm_transport_velocity_integral_le (mul_nonneg hN (norm_nonneg e))
      (fun v hv => hcb z v hz0 hv) ?_ ?_).trans_eq ?_
    · intro v hv
      rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf htz.1 _ _) e]
      have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
        funext (fun y => hP _ ⟨htz.1.le,htz.2⟩ y v hv)
      rw [he]
      simp
    · intro v
      rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf htz.1 _ _) e]
      simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans
        (mul_le_mul_of_nonneg_right (hfN _ ⟨htz.1.le,htz.2⟩ _ v) (norm_nonneg e))
    · simp only [D,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
      ring
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    intro q _
    have htz := htime hz
    simpa only [add_right_comm] using hasDerivAt_transport_particle_line hf htz.1
      (hP _ ⟨htz.1.le,htz.2⟩) (x+z) e z hz0 i q

lemma magnetic_transport_deriv_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
        transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨B,C,D,hB,hC,hD,hb⟩ := magnetic_transport_gradient_bound P A M H e i hA hH
  refine ⟨B,C,D,hB,hC,hD,?_⟩
  intro s U t N x ht htU hUH hN hf hE hBB hc heq hfA hP hEB hfN
  rw [(hasDerivAt_magnetic_transport_integral x e i 0 ht htU hf hA hN hP hfA hfN).deriv]
  simpa only [zero_smul,add_zero] using hb s U t N x ht htU hUH hN hf hE hBB hc heq hfA hP hEB hfN

lemma source_sphere_support {s : Solution} {t U P r : ℝ} (x e : Vec) (i : Fin 3)
    (hr : 0≤r) (hrt : r≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ n : Sphere,r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) •
      (sourceConeCoefficient s t x i (r • n.1,v) • coneSpatialLift 0 (r • n.1) v e)) ∂sphereMeasure) =
    (∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) •
      sourceFixedFlux v (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) ∂sphereMeasure) := by
  apply integral_congr_ae
  apply ae_of_all
  intro n
  have hrad : coneRadius 0 (r • n.1)=r := by
    simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one]
  simp only [sourceConeCoefficient,hrad]
  change r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
      (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1))=_
  congr 2
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  rw [hP _ ⟨by linarith,by linarith⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_smul]

lemma source_bulk_support {s : Solution} {t U P ε R : ℝ} (x e : Vec) (i : Fin 3)
    (hRt : R≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,∫ v,s.f (t-coneRadius 0 z,x+z,v)*
      (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
        divergence (fun w => sourceConeCoefficient s t x i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)) =
    ∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z := by
  apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
  intro z hz
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    have hzR : ‖z‖<R := by simpa only [mem_ball,dist_zero_right] using hz.1
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  rw [hP _ hu _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_mul]

lemma magnetic_source_annulus_gradient_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H Q ε R : ℝ) (x : Vec),
      0≤H → 0≤Q → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        C*(H+H^2*(1+Q)) := by
  obtain ⟨C,hC,hb⟩ := source_division_bulk_annulus_bound P A M e i hA
  obtain ⟨B,hB,hbd⟩ := source_sphere_boundary_bound P M A e i hA
  refine ⟨C+2*B,by positivity,?_⟩
  intro s U t H Q ε R x hH hQ hε hεR hRt htU hUH hf hE hB' hc heq hfA hfP hEB hDF
  have hid := magnetic_source_division_annulus hf hE hB' hc heq htU hε hεR hRt x e i
  rw [hid,source_sphere_support x e i (hε.le.trans hεR) hRt.le htU hfP,
    source_sphere_support x e i hε.le (hεR.trans hRt.le) htU hfP,
    source_bulk_support x e i hRt.le htU hfP]
  have hout := hbd s t U R x (hε.trans_le hεR) hRt.le htU hfA hEB
  have hin := hbd s t U ε x hε (hεR.trans hRt.le) htU hfA hEB
  have hbulk := hb s U t H Q ε R x hH hQ hε hεR hRt htU hUH hE hB' hfA hEB hDF
  apply (abs_sub _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add hout hin)) hbulk).trans
  have hRH : R≤H := hRt.le.trans (htU.trans hUH)
  have heH : ε≤H := hεR.trans hRH
  have hnon : 0≤H^2*(1+Q) := by positivity
  have hBR : B*R≤B*H := mul_le_mul_of_nonneg_left hRH hB
  have hBe : B*ε≤B*H := mul_le_mul_of_nonneg_left heH hB
  have hBN : 0≤B*(H^2*(1+Q)) := mul_nonneg hB hnon
  nlinarith

lemma sourceConeCoefficient_uniform_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |sourceConeCoefficient s t x i (z,v)|≤C/‖z‖ := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (sourceAngularProfile i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact (sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s t x z v hz hv hE hB
  have hb := hC ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v) (by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
    · simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB
    · simpa only [mem_closedBall,dist_zero_right] using hv)
  unfold sourceConeCoefficient sourceFixedCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _))
    (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma source_particle_derivative_integrable {s : Solution} {U t P M N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => sourceConeCoefficient s t x i p*
    fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0)
  let A := ball (0:Vec) t \ ({0} : Set Vec)
  have hzprop {z : Vec} (hz : z∈A) : z≠0 ∧ 0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hzr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact ⟨hz.2,by simpa [coneRadius] using sub_pos.mpr hzr,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-z)]⟩
  have hfc : ContinuousOn F (A ×ˢ univ) := by
    intro p hp
    have hh := hzprop hp.1
    have hr := (contDiffAt_coneRadius (k:=1) hh.1.symm).comp p contDiffAt_fst
    have hm : ContinuousAt (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2)) p :=
      ((contDiffAt_const.sub hr).prodMk ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd)).continuousAt
    have hdf : ContinuousAt (fun q : Phase => fderiv ℝ s.f (t-coneRadius 0 q.1,x+q.1,q.2)) p :=
      ((particle_contDiffAt_positive hf hh.2.1 (x+p.1) p.2).continuousAt_fderiv (by simp)).comp (f:=fun q : Phase => (t-coneRadius 0 q.1,x+q.1,q.2)) hm
    exact ((sourceConeCoefficient_contDiffAt hE hB x i hh.1 hh.2.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := sourceConeCoefficient_uniform_bound P M i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_one]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb s t x z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv)
        (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).1 (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).2)
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma magnetic_source_particle_gradient_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H Q N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤Q → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤C*(H+H^2*(1+Q)) := by
  obtain ⟨C,hC,hb⟩ := magnetic_source_annulus_gradient_bound P A M e i hA
  refine ⟨C,hC,?_⟩
  intro s U t H Q N x ht htU hUH hQ hN hf hE hB hc heq hfA hP hEB hDF hfN
  apply norm_integral_ball_of_annulus_bound ht
    (source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN)
  intro ε R hε hεR hRt
  exact hb s U t H Q ε R x (ht.le.trans (htU.trans hUH)) hQ hε hεR hRt htU hUH
    hf hE hB hc heq hfA hP hEB hDF

lemma sourceAngularProfile_derivative_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖fderiv ℝ (sourceAngularProfile i) ((n.1,E,B),v)‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fderiv ℝ (sourceAngularProfile i)) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact ((sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

def sourceReceiverKernel (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceConeCoefficient s t p.1 i p.2

lemma sourceReceiverKernel_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceReceiverKernel s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hn := (contDiffAt_coneDirection (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_fst.add contDiffAt_snd.fst)
  have he := (field_contDiffAt_positive hE ht (p.1+p.2.1)).comp p hm
  have hb := (field_contDiffAt_positive hB ht (p.1+p.2.1)).comp p hm
  have hprof := (sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 p.2.1,s.E (t-coneRadius 0 p.2.1,p.1+p.2.1),s.B (t-coneRadius 0 p.2.1,p.1+p.2.1)),p.2.2))
    (cone_denom_pos p.2.2 _ (coneDirection_norm hz.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd.snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hprof

lemma source_receiver_fderiv_formula {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e =
      (coneRadius 0 z)⁻¹*fderiv ℝ (sourceAngularProfile i)
        ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v)
        ((0,fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),0) := by
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk ((hasFDerivAt_id (𝕜:=ℝ) x).add_const z)
  have he := ((field_contDiffAt_positive hE ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hb := ((field_contDiffAt_positive hB ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hp := ((sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).hasFDerivAt.comp x
      (((hasFDerivAt_const (coneDirection 0 z) x).prodMk (he.prodMk hb)).prodMk (hasFDerivAt_const v x))
  have hh := hp.const_mul ((coneRadius 0 z)⁻¹)
  change HasFDerivAt (fun y => sourceConeCoefficient s t y i (z,v)) _ x at hh
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma physical_source_receiver_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v e : Vec),
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      z≠0 → 0<t-coneRadius 0 z → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e|≤
        C/‖z‖*max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖
          ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖*‖e‖ := by
  obtain ⟨C,hC,hcb⟩ := sourceAngularProfile_derivative_bound P M i
  refine ⟨C,hC,?_⟩
  intro s t x z v e hE hB hz ht hv he hb
  rw [source_receiver_fderiv_formula x z v e i hE hB hz ht,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))]
  let Q := max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖
  have hQ : 0≤Q := (norm_nonneg _).trans (le_max_left _ _)
  have he' : ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_left ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ _) (norm_nonneg ((0:ℝ),e)))
  have hb' : ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_right _ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖) (norm_nonneg ((0:ℝ),e)))
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  have hd := hcb ⟨coneDirection 0 z,hn⟩ v _ _ hv he hb
  have harg : ‖(((0:Vec),fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),
      fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),(0:Vec))‖≤Q*‖e‖ := by
    simp only [Prod.norm_mk,norm_zero]
    exact max_le (max_le (by positivity) (max_le he' hb')) (by positivity)
  have hh := (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hd harg (norm_nonneg _) hC)
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0≤coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg,Q]
  ring

lemma norm_velocity_integral_bound {P C : ℝ} {g : Vec → ℝ}
    (hzero : ∀ v, P<‖v‖ → g v=0) (hb : ∀ v, ‖v‖≤P → |g v|≤C) :
    ‖∫ v,g v‖≤volume.real (closedBall (0:Vec) P)*C := by
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall (0:Vec) P)
    (f:=g) (fun v hv => hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv))]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P)) (f:=g) (C:=C) (by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
    simpa only [Real.norm_eq_abs] using hb v (by simpa only [mem_closedBall,dist_zero_right] using hv))
  simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

lemma retarded_packet_integrable {F : Vec × Phase → ℝ} {t P C : ℝ} (x : Vec)
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖) :
    IntegrableOn (fun z => ∫ v,F (x,z,v)) (ball (0:Vec) t) := by
  let A := ball (0:Vec) t \ ({0}:Set Vec)
  have hC : ContinuousOn (fun p : Phase => F (x,p)) (A ×ˢ univ) := by
    intro p hp
    exact ((hc (x,p) hp.1.2 (by simpa only [mem_ball,dist_zero_right] using hp.1.1)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzero (z : Vec) (hza : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (x,z,v)=0 :=
    hz x z v hza.2 (by simpa only [mem_ball,dist_zero_right] using hza.1)
      (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=volume.real (closedBall (0:Vec) P)*C)
    (by norm_num) (continuousOn_integral_uniform_support (isCompact_closedBall _ _) hC hzero)
  intro z hz0 hzt
  have hzn := norm_pos_iff.mp hz0
  have hh := norm_velocity_integral_bound (hz x z · hzn hzt) (hb x z · hzn hzt)
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh

lemma retarded_packet_spatial_fderiv {F : Vec × Phase → ℝ} {x z v : Vec}
    (hF : DifferentiableAt ℝ F (x,z,v)) (e : Vec) :
    fderiv ℝ (fun y => F (y,z,v)) x e=fderiv ℝ F (x,z,v) (e,0,0) := by
  have hh := hF.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma retarded_packet_derivative_zero {F : Vec × Phase → ℝ} {P t : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z v e : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) (hv : P<‖v‖) :
    fderiv ℝ F (x,z,v) (e,0,0)=0 := by
  rw [←retarded_packet_spatial_fderiv ((hF (x,z,v) hz0 hzt).differentiableAt (by simp)) e]
  have he : (fun y => F (y,z,v))=fun _ => (0:ℝ) := funext (fun y => hz y z v hz0 hzt hv)
  rw [he]
  simp

lemma hasDerivAt_retarded_packet_line {F : Vec × Phase → ℝ} {t P : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z e : Vec) (a : ℝ) (hz0 : z≠0) (hzt : ‖z‖<t) :
    HasDerivAt (fun q : ℝ => ∫ v,F (x+q • e,z,v))
      (∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let G : ℝ × Vec → ℝ := fun p => F (x+p.1 • e,z,p.2)
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hF (x+p.1 • e,z,p.2) hz0 hzt).comp p
      ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk
        (contDiffAt_const.prodMk contDiffAt_snd))
  have hzero (q : ℝ) (_ : q∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : G (q,v)=0 :=
    hz _ z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG.contDiffOn hzero).differentiableAt.hasDerivAt
  rw [show deriv (fun q => ∫ v,G (q,v)) a = fderiv ℝ (fun q => ∫ v,G (q,v)) a 1 from rfl,
    fderiv_integral_uniform_support_apply isOpen_univ (isCompact_closedBall (0:Vec) P)
      (mem_univ a) hG.contDiffOn hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  apply ae_of_all
  intro v
  have hm := ((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
    ((hasFDerivAt_const z (a,v)).prodMk (hasFDerivAt_snd (𝕜:=ℝ)))
  have hh := ((hF (x+a • e,z,v) hz0 hzt).differentiableAt (by simp)).hasFDerivAt.comp (a,v) hm
  change HasFDerivAt G _ (a,v) at hh
  simpa using congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv

lemma hasDerivAt_retarded_packet_integral {F : Vec × Phase → ℝ} {t P C D : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖)
    (x e : Vec) (a : ℝ)
    (hD : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |fderiv ℝ F (x,z,v) (e,0,0)|≤D/‖z‖) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,F (x+q • e,z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let V := volume.real (closedBall (0:Vec) P)
  have hfc := fun p hp ht => (hF p hp ht).continuousAt
  have hdc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t →
      ContinuousAt (fun p => fderiv ℝ F p (e,0,0)) p := by
    intro p hp ht
    exact ((hF p hp ht).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hdz := fun x z v hz0 hzt hv => retarded_packet_derivative_zero hF hz x z v e hz0 hzt hv
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => V*D*‖z‖^(-(1:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (retarded_packet_integrable (x+q • e) hfc hz hb).aestronglyMeasurable))
    (retarded_packet_integrable (x+a • e) hfc hz hb)
    (retarded_packet_integrable (x+a • e) hdc hdz hD).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (1:ℝ)<3 by norm_num)).const_mul (V*D)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hzball
    have hh := norm_velocity_integral_bound (hdz (x+q • e) z · hz0 hzt) (hD (x+q • e) z · hz0 hzt)
    simpa only [V,Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    exact hasDerivAt_retarded_packet_line hF hz x z e q hz0 (by simpa only [mem_ball,dist_zero_right] using hzball)

end RVM.Magnetic

namespace RVM

lemma radial_volterra_majorant_integrable {t C : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn (fun z : Vec => C*g (t-‖z‖)/‖z‖^2) (ball (0:Vec) t) := by
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:Vec) t).exists_bound_of_continuousOn
    (f:=fun z : Vec => C*g (t-‖z‖)) (by fun_prop)
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=D) (by norm_num)
  · intro z hz
    have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz.2
    exact ((continuous_const.mul (hg.comp (continuous_const.sub continuous_norm))).continuousAt.div
      (continuous_norm.pow 2).continuousAt (pow_ne_zero 2 hn)).continuousWithinAt
  · intro z hz hzt
    rw [norm_div,norm_pow,norm_norm,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
    exact (div_le_div_of_nonneg_right (hD z (by
      simpa only [mem_closedBall,dist_zero_right] using hzt.le)) (sq_nonneg _)).trans_eq (by ring)

lemma kernel_volterra_norm_subset {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Vec → W} {t C : ℝ} {S : Set Vec}
    (ht : 0≤t) (hC : 0≤C) (hS : MeasurableSet S) (hsub : S⊆ball (0:Vec) t)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u∈Icc (0:ℝ) t,0≤g u)
    (hb : ∀ z∈S,z≠0 → ‖F z‖≤C*g (t-‖z‖)/‖z‖^2) :
    ‖∫ z in S,F z‖≤(4*Real.pi)*C*(∫ u in Icc (0:ℝ) t,g u) := by
  let G : Vec → ℝ := fun z => C*g (t-‖z‖)/‖z‖^2
  have hG : IntegrableOn G (ball (0:Vec) t) := radial_volterra_majorant_integrable hg
  have hgball (z : Vec) (hz : z∈ball (0:Vec) t) : 0≤g (t-‖z‖) :=
    hg0 _ ⟨by
      have hh : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
      exact sub_nonneg.mpr hh.le,
      sub_le_self _ (norm_nonneg z)⟩
  have hGb (z : Vec) (hz : z∈ball (0:Vec) t) : 0≤G z := by
    have hh := hgball z hz
    dsimp [G]; positivity
  have hh := norm_integral_le_of_norm_le (hG.mono_set hsub) (f:=F) (by
    filter_upwards [ae_restrict_mem hS,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact hb z hz hz0)
  apply hh.trans
  apply (setIntegral_mono_set hG (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hGb z hz) (ae_of_all _ (fun z hz => hsub hz))).trans
  apply (le_abs_self _).trans
  change ‖∫ z in ball (0:Vec) t,G z‖≤_
  apply kernel_volterra_norm ht hC hG hg
  intro z hz hzt
  dsimp [G]
  have hgzt := hg0 (t-‖z‖) ⟨sub_nonneg.mpr hzt,sub_le_self _ (norm_nonneg z)⟩
  rw [abs_of_nonneg (by positivity)]

lemma source_volterra_factor {a b q H : ℝ} (ha : 0≤a) (hb : 0≤b) (hq : 0≤q) (hH : 0≤H) :
    a+(a*q+b)*H≤(a+b)*(1+H)*(1+q) := by
  have hh : a*q+b≤(a+b)*(1+q) := by nlinarith [mul_nonneg hb hq]
  have hh' := mul_le_mul_of_nonneg_right hh hH
  nlinarith [mul_nonneg (add_nonneg ha hb) hq]

lemma source_division_bulk_annulus_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H ε R : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z|≤
        C*(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨Ks,hKs,hks⟩ := physical_source_spatial_bound P M e i
  obtain ⟨Kv,hKv,hkv⟩ := physical_source_velocity_bound P M e i
  let V := volume.real (closedBall (0:Vec) P)*A
  have hV : 0≤V := by dsimp [V]; positivity
  let C := 4*Real.pi*V*(3*Ks+Kv)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s U t H ε R x g hH hg hg0 hε hεR hRt htU hUH hE hB hf hEB hDF
  let L := V*(3*Ks+Kv)*(1+H)
  have hL : 0≤L := by dsimp [L]; positivity
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (z : Vec) (hz : z∈ball (0:Vec) R \ ball (0:Vec) ε) :
      ‖sourceDivisionBulk P s t x e i z‖≤L*(1+g (t-‖z‖))/‖z‖^2 := by
    have hzr : ‖z‖<R ∧ ε≤‖z‖ := by simpa only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hε.trans_le hzr.2)
    have hzpos : 0<‖z‖ := norm_pos_iff.mpr hzn
    have hrad : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
      rw [hrad]
      exact ⟨by linarith,by linarith [norm_nonneg z]⟩
    have hgpos : 0≤g (t-‖z‖) := by
      rw [←hrad]; exact hg0 _ ⟨hu.1.le,hu.2⟩
    let n : Sphere := ⟨‖z‖⁻¹ • z,by
      simp only [mem_sphere,dist_zero_right,norm_smul,norm_inv,norm_norm,
        inv_mul_cancel₀ hzpos.ne']⟩
    have hn : ‖z‖ • (n.1 : Vec)=z := by simp only [n,smul_smul,mul_inv_cancel₀ hzpos.ne',one_smul]
    have hs (v : Vec) (hv : ‖v‖≤P) :
        |divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z|≤
        3*Ks/‖z‖^2+(3*Ks/‖z‖)*g (t-‖z‖) := by
      have hh := hks s t ‖z‖ x v n hE hB hzpos (hzr.1.trans hRt) hv
      rw [hn] at hh
      apply (hh (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2).trans
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by simpa only [hrad] using max_le (hDF _ hu _).1 (hDF _ hu _).2) (by positivity))
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v))
      (C:=A*(((3*Ks+Kv)*(1+H)*(1+g (t-‖z‖)))/‖z‖^2)) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        have hvP : ‖v‖≤P := by simpa only [mem_closedBall,dist_zero_right] using hv
        have hvb := hkv s t x z v hzn hvP (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
        rw [hrad] at hvb
        rw [Real.norm_eq_abs,abs_mul]
        apply mul_le_mul (hf _ ⟨hu.1.le,hu.2⟩ _ v) _ (abs_nonneg _) hA
        exact ((abs_add_le _ _).trans (add_le_add (hs v hvP) hvb)).trans
          ((inverse_source_majorant (by positivity) hKv hgpos hzpos (hzr.1.le.trans (hRt.le.trans (htU.trans hUH)))).trans
            (div_le_div_of_nonneg_right (source_volterra_factor (by positivity) hKv hgpos hH) (sq_nonneg _))))
    exact hh.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ,L,V]; ring)
  have hh := kernel_volterra_norm_subset (hε.le.trans (hεR.trans hRt.le)) hL
    (measurableSet_ball.diff measurableSet_ball)
    (show ball (0:Vec) R \ ball (0:Vec) ε ⊆ ball (0:Vec) t from fun z hz => ball_subset_ball hRt.le hz.1)
    (g:=fun u => 1+g u) (continuous_const.add hg)
    (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity)
    (fun z hz _ => hb z hz)
  rw [Real.norm_eq_abs] at hh
  exact hh.trans_eq (by dsimp [C,L]; ring)

lemma electric_source_annulus_gradient_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H ε R : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C,hC,hb⟩ := source_division_bulk_annulus_volterra_bound P A M e i hA
  obtain ⟨B,hB,hbd⟩ := source_sphere_boundary_bound P M A e i hA
  refine ⟨C+2*B,by positivity,?_⟩
  intro s U t H ε R x g hH hg hg0 hε hεR hRt htU hUH hf hE hB' hc heq hfA hfP hEB hDF
  have hid := electric_source_division_annulus hf hE hB' hc heq htU hε hεR hRt x e i
  rw [hid,source_sphere_support x e i (hε.le.trans hεR) hRt.le htU hfP,
    source_sphere_support x e i hε.le (hεR.trans hRt.le) htU hfP,
    source_bulk_support x e i hRt.le htU hfP]
  have hout := hbd s t U R x (hε.trans_le hεR) hRt.le htU hfA hEB
  have hin := hbd s t U ε x hε (hεR.trans hRt.le) htU hfA hEB
  have hbulk := hb s U t H ε R x g hH hg hg0 hε hεR hRt htU hUH hE hB' hfA hEB hDF
  apply (abs_sub _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add hout hin)) hbulk).trans
  have hRH : R≤H := hRt.le.trans (htU.trans hUH)
  have heH : ε≤H := hεR.trans hRH
  have hW : 0≤(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Icc (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity))
  have hBR : B*R≤B*H := mul_le_mul_of_nonneg_left hRH hB
  have hBe : B*ε≤B*H := mul_le_mul_of_nonneg_left heH hB
  have hBW : 0≤B*((1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := mul_nonneg hB hW
  have hCH := mul_nonneg hC hH
  nlinarith

lemma electric_source_particle_gradient_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H N : ℝ) (x : Vec) (g : ℝ → ℝ),
      0<t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C,hC,hb⟩ := electric_source_annulus_gradient_volterra_bound P A M e i hA
  refine ⟨C,hC,?_⟩
  intro s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN
  apply norm_integral_ball_of_annulus_bound ht
    (source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN)
  intro ε R hε hεR hRt
  exact hb s U t H ε R x g (ht.le.trans (htU.trans hUH)) hg hg0 hε hεR hRt htU hUH
    hf hE hB hc heq hfA hP hEB hDF

lemma source_receiver_packet_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t : ℝ) (g : ℝ → ℝ),t≤U → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*g (t-‖z‖)/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t g htU hg0 hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hQ : 0≤g (t-coneRadius 0 z) := hg0 _ ⟨hu.1.le,hu.2⟩
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*g (t-coneRadius 0 z)*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by simp only [coneRadius,zero_sub,norm_neg]; ring))

lemma electric_source_receiver_integral_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) t,∫ v,sourceReceiverParticlePacket s t e i (x,z,v)|≤
        C*H*(∫ u in Icc (0:ℝ) t,g u) := by
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_volterra_bound P A M e i hA
  let V := volume.real (closedBall (0:Vec) P)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨4*Real.pi*V*K,by positivity,?_⟩
  intro s U t H x g ht htU hUH hg hg0 hE hB hfA hP hEB hDF
  have hH : 0≤H := ht.trans (htU.trans hUH)
  rw [←Real.norm_eq_abs]
  apply (kernel_volterra_norm_subset ht (C:=V*K*H) (by positivity) measurableSet_ball
    (Subset.rfl) hg (fun u hu => hg0 u ⟨hu.1,hu.2.trans htU⟩) ?_).trans_eq (by ring)
  intro z hz hz0
  have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  have hgu : 0≤g (t-‖z‖) := by simpa only [coneRadius,zero_sub,norm_neg] using hg0 _ hu
  have hh := norm_velocity_integral_bound (P:=P) (g:=fun v => sourceReceiverParticlePacket s t e i (x,z,v))
    (fun v hv => by simp only [sourceReceiverParticlePacket,hP _ hu _ v hv,mul_zero])
    (hkb s U t g htU hg0 hE hB hfA hEB hDF x z · hz0 hzt)
  apply hh.trans
  change V*(K*g (t-‖z‖)/‖z‖)≤_
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz0
  calc
    _ = (V*K*g (t-‖z‖)*‖z‖)/‖z‖^2 := by field_simp
    _ ≤ (V*K*g (t-‖z‖)*H)/‖z‖^2 := by gcongr; exact hzt.le.trans (htU.trans hUH)
    _ = _ := by ring

lemma electric_source_deriv_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H N : ℝ) (x : Vec) (g : ℝ → ℝ),
      0<t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
        sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := electric_source_particle_gradient_volterra_bound P A M e i hA
  obtain ⟨C₂,hC₂,hb₂⟩ := electric_source_receiver_integral_volterra_bound P A M e i hA
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN
  obtain ⟨Q₀,hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f:=g) hg.continuousOn
  let Q := max Q₀ 0
  have hQ : 0≤Q := le_max_right _ _
  have hDFconst : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q := by
    intro u hu y
    have hh : g u≤Q := (le_abs_self _).trans ((hQ₀ u ⟨hu.1.le,hu.2⟩).trans (le_max_left _ _))
    exact ⟨(hDF u hu y).1.trans hh,(hDF u hu y).2.trans hh⟩
  have hH : 0≤H := ht.le.trans (htU.trans hUH)
  have hprop (z : Vec) (hz : ‖z‖<t) : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  let R := sourceReceiverParticlePacket s t e i
  let F := fun p : Vec × Phase => fderiv ℝ (sourceWeightedPacket s t i) p (e,0,0)
  have hRc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt R p :=
    fun p hp hpt => sourceReceiverParticlePacket_continuousAt e i hf hE hB hp hpt
  have hRz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → R (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [R,sourceReceiverParticlePacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hweighted : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p :=
    fun p hp hpt => sourceWeightedPacket_contDiffAt i hf hE hB hp (hprop p.2.1 hpt).1
  have hWz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → sourceWeightedPacket s t i (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hFc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p := by
    intro p hp hpt
    exact ((hweighted p hp hpt).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hFz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0 :=
    fun x z v hz hzt hv => retarded_packet_derivative_zero hweighted hWz x z v e hz hzt hv
  have hRi := retarded_packet_integrable x hRc hRz (hkb s U t Q htU hQ hE hB hfA hEB hDFconst)
  have hPi := source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN
  have hsplit : (∫ z in ball (0:Vec) t,∫ v,F (x,z,v))=
      (∫ z in ball (0:Vec) t,∫ v,R (x,z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) := by
    rw [←integral_add hRi hPi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    have hFi := retarded_packet_inner_integrable hFc hFz x z hz0 hzt
    have hRi' := retarded_packet_inner_integrable hRc hRz x z hz0 hzt
    have hh : (∫ v,F (x,z,v))-(∫ v,R (x,z,v))=
        ∫ v,sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
      rw [←integral_sub hFi hRi']
      apply integral_congr_ae
      exact ae_of_all _ (fun v => by
        dsimp [F,R,sourceReceiverParticlePacket]
        rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz0 (hprop z hzt).1]
        ring)
    linarith
  rw [(hasDerivAt_electric_source_integral x e i 0 htU hf hE hB hA hN hQ hP hfA hEB hDFconst hfN).deriv]
  simp only [zero_smul,add_zero]
  change |∫ z in ball (0:Vec) t,∫ v,F (x,z,v)|≤_
  rw [hsplit]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hb₂ s U t H x g ht.le htU hUH hg hg0 hE hB hfA hP hEB hDF)
    (hb₁ s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN)).trans
  have hJ : 0≤∫ u in Icc (0:ℝ) t,1+g u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity)
  have hG : 0≤∫ u in Icc (0:ℝ) t,g u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => hg0 u ⟨hu.1,hu.2.trans htU⟩)
  have hGJ : (∫ u in Icc (0:ℝ) t,g u)≤∫ u in Icc (0:ℝ) t,1+g u :=
    integral_mono hg.integrableOn_Icc (continuous_const.add hg).integrableOn_Icc (fun u => by linarith)
  have hh : C₂*H*(∫ u in Icc (0:ℝ) t,g u)≤C₂*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
    have hmul : H*(∫ u in Icc (0:ℝ) t,g u)≤(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := by
      gcongr; linarith
    have hh' := mul_le_mul_of_nonneg_left (hmul.trans (le_add_of_nonneg_left hH)) hC₂
    nlinarith
  nlinarith

lemma uniform_normalised_integrand_curvature_horizon (A P L R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) R, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a : Vec → ℝ, ∀ E B : Vec → Vec,
      (∀ x, |a x|≤A ∧ ‖E x‖≤L ∧ ‖B x‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      CurvatureBound a Hf → CurvatureBound E H → CurvatureBound B H →
      (∀ x y, |a y-a x|≤M*‖y-x‖) →
      (∀ x y, ‖E y-E x‖≤N*‖y-x‖ ∧ ‖B y-B x‖≤N*‖y-x‖) →
      CurvatureBound (fun x => normalisedPhysicalIntegrand ((r,n,v),(a x,E x,B x)))
        (C*(Hf+H+2*(M+N)^2)) := by
  let K : Set (ℝ × Vec × Vec) := Icc (0:ℝ) R ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  let S : Set (ℝ × Vec × Vec) := closedBall (0:ℝ) A ×ˢ closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : Convex ℝ S := (convex_closedBall _ _).prod ((convex_closedBall _ _).prod (convex_closedBall _ _))
  obtain ⟨C,hC,hb⟩ := compact_parameter_curvature (X:=Vec) hK hS hc
    (g:=normalisedPhysicalIntegrand) (fun q hq => normalisedPhysicalIntegrand_smoothAt
      ((cone_denom_pos q.1.2.2 q.1.2.1 (mem_sphere_zero_iff_norm.mp hq.1.2.1)).ne'))
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a E B hbnd Hf H M N hHf hH hM hN ha hE hB haL hEBL
  apply hb (r,n,v) ⟨hr,mem_sphere_zero_iff_norm.mpr hn,mem_closedBall_zero_iff.mpr hv⟩
    (fun x => (a x,E x,B x))
    (fun x => ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using (hbnd x).1,
      mem_closedBall_zero_iff.mpr (hbnd x).2.1,mem_closedBall_zero_iff.mpr (hbnd x).2.2⟩)
    (Hf+H) (M+N) (add_nonneg hM hN)
  · exact (ha.mono (le_add_of_nonneg_right hH)).prodMk
      ((hE.mono (le_add_of_nonneg_left hHf)).prodMk (hB.mono (le_add_of_nonneg_left hHf)))
  · intro x y
    apply max_le
    · exact (haL x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN) (norm_nonneg _))
    · exact max_le (((hEBL x y).1).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg _)))
        ((hEBL x y).2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg _)))

lemma uniform_physical_integrand_curvature_horizon (A P L R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) R, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a : Vec → ℝ, ∀ E B : Vec → Vec,
      (∀ x, |a x|≤A ∧ ‖E x‖≤L ∧ ‖B x‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      CurvatureBound a Hf → CurvatureBound E H → CurvatureBound B H →
      (∀ x y, |a y-a x|≤M*‖y-x‖) →
      (∀ x y, ‖E y-E x‖≤N*‖y-x‖ ∧ ‖B y-B x‖≤N*‖y-x‖) →
      CurvatureBound (fun x => (a x*(1-dot n (velocity v))) •
        physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x))))
        (C*(Hf+H+2*(M+N)^2)/r^2) := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_integrand_curvature_horizon A P L R
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a E B hbnd Hf H M N hHf hH hM hN ha hE hB haL hEBL x w
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv a E B hbnd Hf H M N hHf hH hM hN ha hE hB haL hEBL x w
  simp only [normalisedPhysicalIntegrand_eq hr.1.ne'] at hh
  rw [show (2:ℝ) • (r^2 • ((a x*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x)))))=
      r^2 • ((2:ℝ) • ((a x*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x))))) by module,
    ← smul_add,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma uniform_physical_integral_curvature_horizon (A P L R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) R, ∀ n : Vec, ‖n‖=1 →
      ∀ f : Vec → Vec → ℝ, (∀ x, Continuous (f x)) → (∀ x, HasCompactSupport (f x)) →
      (∀ x v, |f x v|≤A) → (∀ x v, P<‖v‖ → f x v=0) →
      ∀ E B : Vec → Vec, (∀ x, ‖E x‖≤L ∧ ‖B x‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      (∀ v, CurvatureBound (fun x => f x v) Hf) → CurvatureBound E H → CurvatureBound B H →
      (∀ v x y, |f y v-f x v|≤M*‖y-x‖) →
      (∀ x y, ‖E y-E x‖≤N*‖y-x‖ ∧ ‖B y-B x‖≤N*‖y-x‖) →
      CurvatureBound (fun x => ∫ v : Vec, (f x v*(1-dot n (velocity v))) •
        physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x))))
        (C*(Hf+H+2*(M+N)^2)/r^2) := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_integrand_curvature_horizon A P L R
  refine ⟨K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro r hr n hn f hf hc hab hs E B hEB Hf H M N hHf hH hM hN hfc hEc hBc hfL hEBL
  let g : Vec → Vec → Vec := fun v x => (f x v*(1-dot n (velocity v))) •
    physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E x+cross (velocity v) (B x)))
  have hint (x : Vec) : Integrable (fun v => g v x) :=
    integrable_physical_integrand (hf x) (hc x) hr.1.ne' hn (E x) (B x)
  have he (x : Vec) : (∫ v in closedBall (0:Vec) P, g v x)=∫ v, g v x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [g,hs x v (by simpa only [mem_closedBall_zero_iff,not_le] using hv),zero_mul,zero_smul]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0:Vec) P).measure_lt_top⟩
  have hbound : ∀ᵐ v ∂volume.restrict (closedBall (0:Vec) P),
      CurvatureBound (g v) (K*(Hf+H+2*(M+N)^2)/r^2) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
    exact hk r hr n hn v (mem_closedBall_zero_iff.mp hv) (fun x => f x v) E B
      (fun x => ⟨hab x v,hEB x⟩) Hf H M N hHf hH hM hN (hfc v) hEc hBc (hfL v) hEBL
  have hh := CurvatureBound.integral (fun x => (hint x).restrict) hbound
  simp only [he,Measure.real,Measure.restrict_apply_univ] at hh
  convert hh using 1
  simp only [Measure.real]
  ring

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma boundary_integral_curvature_volterra {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : Vec → U → W} {a : U → W} {t C D : ℝ} {g : ℝ → ℝ}
    (ht : 0≤t) (hC : 0≤C) (hg : Continuous g) (hg0 : ∀ u∈Icc (0:ℝ) t,0≤g u)
    (hF : ∀ x, IntegrableOn (fun z => F z x) (ball (0:Vec) t))
    (ha : CurvatureBound a D)
    (hFc : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t → CurvatureBound (F z) (C*g (t-‖z‖)/‖z‖^2)) :
    CurvatureBound (fun x => a x+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z x)
      (D+C*(∫ u in Icc (0:ℝ) t,g u)) := by
  intro x v
  have hp : IntegrableOn (fun z => F z (x+v)+F z (x-v)) (ball (0:Vec) t) := (hF (x+v)).add (hF (x-v))
  have hm : IntegrableOn (fun z => (2:ℝ) • F z x) (ball (0:Vec) t) := (hF x).smul (2:ℝ)
  have he : (a (x+v)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z (x+v))+
      (a (x-v)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z (x-v))-
      (2:ℝ) • (a x+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z x)=
      (a (x+v)+a (x-v)-(2:ℝ) • a x)+(4*Real.pi)⁻¹ •
        ∫ z in ball (0:Vec) t, (F z (x+v)+F z (x-v)-(2:ℝ) • F z x) := by
    rw [integral_sub hp hm,integral_add (hF (x+v)) (hF (x-v)),integral_smul]
    module
  rw [he]
  have hb := kernel_volterra_norm_subset (F:=fun z => F z (x+v)+F z (x-v)-(2:ℝ) • F z x)
    ht (show 0≤C*‖v‖^2 by positivity) measurableSet_ball (Subset.refl _) hg hg0 (by
      intro z hz hz0
      exact (hFc z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le x v).trans_eq (by ring))
  have hscale : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      (F z (x+v)+F z (x-v)-(2:ℝ) • F z x)‖≤C*(∫ u in Icc (0:ℝ) t,g u)*‖v‖^2 := by
    rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by field_simp)
  exact ((norm_add_le _ _).trans (add_le_add (ha x v) hscale)).trans_eq (by ring)

lemma retarded_density_curvature_volterra (A P L M N R : ℝ) (hM : 0≤M) (hN : 0≤N) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U : ℝ) (g : ℝ → ℝ), U≤R →
      RegularParticle s.f →
      (∀ r∈Icc (0:ℝ) U,0≤g r) →
      (∀ r∈Icc (0:ℝ) U,∀ x v,|s.f (r,x,v)|≤A) →
      (∀ r∈Icc (0:ℝ) U,∀ x v,P<‖v‖ → s.f (r,x,v)=0) →
      (∀ r∈Icc (0:ℝ) U,∀ x,‖s.E (r,x)‖≤L ∧ ‖s.B (r,x)‖≤L) →
      (∀ r∈Icc (0:ℝ) U,∀ v,CurvatureBound (fun x => s.f (r,x,v)) (g r)) →
      (∀ r∈Icc (0:ℝ) U,CurvatureBound (fun x => s.E (r,x)) (g r) ∧ CurvatureBound (fun x => s.B (r,x)) (g r)) →
      (∀ r∈Icc (0:ℝ) U,∀ v x y,|s.f (r,y,v)-s.f (r,x,v)|≤M*‖y-x‖) →
      SpatialFieldLip U N s.E s.B →
      ∀ t∈Icc (0:ℝ) U,∀ z : Vec,0<‖z‖ → ‖z‖≤t →
        CurvatureBound (fun x => retardedElectricDensity s t x (x+z)) (C*(1+g (t-‖z‖))/‖z‖^2) ∧
        CurvatureBound (fun x => retardedMagneticDensity s t x (x+z)) (C*(1+g (t-‖z‖))/‖z‖^2) := by
  obtain ⟨C,hC,hk⟩ := uniform_physical_integral_curvature_horizon A P L R
  refine ⟨C*(2+2*(M+N)^2),by positivity,?_⟩
  intro s U g hUR hreg hg0 hab hs hEB hfc hEBc hfL hEBL t ht z hz hzt
  have htime : t-‖z‖∈Icc (0:ℝ) U := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hn : ‖-(‖z‖⁻¹ • z)‖=1 := by
    simpa only [coneDirection,coneRadius,sub_zero,zero_sub,norm_neg,smul_neg] using coneDirection_norm (x:=(0:Vec)) (y:=z) (norm_pos_iff.mp hz).symm
  have hslice (x : Vec) := hreg.slice htime.1 x
  have he : CurvatureBound (fun x => retardedElectricDensity s t x (x+z))
      (C*(g (t-‖z‖)+g (t-‖z‖)+2*(M+N)^2)/‖z‖^2) := by
    simp only [retardedElectricDensity,coneRadius_add,coneDirection_add]
    exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hUR)⟩ _ hn (fun x v => s.f (t-‖z‖,x+z,v))
      (fun x => (hslice (x+z)).1.continuous) (fun x => (hslice (x+z)).2)
      (fun x v => hab _ htime (x+z) v) (fun x v hv => hs _ htime (x+z) v hv)
      (fun x => s.E (t-‖z‖,x+z)) (fun x => s.B (t-‖z‖,x+z)) (fun x => hEB _ htime (x+z))
      _ _ M N (hg0 _ htime) (hg0 _ htime) hM hN (fun v => (hfc _ htime v).translate z)
      ((hEBc _ htime).1.translate z) ((hEBc _ htime).2.translate z)
      (fun v x y => by simpa only [add_sub_add_right_eq_sub] using hfL _ htime v (x+z) (y+z))
      (fun x y => by simpa only [add_sub_add_right_eq_sub] using hEBL _ htime (x+z) (y+z))
  have hm : C*(g (t-‖z‖)+g (t-‖z‖)+2*(M+N)^2)/‖z‖^2≤
      (C*(2+2*(M+N)^2))*(1+g (t-‖z‖))/‖z‖^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith [mul_nonneg (mul_nonneg hC (sq_nonneg (M+N))) (hg0 _ htime)]
  have he' := he.mono hm
  refine ⟨he',?_⟩
  simpa only [retardedMagneticDensity,coneDirection_add,hn,one_mul] using he'.cross_const_left (-(‖z‖⁻¹ • z))

lemma classical_fields_curvature_volterra_bound {d : Datum} (hd : Admissible d)
    (A P L M N R : ℝ) (hM : 0≤M) (hN : 0≤N) (hR : 0≤R) :
    ∃ D K : ℝ,0≤D ∧ 0≤K ∧ ∀ (s : Solution) (U t : ℝ) (g : ℝ → ℝ),
      ClassicalBefore d s U → SmoothOnFiniteHorizons s → 0<t → t<U → U≤R →
      Continuous g → (∀ r∈Icc (0:ℝ) U,0≤g r) →
      (∀ r∈Icc (0:ℝ) U,∀ x v,|s.f (r,x,v)|≤A) →
      (∀ r∈Icc (0:ℝ) U,∀ x v,P<‖v‖ → s.f (r,x,v)=0) →
      (∀ r∈Icc (0:ℝ) U,∀ x,‖s.E (r,x)‖≤L ∧ ‖s.B (r,x)‖≤L) →
      (∀ r∈Icc (0:ℝ) U,∀ v,CurvatureBound (fun x => s.f (r,x,v)) (g r)) →
      (∀ r∈Icc (0:ℝ) U,CurvatureBound (fun x => s.E (r,x)) (g r) ∧ CurvatureBound (fun x => s.B (r,x)) (g r)) →
      (∀ r∈Icc (0:ℝ) U,∀ v x y,|s.f (r,y,v)-s.f (r,x,v)|≤M*‖y-x‖) →
      SpatialFieldLip U N s.E s.B →
      CurvatureBound (fun x => s.E (t,x)) (D+K*(∫ r in Icc (0:ℝ) t,1+g r)) ∧
      CurvatureBound (fun x => s.B (t,x)) (D+K*(∫ r in Icc (0:ℝ) t,1+g r)) := by
  obtain ⟨K,hK,hden⟩ := retarded_density_curvature_volterra A P L M N R hM hN
  obtain ⟨J,hJ,hJi,hJb⟩ := datum_boundary_global_jets_horizon hd R hR 2
  refine ⟨2*J,K,by positivity,hK,?_⟩
  intro s U t g hs hm ht htU hUR hg hg0 hab hP hEB hfc hEBc hfL hEBL
  have hdt := hden s U g hUR ⟨hs.1,hs.2.2.2.2.2.2.1⟩ hg0 hab hP hEB hfc hEBc hfL hEBL t ⟨ht.le,htU.le⟩
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) U := fun r hr => ⟨hr.1,hr.2.trans htU.le⟩
  have hgb : ∀ r∈Icc (0:ℝ) t,0≤1+g r := fun r hr => by have := hg0 r (hsub hr); linarith
  have hglob : Continuous (fun r => 1+g r) := continuous_const.add hg
  have heq : (fun x => s.E (t,x))=(fun x => electricBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,retardedElectricDensity s t x (x+z)) := by
    funext x
    rw [classical_electric_physical_vector_before hs hm ht htU x]
    congr 1
    ext i
    exact classical_electricConeBoundary_datum_before hs ht x i
  have hbq : (fun x => s.B (t,x))=(fun x => magneticBoundaryField (datumBoundarySolution d) t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,retardedMagneticDensity s t x (x+z)) := by
    funext x
    rw [classical_magnetic_physical_vector_before hs hm ht htU x]
    congr 1
    ext i
    exact classical_magneticConeBoundary_datum_before hs ht x i
  rw [heq,hbq]
  have hb := hJb t ⟨ht,htU.le.trans hUR⟩
  constructor
  · exact boundary_integral_curvature_volterra ht.le hK hglob hgb
      (fun x => integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 ht.le le_rfl x)
      (curvature_of_second_derivative_bound hb.1.1 hJ (fun x => (hb.2 x).1)) (fun z hz hzt => (hdt z hz hzt).1)
  · exact boundary_integral_curvature_volterra ht.le hK hglob hgb
      (fun x => integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.2.2.2.1 ht.le le_rfl x)
      (curvature_of_second_derivative_bound hb.1.2 hJ (fun x => (hb.2 x).2)) (fun z hz hzt => (hdt z hz hzt).2)

end RVM

end

end OAI
