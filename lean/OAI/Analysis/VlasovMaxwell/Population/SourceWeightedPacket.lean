import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.VolterraKernels

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def sourceWeightedPacket (s : Solution) (t : ℝ) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  sourceReceiverKernel s t i p*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

lemma sourceWeightedPacket_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p :=
    (contDiffAt_const.sub hr).prodMk ((contDiffAt_fst.add contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  exact (sourceReceiverKernel_contDiffAt i hE hB hz ht).mul
    ((particle_contDiffAt_positive hf ht (p.1+p.2.1) p.2.2).comp p hm)

lemma sourceWeightedPacket_fderiv {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)=
      fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)*s.f (t-coneRadius 0 z,x+z,v)+
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
  have hk := (sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  have hF := (sourceWeightedPacket_contDiffAt i hf hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  rw [←retarded_packet_spatial_fderiv hF e,←retarded_packet_spatial_fderiv hk e]
  have hkp := hk.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk
    (((hasFDerivAt_id (𝕜:=ℝ) x).add_const z).prodMk (hasFDerivAt_const v x))
  have hfp := (particle_differentiableAt_positive hf ht (x+z) v).hasFDerivAt.comp x hm
  have hh := hkp.mul hfp
  change HasFDerivAt (fun y => sourceWeightedPacket s t i (y,z,v)) _ x at hh
  change HasFDerivAt (fun y => sourceReceiverKernel s t i (y,z,v)) _ x at hkp
  rw [hh.fderiv,hkp.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    zero_apply,smul_eq_mul,Function.comp_apply,id_eq,sourceReceiverKernel]
  ring

lemma source_packet_estimates (P A M N Q : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (s : Solution) (U t : ℝ), t≤U →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceWeightedPacket s t i (x,z,v)|≤C/‖z‖ ∧
      |fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)|≤D/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  obtain ⟨L,hL,hlb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*A,L*Q*‖e‖*A+K*N*‖e‖,by positivity,by positivity,?_⟩
  intro s U t htU hf hE hB hfA hEB hDF hfN x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    have hr : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    rw [hr]
    constructor <;> linarith [norm_nonneg z]
  have hc := hkb s t x z v hz hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd := hlb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤L/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  have hfd : |fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤N*‖e‖ := by
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hu.1 _ _) e]
    exact (ContinuousLinearMap.le_opNorm _ e).trans
      (mul_le_mul_of_nonneg_right (hfN _ ⟨hu.1.le,hu.2⟩ _ v) (norm_nonneg e))
  constructor
  · change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul hc (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz hu.1]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact (add_le_add (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity))
      (mul_le_mul hc hfd (abs_nonneg _) (by positivity))).trans_eq (by ring)

lemma hasDerivAt_magnetic_source_integral {s : Solution} {U t P A M N Q : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ) (htU : t≤U)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hDF : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
      sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ (sourceWeightedPacket s t i) (x+a • e,z,v) (e,0,0)) a := by
  obtain ⟨C,D,hC,hD,hb⟩ := source_packet_estimates P A M N Q e i hA hN hQ
  have hbc := hb s U t htU hf hE hB hfA hEB hDF hfN
  apply hasDerivAt_retarded_packet_integral (F:=sourceWeightedPacket s t i) (P:=P) (C:=C) (D:=D) ?_ ?_
    (fun x z v hz hzt hv => (hbc x z v hz hzt hv).1) x e a (fun x z v hz hzt hv => (hbc x z v hz hzt hv).2)
  · intro p hp ht
    apply sourceWeightedPacket_contDiffAt i hf hE hB hp
    simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  · intro x z v hz hzt hv
    have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
      simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
      constructor <;> linarith [norm_nonneg z]
    simp only [sourceWeightedPacket,hP _ hu _ v hv,mul_zero]

lemma retarded_packet_inner_integrable {F : Vec × Phase → ℝ} {t P : ℝ}
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) : Integrable (fun v => F (x,z,v)) := by
  have hcont : Continuous (fun v => F (x,z,v)) := continuous_iff_continuousAt.mpr (fun v =>
    (hc (x,z,v) hz0 hzt).comp (f:=fun w : Vec => (x,z,w)) (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0:Vec) P)
    (fun v hv => hz x z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)))

lemma norm_integral_ball_inverse_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t C : ℝ} (ht : 0≤t)
    (hb : ∀ z : Vec,z≠0 → ‖z‖<t → ‖F z‖≤C/‖z‖) :
    ‖∫ z in ball (0:Vec) t,F z‖≤2*Real.pi*C*t^2 := by
  have hh := norm_integral_le_of_norm_le ((integrableOn_norm_rpow_neg (R:=t) (show (1:ℝ)<3 by norm_num)).const_mul C) (f:=F) (by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv] using
      hb z hz0 (by simpa only [mem_ball,dist_zero_right] using hz))
  rw [integral_const_mul,integral_ball_norm_rpow_neg (show (1:ℝ)<3 by norm_num) ht] at hh
  norm_num only [show (3:ℝ)-1=2 by norm_num,Real.rpow_two] at hh
  exact hh.trans_eq (by ring)

def sourceReceiverParticlePacket (s : Solution) (t : ℝ) (e : Vec) (i : Fin 3) (p : Vec × Phase) : ℝ :=
  fderiv ℝ (sourceReceiverKernel s t i) p (e,0,0)*s.f (t-coneRadius 0 p.2.1,p.1+p.2.1,p.2.2)

lemma sourceReceiverParticlePacket_continuousAt {s : Solution} {t : ℝ} (e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : ‖p.2.1‖<t) :
    ContinuousAt (sourceReceiverParticlePacket s t e i) p := by
  have hu : 0<t-coneRadius 0 p.2.1 := by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  have hm : ContinuousAt (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p := (continuousAt_const.sub ((contDiffAt_coneRadius (k:=1) hz.symm).continuousAt.comp (f:=fun q : Vec × Phase => q.2.1) continuousAt_snd.fst)).prodMk
    ((continuousAt_fst.add continuousAt_snd.fst).prodMk continuousAt_snd.snd)
  exact (((sourceReceiverKernel_contDiffAt i hE hB hz hu).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).mul
    ((particle_contDiffAt_positive hf hu (p.1+p.2.1) p.2.2).continuousAt.comp (f:=fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) hm)

lemma source_receiver_packet_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t Q : ℝ),t≤U → 0≤Q →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*Q/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t Q htU hQ hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by ring))

lemma magnetic_source_receiver_integral_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t Q : ℝ) (x : Vec),0≤t → t≤U → 0≤Q →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      |∫ z in ball (0:Vec) t,∫ v,sourceReceiverParticlePacket s t e i (x,z,v)|≤C*Q*t^2 := by
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨2*Real.pi*volume.real (closedBall (0:Vec) P)*K,by positivity,?_⟩
  intro s U t Q x ht htU hQ hE hB hfA hP hEB hDF
  rw [←Real.norm_eq_abs]
  apply (norm_integral_ball_inverse_le ht (C:=volume.real (closedBall (0:Vec) P)*K*Q) ?_).trans_eq (by ring)
  intro z hz hzt
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  have hh := norm_velocity_integral_bound (P:=P) (g:=fun v => sourceReceiverParticlePacket s t e i (x,z,v))
    (fun v hv => by simp only [sourceReceiverParticlePacket,hP _ hu _ v hv,mul_zero])
    (hkb s U t Q htU hQ hE hB hfA hEB hDF x z · hz hzt)
  exact hh.trans_eq (by ring)

lemma magnetic_source_deriv_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H Q N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤Q → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
        sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        C*(H+H^2*(1+Q)) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := magnetic_source_particle_gradient_bound P A M e i hA
  obtain ⟨C₂,hC₂,hb₂⟩ := magnetic_source_receiver_integral_bound P A M e i hA
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro s U t H Q N x ht htU hUH hQ hN hf hE hB hc heq hfA hP hEB hDF hfN
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
  have hRi := retarded_packet_integrable x hRc hRz (hkb s U t Q htU hQ hE hB hfA hEB hDF)
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
  rw [(hasDerivAt_magnetic_source_integral x e i 0 htU hf hE hB hA hN hQ hP hfA hEB hDF hfN).deriv]
  simp only [zero_smul,add_zero]
  change |∫ z in ball (0:Vec) t,∫ v,F (x,z,v)|≤_
  rw [hsplit]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hb₂ s U t Q x ht.le htU hQ hE hB hfA hP hEB hDF)
    (hb₁ s U t H Q N x ht htU hUH hQ hN hf hE hB hc heq hfA hP hEB hDF hfN)).trans
  have htH : t^2≤H^2 := by nlinarith [htU.trans hUH]
  have hh : C₂*Q*t^2≤C₂*(H+H^2*(1+Q)) := by
    calc
      _ ≤ C₂*Q*H^2 := mul_le_mul_of_nonneg_left htH (mul_nonneg hC₂ hQ)
      _ ≤ _ := by nlinarith [mul_nonneg hC₂ hH,mul_nonneg hC₂ (sq_nonneg H)]
  nlinarith

end RVM.Magnetic

end

end OAI
