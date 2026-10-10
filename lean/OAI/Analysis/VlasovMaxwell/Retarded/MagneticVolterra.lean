import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SourceWeightedPacket

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

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

lemma magnetic_source_annulus_gradient_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
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
  have hid := magnetic_source_division_annulus hf hE hB' hc heq htU hε hεR hRt x e i
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

lemma magnetic_source_particle_gradient_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
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
  obtain ⟨C,hC,hb⟩ := magnetic_source_annulus_gradient_volterra_bound P A M e i hA
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

lemma magnetic_source_receiver_integral_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
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

lemma magnetic_source_deriv_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
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
  obtain ⟨C₁,hC₁,hb₁⟩ := magnetic_source_particle_gradient_volterra_bound P A M e i hA
  obtain ⟨C₂,hC₂,hb₂⟩ := magnetic_source_receiver_integral_volterra_bound P A M e i hA
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
  rw [(hasDerivAt_magnetic_source_integral x e i 0 htU hf hE hB hA hN hQ hP hfA hEB hDFconst hfN).deriv]
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

end RVM.Magnetic
end

end OAI
