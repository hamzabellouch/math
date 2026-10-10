import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.SourceVelocityProfile

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

section
attribute [local instance] Measure.Subtype.measureSpace
local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

lemma singular_radial_log_bound_norm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : ℝ → W} {t H A N : ℝ} (ht : 0<t) (htH : t≤H) (hA : 0≤A) (hN : 0≤N)
    (hg : ContinuousOn g (Ioc (0:ℝ) t))
    (hn : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤N)
    (ha : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤A/r) :
    IntegrableOn g (Ioc (0:ℝ) t) ∧
      (∫r in Ioc (0:ℝ) t,‖g r‖)≤1+A*(Real.log (max 1 H)+Real.log (1+N)) := by
  have hh := singular_radial_log_bound ht htH hA hN hg.norm
    (fun r hr => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hn r hr)
    (fun r hr => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using ha r hr)
  exact ⟨(singular_radial_log_bound ht htH hA hN hg hn ha).1,
    (le_abs_self _).trans hh.2⟩

lemma integral_annulus_polar_radial {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec → W} {ε R : ℝ} (hε : 0<ε)
    (hg : ContinuousOn g {z | ε≤‖z‖ ∧ ‖z‖≤R}) :
    (∫z in ball (0:Vec) R \ ball (0:Vec) ε,g z)=
      ∫r in Ico ε R, ∫n : Sphere,r^2 • g (r • n.1) ∂sphereMeasure := by
  have hclosed : {z : Vec | ε≤‖z‖ ∧ ‖z‖≤R}=closedBall (0:Vec) R \ ball (0:Vec) ε := by
    ext z
    simp only [mem_ofPred_eq,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt]
    exact and_comm
  have hgi : IntegrableOn g (ball (0:Vec) R \ ball (0:Vec) ε) := by
    have hcomp : IsCompact {z : Vec | ε≤‖z‖ ∧ ‖z‖≤R} := by
      rw [hclosed]
      exact (isCompact_closedBall _ _).diff isOpen_ball
    exact (hg.integrableOn_compact hcomp).mono_set (by
      intro z hz
      simp only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] at hz
      exact ⟨hz.2,hz.1.le⟩)
  have hfun : ContinuousOn (fun p : ℝ × Sphere => p.1^2 • g (p.1 • p.2.1)) (Icc ε R ×ˢ univ) := by
    apply (continuous_fst.pow 2).continuousOn.smul
    apply hg.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    have hr : 0≤p.1 := hε.le.trans hp.1.1
    change ε≤‖p.1 • p.2.1‖ ∧ ‖p.1 • p.2.1‖≤R
    simpa only [mem_Icc,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one] using hp.1
  have hi : Integrable (fun p : ℝ × Sphere => p.1^2 • g (p.1 • p.2.1))
      ((volume.restrict (Ico ε R)).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [←Measure.restrict_univ (μ:=sphereMeasure),Measure.prod_restrict]
    exact (hfun.integrableOn_compact (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono Ico_subset_Icc_self Subset.rfl)
  rw [integral_annulus_polar hε hgi]
  exact (integral_integral_swap hi).symm

def transportSingularBulk (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P, divergence (transportSpatialFlux v e i) z * f (t-coneRadius 0 z,x+z,v)

lemma transportSingularBulk_continuousOn {P t U ε R : ℝ} {f : Particle}
    (x e : Vec) (i : Fin 3) (hε : 0<ε) (hRt : R≤t) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    ContinuousOn (transportSingularBulk P f t x e i) {z | ε≤‖z‖ ∧ ‖z‖≤R} := by
  let K := closedBall (0:Vec) P
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  let G : Vec × K → ℝ := fun p => divergence (transportSpatialFlux p.2.1 e i) p.1 *
    f (t-coneRadius 0 p.1,x+p.1,p.2.1)
  have hdiv : ContinuousOn (fun p : Vec × K => divergence (transportSpatialFlux p.2.1 e i) p.1)
      ({z | ε≤‖z‖ ∧ ‖z‖≤R} ×ˢ univ) := by
    apply (continuousOn_transportSpatialDivergence e i).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    change p.1≠0
    exact norm_pos_iff.mp (hε.trans_le hp.1.1)
  have hm : Continuous (fun p : Vec × K => (t-coneRadius 0 p.1,x+p.1,p.2.1)) := by
    unfold coneRadius
    fun_prop
  have hG : ContinuousOn G ({z | ε≤‖z‖ ∧ ‖z‖≤R} ×ˢ univ) := by
    apply hdiv.mul (hf.comp hm.continuousOn ?_)
    intro p hp
    change t-coneRadius 0 p.1∈Icc (0:ℝ) U
    simp only [coneRadius,zero_sub,norm_neg]
    exact ⟨by linarith [hp.1.2],by linarith [norm_nonneg p.1]⟩
  have hh : ContinuousOn (fun z => ∫ v : K, G (z,v)) {z | ε≤‖z‖ ∧ ‖z‖≤R} := by
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hG
    intro z v _ hv
    exact (hv (mem_univ v)).elim
  apply hh.congr
  intro z hz
  exact (integral_subtype measurableSet_closedBall
    (fun v : Vec => divergence (transportSpatialFlux v e i) z * f (t-coneRadius 0 z,x+z,v))).symm

lemma transportSingularBulk_shell {P t U r : ℝ} {f : Particle} (x e : Vec) (i : Fin 3)
    (hr : 0<r) (hrt : r≤t) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    (∫ n : Sphere,r^2 • transportSingularBulk P f t x e i (r • n.1) ∂sphereMeasure)=
      transportSingularShell P f t x e i r := by
  let K := closedBall (0:Vec) P
  have he (n : Sphere) : r^2 • transportSingularBulk P f t x e i (r • n.1)=
      r⁻¹*(∫ v in K, divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v)) := by
    have hn : (n:Vec)≠0 := by
      intro h
      have := sphere_norm n
      rw [h,norm_zero] at this
      norm_num at this
    have hd (v : Vec) := divergence_degree_neg_two
      (fun a ha z => transportSpatialFlux_homogeneous v e i ha z)
      (fun z hz => (transportSpatialFlux_contDiffAt v e i hz).differentiableAt (by simp)) hr hn
    have hrad : coneRadius 0 (r • n.1)=r := by
      simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr.le,sphere_norm,mul_one]
    simp only [transportSingularBulk,hd,hrad,smul_eq_mul,mul_assoc,integral_const_mul]
    rw [←mul_assoc]
    congr 1
    field_simp
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  have hfun : ContinuousOn (fun p : Sphere × Vec => divergence (transportSpatialFlux p.2 e i) p.1.1 *
      f (t-r,x+r • p.1.1,p.2)) (univ ×ˢ K) := by
    have hc : ContinuousOn (fun p : Sphere × Vec => divergence (transportSpatialFlux p.2 e i) p.1.1)
        (univ ×ˢ K) := by
      apply (continuousOn_transportSpatialDivergence e i).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      intro p hp
      change (p.1:Vec)≠0
      intro hh
      have := sphere_norm p.1
      rw [hh,norm_zero] at this
      norm_num at this
    apply hc.mul
    apply hf.comp (by fun_prop : Continuous (fun p : Sphere × Vec => (t-r,x+r • p.1.1,p.2))).continuousOn
    intro p hp
    exact ⟨by linarith,by linarith⟩
  have hi : Integrable (fun p : Sphere × Vec => divergence (transportSpatialFlux p.2 e i) p.1.1 *
      f (t-r,x+r • p.1.1,p.2)) (sphereMeasure.prod (volume.restrict K)) := by
    rw [←Measure.restrict_univ (μ:=sphereMeasure),Measure.prod_restrict]
    exact hfun.integrableOn_compact (isCompact_univ.prod (isCompact_closedBall _ _))
  exact integral_integral_swap hi

lemma transportSingularBulk_annulus {P t U ε R : ℝ} {f : Particle}
    (x e : Vec) (i : Fin 3) (hε : 0<ε) (hRt : R≤t) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P f t x e i z)=
      ∫ r in Ico ε R,transportSingularShell P f t x e i r := by
  rw [integral_annulus_polar_radial hε (transportSingularBulk_continuousOn x e i hε hRt htU hf)]
  apply setIntegral_congr_fun measurableSet_Ico
  intro r hr
  exact transportSingularBulk_shell x e i (hε.trans_le hr.1) (hr.2.le.trans hRt) htU hf

lemma physical_transport_annulus_log_bound (P H A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (U t N ε R : ℝ) (f : Particle),
      0<t → t≤U → U≤H → 0≤N → 0<ε → R≤t →
      ContinuousOn f {p | p.1∈Icc (0:ℝ) U} →
      (∀ s∈Icc (0:ℝ) U, ∀ v, Differentiable ℝ (fun y => f (s,y,v))) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => f (s,z,v)) y‖≤N) →
      ∀ x, |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P f t x e i z|≤
        1+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨K,hK,hkb⟩ := transportSpatialDivergence_uniform_bound P e i
  let C := volume.real (closedBall (0:Vec) P)*(4*Real.pi)*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,C*A,hC,mul_nonneg hC hA,?_⟩
  intro U t N ε R f ht htU hUH hN hε hRt hfc hfd hfA hfN x
  have htt : t∈Icc (0:ℝ) U := ⟨ht.le,htU⟩
  have hh := singular_radial_log_bound_norm ht (htU.trans hUH) (mul_nonneg hC hA) (mul_nonneg hC hN)
    (transportSingularShell_continuousOn x e i hfc htt)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).1)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).2)
  rw [transportSingularBulk_annulus x e i hε hRt htU hfc]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply le_trans _ hh.2
  exact integral_mono_measure (Measure.restrict_mono_set volume (by
    intro r hr
    exact ⟨hε.trans_le hr.1,hr.2.le.trans hRt⟩))
    (Filter.Eventually.of_forall (fun r => norm_nonneg _)) hh.1.norm

end

lemma norm_integral_annulus_inverse_sq_le {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {F : Vec → W} {ε R C : ℝ} (hε : 0<ε) (hεR : ε≤R)
    (hC : 0≤C) (hF : ∀ z∈ball (0:Vec) R \ ball (0:Vec) ε, ‖F z‖≤C/‖z‖^2) :
    ‖∫ z in ball (0:Vec) R \ ball (0:Vec) ε,F z‖≤4*Real.pi*C*R := by
  have hR : 0≤R := hε.le.trans hεR
  by_cases hi : IntegrableOn F (ball (0:Vec) R \ ball (0:Vec) ε)
  · rw [integral_annulus_polar hε hi]
    have hn (n : Sphere) : ‖∫ r in Ico ε R,r^2 • F (r • n.1)‖≤C*R := by
      have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (Ico ε R))
        (f:=fun r => r^2 • F (r • n.1)) (C:=C) (by
          filter_upwards [ae_restrict_mem measurableSet_Ico] with r hr
          have hr0 : 0<r := hε.trans_le hr.1
          have hnorm : ‖r • n.1‖=r := by
            simp only [norm_smul,Real.norm_of_nonneg hr0.le,sphere_norm,mul_one]
          have hb := hF (r • n.1) (by
            simp only [Set.mem_sdiff,mem_ball,dist_zero_right,hnorm,not_lt]
            exact ⟨hr.2,hr.1⟩)
          rw [hnorm] at hb
          rw [norm_smul,Real.norm_of_nonneg (sq_nonneg r)]
          exact (mul_le_mul_of_nonneg_left hb (sq_nonneg r)).trans_eq (by field_simp))
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ico,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hεR)] at hh
      exact hh.trans (by nlinarith)
    have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hn)
    simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  · rw [integral_undef hi,norm_zero]
    positivity

def transportVelocityBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P, s.f (t-coneRadius 0 z,x+z,v)*
    divergence (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v

lemma transport_velocity_annulus_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t ε R : ℝ) (x : Vec),
      0<ε → ε≤R → R≤t → t≤U → U≤H →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportVelocityBulk P s t x e i z|≤C := by
  obtain ⟨K,hK,hkb⟩ := physical_transport_velocity_bound P M e i
  let D := volume.real (closedBall (0:Vec) P)*A*K
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨4*Real.pi*D*H,by positivity,?_⟩
  intro s U t ε R x hε hεR hRt htU hUH hf hEB
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (z : Vec) (hz : z∈ball (0:Vec) R \ ball (0:Vec) ε) :
      ‖transportVelocityBulk P s t x e i z‖≤D/‖z‖^2 := by
    have hzr : ‖z‖<R ∧ ε≤‖z‖ := by simpa only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hε.trans_le hzr.2)
    have hrad : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
      rw [hrad]
      exact ⟨by linarith,by linarith [norm_nonneg z]⟩
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-coneRadius 0 z,x+z,v)*
        divergence (fun w => transportConeCoefficient i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)
      (C:=A*(K/‖z‖^2)) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        have hvP : ‖v‖≤P := by simpa only [mem_closedBall,dist_zero_right] using hv
        have hh := hkb s t x z v hzn hvP (hEB _ hu _).1 (hEB _ hu _).2
        rw [hrad] at hh
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (hf _ hu _ v) hh (abs_nonneg _) hA)
    exact hh.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ,D]; ring)
  rw [←Real.norm_eq_abs]
  exact (norm_integral_annulus_inverse_sq_le hε hεR hD hb).trans
    (mul_le_mul_of_nonneg_left (hRt.trans (htU.trans hUH)) (by positivity))

lemma transport_velocity_divergence_continuousOn {s : Solution} {t : ℝ} (x e : Vec) (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace) :
    ContinuousOn (fun p : Phase => divergence (fun w => transportConeCoefficient i (p.1,w) •
      (coneSpatialCoefficient 0 p.1 w e • coneLorentz s t x (p.1,w))) p.2)
      (retardedSpaceDomain t 0 ×ˢ univ) := by
  have hk : ContDiffOn ℝ 1 (transportConeCoefficient i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (transportConeCoefficient_contDiffAt i hp.1.1.symm).contDiffWithinAt
  have hco : ContDiffOn ℝ 1 (fun z : Phase => coneSpatialCoefficient 0 z.1 z.2 e)
      (retardedSpaceDomain t 0 ×ˢ univ) := fun p hp =>
    (contDiffAt_coneSpatialCoefficient_phase hp.1.1).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  exact (continuousOn_phase_divergences (isOpen_retardedSpaceDomain t 0) (hk.smul (hco.smul hK))).2

lemma shifted_particle_continuousOn {f : Particle} {t U : ℝ} (x : Vec) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    ContinuousOn (fun p : Phase => f (t-coneRadius 0 p.1,x+p.1,p.2))
      (retardedSpaceDomain t 0 ×ˢ univ) := by
  apply hf.comp (by unfold coneRadius; fun_prop : Continuous
    (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2))).continuousOn
  intro p hp
  exact ⟨hp.1.2.le,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-p.1)]⟩

lemma transport_bulk_split {s : Solution} {t U P ε R : ℝ} (x e : Vec) (i : Fin 3)
    (htU : t≤U) (hε : 0<ε) (hRt : R<t)
    (hf : ContinuousOn s.f {p | p.1∈Icc (0:ℝ) U})
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
      (divergence (transportSpatialFlux v e i) z+
        divergence (fun w => transportConeCoefficient i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)) =
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P s.f t x e i z)+
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportVelocityBulk P s t x e i z) := by
  let A := ball (0:Vec) R \ ball (0:Vec) ε
  let C := closedBall (0:Vec) R \ ball (0:Vec) ε
  let U₀ := retardedSpaceDomain t 0
  let F : Phase → ℝ := fun p => s.f (t-coneRadius 0 p.1,x+p.1,p.2)
  let D : Phase → ℝ := fun p => divergence (transportSpatialFlux p.2 e i) p.1
  let V : Phase → ℝ := fun p => divergence (fun w => transportConeCoefficient i (p.1,w) •
    (coneSpatialCoefficient 0 p.1 w e • coneLorentz s t x (p.1,w))) p.2
  have hfC : ContinuousOn F (U₀ ×ˢ univ) := shifted_particle_continuousOn x htU hf
  have hDC : ContinuousOn D (U₀ ×ˢ univ) := (continuousOn_transportSpatialDivergence e i).mono
    (by intro p hp; exact hp.1.1.symm)
  have hVC : ContinuousOn V (U₀ ×ˢ univ) := transport_velocity_divergence_continuousOn x e i hE hB
  have hzero (z : Vec) (hz : z∈U₀) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    apply hP _ ⟨hz.2.le,?_⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
    dsimp [coneRadius]
    linarith [norm_nonneg ((0:Vec)-z)]
  have hAU : A⊆C := fun z hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hCU : C⊆U₀ := by
    intro z hz
    have hrz : ‖z‖≤R ∧ ε≤‖z‖ := by simpa only [C,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt] using hz
    exact ⟨(norm_pos_iff.mp (hε.trans_le hrz.2)).symm,by simpa [coneRadius] using sub_pos.mpr (hrz.1.trans_lt hRt)⟩
  have hcompact : IsCompact C := (isCompact_closedBall _ _).diff isOpen_ball
  have hdI : IntegrableOn (fun z => ∫ v, F (z,v)*D (z,v)) A :=
    ((continuousOn_integral_uniform_support (isCompact_closedBall (0:Vec) P) (hfC.mul hDC)
      (by intro z hz v hv; dsimp only [Pi.mul_apply]; rw [hzero z hz v hv,zero_mul])).mono hCU).integrableOn_compact hcompact |>.mono_set hAU
  have hvI : IntegrableOn (fun z => ∫ v, F (z,v)*V (z,v)) A :=
    ((continuousOn_integral_uniform_support (isCompact_closedBall (0:Vec) P) (hfC.mul hVC)
      (by intro z hz v hv; dsimp only [Pi.mul_apply]; rw [hzero z hz v hv,zero_mul])).mono hCU).integrableOn_compact hcompact |>.mono_set hAU
  have hdi (z : Vec) (hz : z∈U₀) : Integrable (fun v => F (z,v)*D (z,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hfC.mul hDC).comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz,mem_univ _⟩)
    · exact compactSupport_of_zero_off (isCompact_closedBall (0:Vec) P) (fun v hv => by rw [hzero z hz v hv,zero_mul])
  have hvi (z : Vec) (hz : z∈U₀) : Integrable (fun v => F (z,v)*V (z,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hfC.mul hVC).comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz,mem_univ _⟩)
    · exact compactSupport_of_zero_off (isCompact_closedBall (0:Vec) P) (fun v hv => by rw [hzero z hz v hv,zero_mul])
  calc
    _ = ∫ z in A, (∫ v,F (z,v)*D (z,v))+(∫ v,F (z,v)*V (z,v)) := by
      apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
      intro z hz
      simp only [mul_add]
      exact integral_add (hdi z (hCU (hAU hz))) (hvi z (hCU (hAU hz)))
    _ = (∫ z in A,∫ v,F (z,v)*D (z,v))+(∫ z in A,∫ v,F (z,v)*V (z,v)) := integral_add hdI hvI
    _ = _ := by
      congr 1
      · apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
        intro z hz
        rw [transportSingularBulk]
        simpa only [F,D,mul_comm] using
          (setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=volume) (f:=fun v => F (z,v)*D (z,v)) (fun v hv => by
            change F (z,v)*D (z,v)=0
            rw [hzero z (hCU (hAU hz)) v hv,zero_mul])).symm
      · apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
        intro z hz
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by
          change F (z,v)*V (z,v)=0
          rw [hzero z (hCU (hAU hz)) v hv,zero_mul])).symm

lemma transport_sphere_support {s : Solution} {t U P r : ℝ} (x e : Vec) (i : Fin 3)
    (hr : 0≤r) (hrt : r≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ n : Sphere,r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) •
      transportSpatialFlux v e i (r • n.1)) ∂sphereMeasure) =
    (∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) •
      transportSpatialFlux v e i (r • n.1)) ∂sphereMeasure) := by
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    congr 2
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro v hv
    rw [hP _ ⟨by linarith,by linarith⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_smul])

lemma abs_sub_sub_add_le (a b c d : ℝ) :
    |a-b-(c+d)|≤|a|+|b|+|c|+|d| := by
  linarith [abs_sub a b,abs_sub (a-b) (c+d),abs_add_le c d]

lemma magnetic_transport_annulus_gradient_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N ε R : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N → 0<ε → ε≤R → R<t →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨Cb,hCb,hcb⟩ := transport_sphere_boundary_bound P A e i hA
  obtain ⟨Cv,hCv,hcv⟩ := transport_velocity_annulus_bound P A M H e i hA hH
  obtain ⟨C,D,hC,hD,hcd⟩ := physical_transport_annulus_log_bound P H A e i hA
  refine ⟨2*Cb+Cv+1,C,D,by positivity,hC,hD,?_⟩
  intro s U t N ε R x ht htU hUH hN hε hεR hRt hf hE hB hc heq hfA hP hEB hfN
  have hfc : ContinuousOn s.f {p | p.1∈Icc (0:ℝ) U} := hf.continuousOn.mono (fun p hp => hp.1)
  have hfd (u : ℝ) (hu : u∈Icc (0:ℝ) U) (v : Vec) : Differentiable ℝ (fun y => s.f (u,y,v)) := by
    have hh : ContDiff ℝ 1 (fun y => s.f (u,y,v)) := by
      apply contDiffOn_univ.mp
      exact hf.comp ((contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contDiffOn)
        (fun _ _ => hu.1)
    exact hh.differentiable (by simp)
  have hbR := hcb s.f t U R x (hε.trans_le hεR) hRt.le htU hfA
  have hbε := hcb s.f t U ε x hε (hεR.trans hRt.le) htU hfA
  have hbv := hcv s U t ε R x hε hεR hRt.le htU hUH hfA hEB
  have hbs := hcd U t N ε R s.f ht htU hUH hN hε hRt.le hfc hfd hfA hfN x
  rw [magnetic_transport_division_annulus hf hE hB hc heq htU hε hεR hRt x e i,
    transport_sphere_support x e i (hε.le.trans hεR) hRt.le htU hP,
    transport_sphere_support x e i hε.le (hεR.trans hRt.le) htU hP,
    transport_bulk_split x e i htU hε hRt hfc hE hB hP]
  calc
    _ ≤ |∫ n : Sphere,R^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-R,x+R • n.1,v) •
        transportSpatialFlux v e i (R • n.1)) ∂sphereMeasure|+
      |∫ n : Sphere,ε^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-ε,x+ε • n.1,v) •
        transportSpatialFlux v e i (ε • n.1)) ∂sphereMeasure|+
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P s.f t x e i z|+
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportVelocityBulk P s t x e i z| := by
        exact abs_sub_sub_add_le _ _ _ _
    _ ≤ _ := by linarith

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

lemma sourceFixedFlux_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖sourceFixedFlux v E B e i n.1‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ
    (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)
  have hK : IsCompact K := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : ContinuousOn (sourceJointFlux e i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    have hz : p.1.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact (sourceJointFlux_contDiffAt e i hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,v),(E,B)) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_closedBall,dist_zero_right] using hv⟩,
    by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩

lemma source_sphere_rescale (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {r : ℝ} (hr : 0<r) (n : Sphere) :
    r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) =
    r*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1) := by
  have he : (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1))=
      r⁻¹ • ∫ v in closedBall (0:Vec) P,
        s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
          (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1 := by
    rw [←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only
      rw [sourceFixedFlux_homogeneous v _ _ e i hr]
      simp only [smul_smul,mul_comm])
  rw [he,dot_smul_right]
  field_simp

lemma source_sphere_boundary_bound (P M A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t U r : ℝ) (x : Vec),
      0<r → r≤t → t≤U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      |∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
        s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
          (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) ∂sphereMeasure|≤C*r := by
  obtain ⟨K,hK,hkb⟩ := sourceFixedFlux_uniform_bound P M e i
  let C := volume.real (closedBall (0:Vec) P)*A*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨(4*Real.pi)*C,mul_nonneg (by positivity) hC,?_⟩
  intro s t U r x hr hrt htU hf hEB
  simp_rw [source_sphere_rescale P s t x e i hr]
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith⟩
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (n : Sphere) : ‖r*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1)‖≤r*C := by
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1) (C:=A*K) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hf _ hs _ v)
          (hkb n v _ _ (by simpa only [mem_closedBall,dist_zero_right] using hv)
            (hEB _ hs _).1 (hEB _ hs _).2) (norm_nonneg _) hA)
    have hd := abs_real_inner_le_norm n.1
      (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1)
    rw [sphere_norm,one_mul] at hd
    rw [norm_mul,Real.norm_of_nonneg hr.le,dot_eq_inner,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hd.trans (by
      simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,C,mul_assoc,mul_comm,mul_left_comm] using hh)) hr.le
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_comm,mul_assoc,mul_left_comm] using hh

def sourceDivisionBulk (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  ∫ v in closedBall (0:Vec) P,s.f (t-coneRadius 0 z,x+z,v)*
    (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
      divergence (fun w => sourceConeCoefficient s t x i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)

lemma inverse_source_majorant {a b Q r H : ℝ} (ha : 0≤a) (hb : 0≤b) (hQ : 0≤Q)
    (hr : 0<r) (hrH : r≤H) :
    a/r^2+(a/r)*Q+b/r≤(a+(a*Q+b)*H)/r^2 := by
  calc
    _ = (a+(a*Q+b)*r)/r^2 := by field_simp; ring
    _ ≤ _ := by gcongr

lemma source_division_bulk_annulus_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H Q ε R : ℝ) (x : Vec),
      0≤H → 0≤Q → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z|≤
        C*(H+H^2*(1+Q)) := by
  obtain ⟨Ks,hKs,hks⟩ := physical_source_spatial_bound P M e i
  obtain ⟨Kv,hKv,hkv⟩ := physical_source_velocity_bound P M e i
  let V := volume.real (closedBall (0:Vec) P)*A
  have hV : 0≤V := by dsimp [V]; positivity
  let C := 4*Real.pi*V*(3*Ks+Kv)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s U t H Q ε R x hH hQ hε hεR hRt htU hUH hE hB hf hEB hDF
  let L := V*(3*Ks+(3*Ks*Q+Kv)*H)
  have hL : 0≤L := by dsimp [L]; positivity
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (z : Vec) (hz : z∈ball (0:Vec) R \ ball (0:Vec) ε) :
      ‖sourceDivisionBulk P s t x e i z‖≤L/‖z‖^2 := by
    have hzr : ‖z‖<R ∧ ε≤‖z‖ := by simpa only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hε.trans_le hzr.2)
    have hzpos : 0<‖z‖ := norm_pos_iff.mpr hzn
    have hrad : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
      rw [hrad]
      exact ⟨by linarith,by linarith [norm_nonneg z]⟩
    let n : Sphere := ⟨‖z‖⁻¹ • z,by
      simp only [mem_sphere,dist_zero_right,norm_smul,norm_inv,norm_norm,
        inv_mul_cancel₀ hzpos.ne']⟩
    have hn : ‖z‖ • (n.1 : Vec)=z := by simp only [n,smul_smul,mul_inv_cancel₀ hzpos.ne',one_smul]
    have hs (v : Vec) (hv : ‖v‖≤P) :
        |divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z|≤
        3*Ks/‖z‖^2+(3*Ks/‖z‖)*Q := by
      have hh := hks s t ‖z‖ x v n hE hB hzpos (hzr.1.trans hRt) hv
      rw [hn] at hh
      apply (hh (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2).trans
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (max_le (hDF _ hu _).1 (hDF _ hu _).2) (by positivity))
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v))
      (C:=A*((3*Ks+(3*Ks*Q+Kv)*H)/‖z‖^2)) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        have hvP : ‖v‖≤P := by simpa only [mem_closedBall,dist_zero_right] using hv
        have hvb := hkv s t x z v hzn hvP (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
        rw [hrad] at hvb
        rw [Real.norm_eq_abs,abs_mul]
        apply mul_le_mul (hf _ ⟨hu.1.le,hu.2⟩ _ v) _ (abs_nonneg _) hA
        exact ((abs_add_le _ _).trans (add_le_add (hs v hvP) hvb)).trans
          (inverse_source_majorant (by positivity) hKv hQ hzpos (hzr.1.le.trans (hRt.le.trans (htU.trans hUH)))))
    exact hh.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ,L,V]; ring)
  have hh := norm_integral_annulus_inverse_sq_le hε hεR hL hb
  rw [Real.norm_eq_abs] at hh
  apply hh.trans
  calc
    4*Real.pi*L*R ≤ 4*Real.pi*L*H := by gcongr; exact hRt.le.trans (htU.trans hUH)
    _ ≤ C*(H+H^2*(1+Q)) := by
      dsimp [L,C]
      have hcoef : 3*Ks+(3*Ks*Q+Kv)*H≤(3*Ks+Kv)*(1+H*(1+Q)) := by
        nlinarith [mul_nonneg hKs hH,mul_nonneg (mul_nonneg hKv hH) hQ]
      have hh' := mul_le_mul_of_nonneg_left hcoef (show 0≤4*Real.pi*V*H by positivity)
      nlinarith

end RVM.Magnetic

end

end OAI
