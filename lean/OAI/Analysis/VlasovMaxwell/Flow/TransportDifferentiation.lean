import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.LogSingularBound
import OAI.Analysis.VlasovMaxwell.Geometry.PhysicalDivision

namespace OAI

noncomputable section

namespace RVM


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


section
local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

lemma sphere_mean_zero_lipschitz_bound {a : Sphere → ℝ} {F : Vec → ℝ} {x : Vec}
    {r C N : ℝ} (ha : Continuous a) (hF : Continuous F)
    (hmean : (∫n : Sphere,a n ∂sphereMeasure)=0)
    (hC : 0≤C) (hab : ∀ n, |a n|≤C) (hr : 0≤r)
    (_hN : 0≤N) (hLip : ∀ y, |F y-F x|≤N*‖y-x‖) :
    |∫ n : Sphere, a n*F (x+r • n.1) ∂sphereMeasure|≤(4*Real.pi)*C*N*r := by
  have hc : Continuous (fun n : Sphere => a n*F (x+r • n.1)) :=
    by fun_prop
  have hi := hc.integrable_of_hasCompactSupport (μ:=sphereMeasure) (HasCompactSupport.of_compactSpace _)
  have hai := ha.integrable_of_hasCompactSupport (μ:=sphereMeasure) (HasCompactSupport.of_compactSpace _)
  have he : (∫ n : Sphere,a n*(F (x+r • n.1)-F x) ∂sphereMeasure)=
      ∫ n : Sphere,a n*F (x+r • n.1) ∂sphereMeasure := by
    simp_rw [mul_sub]
    rw [integral_sub hi (hai.mul_const _),integral_mul_const,hmean,zero_mul,sub_zero]
  rw [←he]
  have hb : ∀ n : Sphere, ‖a n*(F (x+r • n.1)-F x)‖≤C*N*r := by
    intro n
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    have hh := hLip (x+r • n.1)
    simp only [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one] at hh
    exact (mul_le_mul (hab n) hh (abs_nonneg _) hC).trans_eq (by ring)
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh

def transportSingularShell (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3) (r : ℝ) : ℝ :=
  r⁻¹ * ∫ v in closedBall (0:Vec) P, ∫ n : Sphere,
    divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v) ∂sphereMeasure

lemma transport_divergence_sphere_continuous (v e : Vec) (i : Fin 3) :
    Continuous (fun n : Sphere => divergence (transportSpatialFlux v e i) n.1) := by
  apply (continuousOn_transportSpatialDivergence e i).comp_continuous
    (continuous_subtype_val.prodMk continuous_const)
  intro n
  have hn := sphere_norm n
  intro hz
  change (n : Vec)=0 at hz
  rw [hz,norm_zero] at hn
  norm_num at hn

lemma transportSingularShell_near_far {P t U A N : ℝ} {f : Particle} {x e : Vec} {i : Fin 3}
    (_hA : 0≤A) (hN : 0≤N)
    (hf : ∀ s∈Icc (0:ℝ) U, ∀ v, Differentiable ℝ (fun y => f (s,y,v)))
    (hfA : ∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A)
    (hfN : ∀ s∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => f (s,z,v)) y‖≤N)
    {C : ℝ} (hC : 0≤C)
    (hc : ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      |divergence (transportSpatialFlux v e i) n.1|≤C)
    (ht : t∈Icc (0:ℝ) U) {r : ℝ} (hr : 0<r) (hrt : r≤t) :
    |transportSingularShell P f t x e i r|≤volume.real (closedBall (0:Vec) P)*(4*Real.pi)*C*N ∧
    |transportSingularShell P f t x e i r|≤
      (volume.real (closedBall (0:Vec) P)*(4*Real.pi)*C*A)/r := by
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith [ht.2]⟩
  have hnear (v : Vec) (hv : v∈closedBall (0:Vec) P) :
      ‖∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
        f (t-r,x+r • n.1,v) ∂sphereMeasure‖≤(4*Real.pi)*C*N*r := by
    apply sphere_mean_zero_lipschitz_bound (transport_divergence_sphere_continuous v e i)
      (hf _ hs v).continuous (transportSpatialFlux_angular_mean_zero v e i) hC (hc v hv) hr.le hN
    intro y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf _ hs v z)
      (fun z _ => hfN _ hs z v) convex_univ (mem_univ x) (mem_univ y)
  have hfar (v : Vec) (hv : v∈closedBall (0:Vec) P) :
      ‖∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
        f (t-r,x+r • n.1,v) ∂sphereMeasure‖≤(4*Real.pi)*C*A := by
    have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (f:=fun n : Sphere =>
      divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v)) (C:=C*A) (ae_of_all _ (fun n : Sphere => by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul (hc v hv n) (hfA _ hs _ v) (abs_nonneg _) hC))
    simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hnear' := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv; exact hnear v hv)
  have hfar' := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv; exact hfar v hv)
  simp only [Measure.restrict_apply_univ,measureReal_def,Real.norm_eq_abs] at hnear' hfar'
  unfold transportSingularShell
  rw [abs_mul,abs_of_pos (inv_pos.mpr hr)]
  constructor
  · exact (mul_le_mul_of_nonneg_left hnear' (inv_nonneg.mpr hr.le)).trans_eq (by simp only [measureReal_def]; field_simp)
  · exact (mul_le_mul_of_nonneg_left hfar' (inv_nonneg.mpr hr.le)).trans_eq (by simp only [measureReal_def]; ring)

attribute [local instance] Measure.Subtype.measureSpace

lemma transportSingularShell_continuousOn {P t U : ℝ} {f : Particle} (x e : Vec) (i : Fin 3)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) (ht : t∈Icc (0:ℝ) U) :
    ContinuousOn (transportSingularShell P f t x e i) (Ioc (0:ℝ) t) := by
  let K := closedBall (0:Vec) P
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  let α := K × Sphere
  let μ : Measure α := volume.prod sphereMeasure
  let G : ℝ × α → ℝ := fun q => divergence (transportSpatialFlux q.2.1.1 e i) q.2.2.1 *
    f (t-q.1,x+q.1 • q.2.2.1,q.2.1.1)
  have hc : Continuous (fun a : α => divergence (transportSpatialFlux a.1.1 e i) a.2.1) := by
    apply (continuousOn_transportSpatialDivergence e i).comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst))
    intro a hz
    change (a.2 : Vec)=0 at hz
    have hh := sphere_norm a.2
    rw [hz,norm_zero] at hh
    norm_num at hh
  have hn : Continuous (fun q : ℝ × α => (q.2.2:Vec)) := continuous_subtype_val.comp continuous_snd.snd
  have hv : Continuous (fun q : ℝ × α => (q.2.1:Vec)) := continuous_subtype_val.comp continuous_snd.fst
  have hmap : Continuous (fun q : ℝ × α => (t-q.1,x+q.1 • (q.2.2:Vec),(q.2.1:Vec))) :=
    (continuous_const.sub continuous_fst).prodMk ((continuous_const.add (continuous_fst.smul hn)).prodMk hv)
  have hG : ContinuousOn G (Ioc (0:ℝ) t ×ˢ univ) := by
    exact (hc.comp continuous_snd).continuousOn.mul (hf.comp hmap.continuousOn (by
      intro q hq
      exact ⟨by linarith [hq.1.2],by linarith [ht.2,hq.1.1]⟩))
  have hi (r : ℝ) (hr : r∈Ioc (0:ℝ) t) : Integrable (fun a : α => G (r,a)) μ :=
    (hG.comp_continuous (continuous_const.prodMk continuous_id) (fun a => ⟨hr,mem_univ a⟩)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : ContinuousOn (fun r => ∫ a, G (r,a) ∂μ) (Ioc (0:ℝ) t) := by
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hG
    intro r a _ ha
    exact (ha (mem_univ a)).elim
  have he (r : ℝ) (hr : r∈Ioc (0:ℝ) t) :
      (∫ a, G (r,a) ∂μ)=∫ v in K,∫ n : Sphere,
        divergence (transportSpatialFlux v e i) n.1*f (t-r,x+r • n.1,v) ∂sphereMeasure := by
    rw [show μ=(volume : Measure K).prod sphereMeasure from rfl,integral_prod _ (hi r hr)]
    exact integral_subtype measurableSet_closedBall
      (fun v : Vec => ∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
        f (t-r,x+r • n.1,v) ∂sphereMeasure)
  apply ContinuousOn.congr (f:=fun r : ℝ => r⁻¹*(∫ a, G (r,a) ∂μ))
  · exact (continuousOn_id.inv₀ (fun r hr => hr.1.ne')).mul hg
  · intro r hr
    change r⁻¹*(∫ v in K,∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
      f (t-r,x+r • n.1,v) ∂sphereMeasure) = r⁻¹*(∫ a, G (r,a) ∂μ)
    rw [he r hr]

lemma physical_transport_log_bound (P H A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (U t N : ℝ) (f : Particle),
      0<t → t≤U → U≤H → 0≤N →
      ContinuousOn f {p | p.1∈Icc (0:ℝ) U} →
      (∀ s∈Icc (0:ℝ) U, ∀ v, Differentiable ℝ (fun y => f (s,y,v))) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => f (s,z,v)) y‖≤N) →
      ∀ x, IntegrableOn (transportSingularShell P f t x e i) (Ioc (0:ℝ) t) ∧
        |∫ r in Ioc (0:ℝ) t,transportSingularShell P f t x e i r|≤
          1+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨K,hK,hkb⟩ := transportSpatialDivergence_uniform_bound P e i
  let C := volume.real (closedBall (0:Vec) P)*(4*Real.pi)*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,C*A,hC,mul_nonneg hC hA,?_⟩
  intro U t N f ht htU hUH hN hfc hfd hfA hfN x
  have htt : t∈Icc (0:ℝ) U := ⟨ht.le,htU⟩
  have hh := singular_radial_log_bound ht (htU.trans hUH) (mul_nonneg hC hA) (mul_nonneg hC hN)
    (transportSingularShell_continuousOn x e i hfc htt)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).1)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).2)
  exact hh

end

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
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (hfun.integrableOn_compact (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ico_subset_Icc_self)
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

section
local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

lemma transportSpatialFlux_uniform_bound (P : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      ‖transportSpatialFlux v e i n.1‖≤C := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => transportSpatialFlux p.2 e i p.1) K := by
    intro p hp
    have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
    have hz : p.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact (transportSpatialFlux_joint_contDiffAt e i hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro v hv n
  exact (hC (n.1,v) ⟨n.2,hv⟩).trans (le_max_left _ _)

lemma transport_sphere_rescale (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3)
    {r : ℝ} (hr : 0<r) (n : Sphere) :
    r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i (r • n.1)) =
    dot n.1 (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1) := by
  have he : (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i (r • n.1))=
      (r^2)⁻¹ • ∫ v in closedBall (0:Vec) P,
        f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1 := by
    rw [←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only
      rw [transportSpatialFlux_homogeneous v e i hr]
      simp only [smul_smul,mul_comm])
  rw [he,dot_smul_right,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'),one_mul]

lemma transport_sphere_boundary_bound (P A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : Particle) (t U r : ℝ) (x : Vec),
      0<r → r≤t → t≤U →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A) →
      |∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
        f (t-r,x+r • n.1,v) • transportSpatialFlux v e i (r • n.1)) ∂sphereMeasure|≤C := by
  obtain ⟨K,hK,hkb⟩ := transportSpatialFlux_uniform_bound P e i
  let C := volume.real (closedBall (0:Vec) P)*A*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨(4*Real.pi)*C,mul_nonneg (by positivity) hC,?_⟩
  intro f t U r x hr hrt htU hf
  simp_rw [transport_sphere_rescale P f t x e i hr]
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith⟩
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (n : Sphere) : ‖dot n.1 (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1)‖≤C := by
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1) (C:=A*K) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hf _ hs _ v) (hkb v hv n) (norm_nonneg _) hA)
    have hd := abs_real_inner_le_norm n.1
      (∫ v in closedBall (0:Vec) P,f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1)
    rw [sphere_norm,one_mul] at hd
    rw [dot_eq_inner,Real.norm_eq_abs]
    exact hd.trans (by simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,C,mul_assoc,mul_comm,mul_left_comm] using hh)
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_comm] using hh

end

def transportVelocityProfile (e : Vec) (i : Fin 3) (p : (Vec × Vec × Vec) × Vec) : Vec :=
  (transportAngularCore p.1.1 (velocity p.2) i *
    (dot p.1.1 e/(1-dot p.1.1 (velocity p.2)))) •
      (p.1.2.1+cross (velocity p.2) p.1.2.2)

lemma transportVelocityProfile_contDiffAt (e : Vec) (i : Fin 3)
    {p : (Vec × Vec × Vec) × Vec} (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (transportVelocityProfile e i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have ha := contDiffAt_transportAngularCore hn hu hd
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p ha
  have hm := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  exact (hi.mul (hm.div (contDiffAt_const.sub hdu) hd)).smul hforce

lemma divergence_parameter_slice {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {F : U × Vec → Vec} {a : U} {v : Vec} (hF : DifferentiableAt ℝ F (a,v)) :
    divergence (fun w => F (a,w)) v=∑ j : Fin 3,(fderiv ℝ F (a,v) (0,basis j)) j := by
  have hP := (hasFDerivAt_const a v).prodMk (hasFDerivAt_id (𝕜:=ℝ) v)
  have hh := hF.hasFDerivAt.comp v hP
  change HasFDerivAt (fun w : Vec => F (a,w)) _ v at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma continuousOn_transportVelocityDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => transportVelocityProfile e i (p.1,w)) p.2)
      {p | 1-dot p.1.1 (velocity p.2)≠0} := by
  apply ContinuousOn.congr (f:=fun p : (Vec × Vec × Vec) × Vec =>
    ∑ j : Fin 3,(fderiv ℝ (transportVelocityProfile e i) p (0,basis j)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((transportVelocityProfile_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact divergence_parameter_slice ((transportVelocityProfile_contDiffAt e i hp).differentiableAt (by simp))

lemma transportVelocityDivergence_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (E B v : Vec), ‖E‖≤M → ‖B‖≤M → ‖v‖≤P →
      |divergence (fun w => transportVelocityProfile e i ((n.1,E,B),w)) v|≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => transportVelocityProfile e i (p.1,w)) p.2) K :=
    (continuousOn_transportVelocityDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
      exact (cone_denom_pos p.2 p.1.1 hn).ne')
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n E B v hE hB hv
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

lemma divergence_real_const_smul {F : Vec → Vec} {v : Vec} (hF : DifferentiableAt ℝ F v) (a : ℝ) :
    divergence (fun w => a • F w) v=a*divergence F v := by
  rw [divergence_smul (differentiableAt_const a) hF]
  have hg : gradient (fun _ : Vec => a) v=0 := by
    ext j
    simp
  rw [hg]
  simp [dot]

lemma transport_velocity_divergence_rescale (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {z : Vec} (hz : z≠0) (v : Vec) :
    divergence (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v =
      ((coneRadius 0 z)^2)⁻¹*
        divergence (fun w => transportVelocityProfile e i
          ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),w)) v := by
  let a := (coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z))
  have ha : DifferentiableAt ℝ (fun w => transportVelocityProfile e i (a,w)) v :=
    ((transportVelocityProfile_contDiffAt e i (p:=(a,v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).comp v
      ((differentiableAt_const a).prodMk differentiableAt_id)
  have he : (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) =
      fun w => ((coneRadius 0 z)^2)⁻¹ • transportVelocityProfile e i (a,w) := by
    funext w
    simp only [transportConeCoefficient,coneSpatialCoefficient,coneLorentz,transportVelocityProfile,a,smul_smul,mul_assoc]
  rw [he,divergence_real_const_smul ha]

lemma physical_transport_velocity_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |divergence (fun w => transportConeCoefficient i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v|≤C/(coneRadius 0 z)^2 := by
  obtain ⟨C,hC,hb⟩ := transportVelocityDivergence_uniform_bound P M e i
  refine ⟨C,hC,?_⟩
  intro s t x z v hz hv hE hB
  rw [transport_velocity_divergence_rescale s t x e i hz v,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  exact (mul_le_mul_of_nonneg_left
    (hb ⟨coneDirection 0 z,hn⟩ _ _ v hE hB hv) (inv_nonneg.mpr (sq_nonneg _))).trans_eq (by ring)

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

lemma electric_transport_annulus_gradient_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
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
  rw [electric_transport_division_annulus hf hE hB hc heq htU hε hεR hRt x e i,
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

lemma electric_transport_gradient_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
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
  obtain ⟨B,C,D,hB,hC,hD,hbound⟩ := electric_transport_annulus_gradient_bound P A M H e i hA hH
  refine ⟨B,C,D,hB,hC,hD,?_⟩
  intro s U t N x ht htU hUH hN hf hE hB hc heq hfA hP hEB hfN
  apply norm_integral_ball_of_annulus_bound ht (transport_derivative_integrable x e i ht htU hf hN hP hfN)
  intro ε R hε hεR hRt
  exact hbound s U t N ε R x ht htU hUH hN hε hεR hRt hf hE hB hc heq hfA hP hEB hfN


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


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

lemma hasDerivAt_electric_transport_integral {s : Solution} {U t P A N : ℝ}
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

lemma electric_transport_deriv_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
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
  obtain ⟨B,C,D,hB,hC,hD,hb⟩ := electric_transport_gradient_bound P A M H e i hA hH
  refine ⟨B,C,D,hB,hC,hD,?_⟩
  intro s U t N x ht htU hUH hN hf hE hBB hc heq hfA hP hEB hfN
  rw [(hasDerivAt_electric_transport_integral x e i 0 ht htU hf hA hN hP hfA hfN).deriv]
  simpa only [zero_smul,add_zero] using hb s U t N x ht htU hUH hN hf hE hBB hc heq hfA hP hEB hfN

end RVM

end

end OAI
