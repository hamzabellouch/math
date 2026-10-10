import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.TransportDifferentiation

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

def transportAngularCore (n u : Vec) : Vec :=
  cross n (RVM.transportAngularCore n u)

def sourceAngularCore (n u b : Vec) : Vec :=
  cross n (RVM.sourceAngularCore n u b)

lemma physicalMagneticKernel_eulerian_split {r : ℝ} {n u : Vec} (b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    (1-dot n u) • cross n (physicalElectricKernel r n u b) =
      (r^2)⁻¹ • transportAngularCore n u+r⁻¹ • sourceAngularCore n u b := by
  have hh := congrArg (cross n) (RVM.physicalElectricKernel_eulerian_split b hr hd)
  simpa only [cross_smul_right,cross_add_right,transportAngularCore,sourceAngularCore] using hh

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
  exact contDiff_cross.contDiffAt.comp z (hn.prodMk (RVM.contDiffAt_transportAngularCore hn hu hd))

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

lemma transportSpatialFlux_joint_contDiffAt (e : Vec) (i : Fin 3) {p : Phase}
    (hp : p.1 ≠ 0) :
    ContDiffAt ℝ 1 (fun z : Phase => transportSpatialFlux z.2 e i z.1) p := by
  have hz : (0:Vec) ≠ p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have he := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hd := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hne := (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hc := he.div (contDiffAt_const.sub hd) hne
  have hW : ContDiffAt ℝ 1 (fun z : Phase => coneSpatialLift 0 z.1 z.2 e) p :=
    contDiffAt_const.add (hc.smul hu)
  have hA := contDiffAt_transportAngularCore hn hu hne
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact (((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi).smul hW

lemma divergence_phase_first {F : Phase → Vec} {p : Phase}
    (hF : DifferentiableAt ℝ F p) :
    divergence (fun z => F (z,p.2)) p.1 =
      ∑ j : Fin 3, (fderiv ℝ F p (basis j,0)) j := by
  have hP := (hasFDerivAt_id (𝕜:=ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hh := hF.hasFDerivAt.comp p.1 hP
  change HasFDerivAt (fun z : Vec => F (z,p.2)) _ p.1 at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma continuousOn_transportSpatialDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : Phase => divergence (transportSpatialFlux p.2 e i) p.1)
      {p | p.1≠0} := by
  have he (p : Phase) (hp : p.1≠0) :=
    divergence_phase_first ((transportSpatialFlux_joint_contDiffAt e i hp).differentiableAt (by simp))
  apply ContinuousOn.congr (f:=fun p : Phase => ∑ j : Fin 3,
    (fderiv ℝ (fun z : Phase => transportSpatialFlux z.2 e i z.1) p (basis j,0)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((transportSpatialFlux_joint_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact he p hp

lemma transportSpatialDivergence_uniform_bound (P : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      |divergence (transportSpatialFlux v e i) n.1|≤C := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => divergence (transportSpatialFlux p.2 e i) p.1) K :=
    (continuousOn_transportSpatialDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
      intro hz
      simp only [hz,norm_zero] at hn
      norm_num at hn)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro v hv n
  exact (hC (n.1,v) ⟨n.2,hv⟩).trans (le_max_left _ _)

def transportConeCoefficient (i : Fin 3) (p : Phase) : ℝ :=
  ((coneRadius 0 p.1)^2)⁻¹*transportAngularCore (coneDirection 0 p.1) (velocity p.2) i

def coneLorentz (s : Solution) (t : ℝ) (x : Vec) (p : Phase) : Vec :=
  s.E (t-coneRadius 0 p.1,x+p.1)+cross (velocity p.2) (s.B (t-coneRadius 0 p.1,x+p.1))

lemma transportConeCoefficient_contDiffAt (i : Fin 3) {p : Phase} (hp : p.1≠0) :
    ContDiffAt ℝ 1 (transportConeCoefficient i) p := by
  have hz : (0:Vec)≠p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hA := contDiffAt_transportAngularCore hn hu (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact ((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi

lemma coneLorentz_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (coneLorentz s t x) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  exact he.add (contDiff_cross.contDiffAt.comp p (hu.prodMk hb))

lemma coneLorentz_vlasov_before {s : Solution} {H t : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s H)
    (htH : t≤H) (x : Vec) {z : Vec} (hz : z∈retardedSpaceDomain t 0) (v : Vec) :
    fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (1,velocity v,coneLorentz s t x (z,v))=0 := by
  have hr : 0<coneRadius 0 z := norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)
  have hh := particle_spacetime_vlasov_before hf heq hz.2 (by linarith : t-coneRadius 0 z<H) (x+z) v
  rw [fderiv_particleBySpacetime (particle_differentiableAt_positive hf hz.2 (x+z) v)] at hh
  exact hh

lemma magnetic_transport_division_annulus {s : Solution} {H t ε R : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (heq : EquationsBefore s H)
    (htH : t≤H) (hε : 0<ε) (hεR : ε≤R) (hRt : R<t) (x e : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
      transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, s.f (t-R,x+R • n.1,v) •
        transportSpatialFlux v e i (R • n.1)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, s.f (t-ε,x+ε • n.1,v) •
        transportSpatialFlux v e i (ε • n.1)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (transportSpatialFlux v e i) z+
          divergence (fun w => transportConeCoefficient i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v) := by
  have hk : ContDiffOn ℝ 1 (transportConeCoefficient i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (transportConeCoefficient_contDiffAt i hp.1.1.symm).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  have hh := retarded_spatial_annulus (e:=e) hf hc hε hεR hRt hk hK
    (fun z hz v => coneLorentz_vlasov_before hf heq htH x hz v)
  unfold transportSpatialFlux transportConeCoefficient at *
  simpa only [smul_smul,smul_eq_mul,mul_assoc] using hh

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

end RVM.Magnetic

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM.Magnetic

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

end RVM.Magnetic

end

end OAI
