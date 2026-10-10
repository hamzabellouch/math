import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.ReceiverQCLM
import OAI.Analysis.VlasovMaxwell.Population.DatumElectricFluxKernel

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PhaseFlowOn.branch_integral {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {H : Set ℝ} (hH : MeasurableSet H)
    (hsub : H ⊆ branchDomain F.flow zX zY T)
    (hne : ∀ s∈H, (F.flow zX s).1 ≠ (F.flow zY s).1)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (g : ℝ → W) :
    ∫ t in branchTime F.flow zX zY T '' H, g t =
      ∫ s in H, branchRate F.flow zX zY T s • g (branchTime F.flow zX zY T s) := by
  rw [integral_image_eq_integral_abs_deriv_smul hH
    (fun s hs => (F.branch_differential zX zY (hsub hs) (hne s hs)).2.hasDerivWithinAt)
    ((F.branch_strictMono zX zY).injOn.mono hsub) g]
  apply setIntegral_congr_fun hH
  intro s hs
  change |branchRate F.flow zX zY T s| • _ = branchRate F.flow zX zY T s • _
  rw [abs_of_pos (F.branchRate_pos zX zY (hsub hs) (hne s hs))]

lemma PhaseFlowOn.branch_integrable_iff {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) {H : Set ℝ} (hH : MeasurableSet H)
    (hsub : H ⊆ branchDomain F.flow zX zY T)
    (hne : ∀ s∈H, (F.flow zX s).1 ≠ (F.flow zY s).1)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (g : ℝ → W) :
    IntegrableOn g (branchTime F.flow zX zY T '' H) ↔
      IntegrableOn (fun s => branchRate F.flow zX zY T s • g (branchTime F.flow zX zY T s)) H := by
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hH
    (fun s hs => (F.branch_differential zX zY (hsub hs) (hne s hs)).2.hasDerivWithinAt)
    ((F.branch_strictMono zX zY).injOn.mono hsub) g]
  apply integrableOn_congr_fun
  · intro s hs
    change |branchRate F.flow zX zY T s| • _ = branchRate F.flow zX zY T s • _
    rw [abs_of_pos (F.branchRate_pos zX zY (hsub hs) (hne s hs))]
  · exact hH

lemma PhaseFlowOn.branch_retardedSource {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1≠(F.flow zY s).1) :
    let t := branchTime F.flow zX zY T s
    let ht : t∈Icc 0 T := ⟨hs.1.1.le.trans (F.branch_spec zX zY hs).1.1,
        (F.branch_spec zX zY hs).1.2⟩
    F.retardedSource ht (F.flow zX t).1 zY=F.flow zY s := by
  dsimp only
  let t := branchTime F.flow zX zY T s
  have hts := F.branch_time_mem zX zY hs hne
  have hspec := (F.branch_spec zX zY hs).2
  have hdom : F.flow zY s∈retardedPhaseDomain t (F.flow zX t).1 := by
    change 0<‖(F.flow zX t).1-(F.flow zY s).1‖ ∧ ‖(F.flow zX t).1-(F.flow zY s).1‖<t
    constructor <;> linarith [hs.1.1]
  have htime : t-‖(F.flow zX t).1-(F.flow zY s).1‖=s := by linarith
  have hlabel : retardedLabel F.flow t (F.flow zX t).1 (F.flow zY s)=zY := by
    change inversePhase F.flow (t-‖(F.flow zX t).1-(F.flow zY s).1‖,F.flow zY s)=zY
    rw [htime]
    exact F.inversePhase_flow (Ioo_subset_Icc_self hs.1) zY
  simpa only [hlabel] using F.retardedSource_label
    (show t∈Icc 0 T from ⟨hs.1.1.le.trans (F.branch_spec zX zY hs).1.1,
      (F.branch_spec zX zY hs).1.2⟩) (F.flow zX t).1 hdom

lemma PhaseFlowOn.actual_branch_force {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX zY : Phase)
    (hσ : σ∈branchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    let t := branchTime F.flow zX zY T σ
    let r := t-σ
    let n := branchDirection F.flow zX zY T σ
    let a := velocity (F.flow zX t).2
    let v := (F.flow zY σ).2
    let b := fderiv ℝ velocity v
      (s.E (σ,(F.flow zY σ).1)+cross (velocity v) (s.B (σ,(F.flow zY σ).1)))
    branchRate F.flow zX zY T σ • ((1-dot n (velocity v))⁻¹ •
      physicalPhaseForce s t (F.flow zX t).1 a (F.flow zY σ)) =
      signedForceKernel r a (velocity v) n b := by

  let t := branchTime F.flow zX zY T σ
  let r := t-σ
  let n := branchDirection F.flow zX zY T σ
  let a := velocity (F.flow zX t).2
  let v := (F.flow zY σ).2
  let b := fderiv ℝ velocity v
    (s.E (σ,(F.flow zY σ).1)+cross (velocity v) (s.B (σ,(F.flow zY σ).1)))
  change branchRate F.flow zX zY T σ • ((1-dot n (velocity v))⁻¹ •
    physicalPhaseForce s t (F.flow zX t).1 a (F.flow zY σ)) =
      signedForceKernel r a (velocity v) n b
  have ht := F.branch_time_mem zX zY hσ hne
  have hr : coneRadius (F.flow zX t).1 (F.flow zY σ).1=r :=
    (F.branch_spec zX zY hσ).2.symm
  have hn : coneDirection (F.flow zX t).1 (F.flow zY σ).1=n := by
    dsimp only [coneDirection]
    rw [hr]
    rfl
  have htime : t-r=σ := by dsimp [r]; ring
  have hh : physicalPhaseForce s t (F.flow zX t).1 a (F.flow zY σ)=
      forceTransportKernel r n a v+forceSourceKernel r n a v b := by
    unfold physicalPhaseForce
    rw [hr,hn,htime]
  rw [hh]
  exact physical_force_branch_kernel r n a v b (sub_ne_zero.mpr ht.1.ne')
    (F.branchDirection_norm zX zY hσ hne)
    (cone_denom_pos (F.flow zX t).2 n (F.branchDirection_norm zX zY hσ hne)).ne'

end RVM
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_moment_bounds {d : Datum} (hf : Continuous d.f₀) (hc : HasCompactSupport d.f₀) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |rho d.f₀ x|≤C ∧ ‖current d.f₀ x‖≤C := by
  have hn : ‖basis 0‖=1 := by simp [basis,PiLp.norm_single]
  obtain ⟨C,hC,hb⟩ := uniform_datum_velocity_integral_bound (H:=fun _ : Vec × Vec => (1:ℝ))
    hf hc continuousOn_const
  obtain ⟨D,hD,hd⟩ := uniform_datum_velocity_integral_bound (H:=fun p : Vec × Vec => velocity p.2)
    hf hc ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro x
  constructor
  · have hh := hb x (basis 0) hn
    simpa only [smul_eq_mul,mul_one,Real.norm_eq_abs,rho] using hh.trans (le_add_of_nonneg_right hD)
  · exact (hd x (basis 0) hn).trans (le_add_of_nonneg_left hC)

lemma norm_coordinate_le (v : Vec) (i : Fin 3) : |v i|≤‖v‖ := by
  exact (PiLp.norm_apply_le v i)

lemma norm_le_three_of_coordinate_bound {v : Vec} {C : ℝ} (hC : 0≤C)
    (h : ∀ i : Fin 3, |v i|≤C) : ‖v‖≤3*C := by
  have hsq (i : Fin 3) : (v i)^2≤C^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using h i)
  have hnorm := dot_self v
  simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hnorm
  change v 0*v 0+(v 1*v 1+v 2*v 2)=‖v‖^2 at hnorm
  nlinarith [hsq 0,hsq 1,hsq 2,norm_nonneg v]

lemma freeWave_bound_compact {g h : Vec → ℝ}
    (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R,
      |freeWave g h (t,x)|≤C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod (isCompact_closedBall (0:Vec) R)).image
    (contDiff_freeWave hg hh).continuous).isBounded.exists_norm_le
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht x hx
  exact (hC _ ⟨(t,x),⟨ht,hx⟩,rfl⟩).trans (le_max_left _ _)

lemma norm_initial_cone_flux {d : Datum} {C : ℝ} (i : Fin 3)
    (hb : ∀ t x y, x≠y → ‖retardedElectricFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    |t^2*dot n.1 (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))|≤C*t := by
  have hr : coneRadius x (x+t • n.1)=t := by
    simpa only [sub_zero] using coneBoundary_radius ht
      (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
  have hxy : x≠x+t • n.1 := by
    intro he
    have hh : coneRadius x (x+t • n.1)=0 := by rw [← he,coneRadius,sub_self,norm_zero]
    linarith
  have hnorm : ‖n.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.2
  have hf := hb t x (x+t • n.1) hxy
  rw [hr] at hf
  rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
  have ha : |dot (n.1 : Vec) (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))| ≤
      ‖n.1‖*‖retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)‖ := by
    simpa only [dot_eq_inner] using
      abs_real_inner_le_norm (n.1 : Vec) (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))
  calc
    _ ≤ t^2*(‖n.1‖*‖retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)‖) :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    _ ≤ t^2*(C/t) := by rw [hnorm,one_mul]; gcongr
    _ = C*t := by field_simp

lemma norm_initial_magnetic_cone_flux {d : Datum} {C : ℝ} (i : Fin 3)
    (hb : ∀ t x y, x≠y → ‖retardedMagneticFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    |t^2*dot n.1 (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))|≤C*t := by
  have hr : coneRadius x (x+t • n.1)=t := by
    simpa only [sub_zero] using coneBoundary_radius ht
      (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
  have hxy : x≠x+t • n.1 := by
    intro he
    have hh : coneRadius x (x+t • n.1)=0 := by rw [← he,coneRadius,sub_self,norm_zero]
    linarith
  have hnorm : ‖n.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.2
  have hf := hb t x (x+t • n.1) hxy
  rw [hr] at hf
  rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
  have ha : |dot (n.1 : Vec) (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))| ≤
      ‖n.1‖*‖retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)‖ := by
    simpa only [dot_eq_inner] using
      abs_real_inner_le_norm (n.1 : Vec) (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))
  calc
    _ ≤ t^2*(‖n.1‖*‖retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)‖) :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    _ ≤ t^2*(C/t) := by rw [hnorm,one_mul]; gcongr
    _ = C*t := by field_simp

lemma norm_sphere_integral_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Sphere → W} {C : ℝ} (hb : ∀ n, ‖g n‖≤C) :
    ‖∫ n, g n ∂sphereMeasure‖≤C*(4*Real.pi) := by
  simpa only [sphere_area] using norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)

lemma abs_sphere_integral_le {g : Sphere → ℝ} {C : ℝ} (hb : ∀ n, |g n|≤C) :
    |∫ n, g n ∂sphereMeasure|≤C*(4*Real.pi) := by
  simpa only [Real.norm_eq_abs] using norm_sphere_integral_le (g:=g) (C:=C) hb

lemma waveK_bound_of_bounded {g : Vec → ℝ} {C : ℝ} (hb : ∀ x, |g x|≤C)
    {t : ℝ} (ht : 0≤t) (x : Vec) : |waveK g (t,x)|≤t*C := by
  have hh := norm_sphere_integral_le (g:=fun n : Sphere => g (x+t • n.1))
    (fun n => hb (x+t • n.1))
  simp only [Real.norm_eq_abs] at hh
  dsimp only [waveK,sphereSum]
  rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹),abs_of_nonneg ht]
  calc
    _ ≤ (4*Real.pi)⁻¹*(t*(C*(4*Real.pi))) := by gcongr
    _ = t*C := by field_simp

lemma electricConeBoundary_datum_bound {d : Datum} (hd : Admissible d)
    (T R : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R,
      |electricConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumElectricFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := freeWave_bound_compact (hproj.comp hd.2.2.2.1.1)
    (hproj.comp (contDiff_curl hd.2.2.2.2.1.1)) T R
  refine ⟨A+(C+2*D)*max T 0,by positivity,?_⟩
  intro t ht x hx
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_cone_flux i hflux ht.1 x n)
  have hrho : |∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure|≤
      (t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    have hn : |n.1 i|≤1 := by
      exact (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        (hmom (x+t • n.1)).1 (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = t*D := by ring
  have hj : |waveK (fun y => current d.f₀ y i) (t,x)|≤t*D :=
    waveK_bound_of_bounded (fun y => (norm_coordinate_le (current d.f₀ y) i).trans (hmom y).2) ht.1.le x
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure)|≤t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hrho hp
      _ = t*D := by field_simp
  have hf := hfree t ⟨ht.1.le,ht.2⟩ x hx
  simp only [electricConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)) hj)).trans (by
      have htT := ht.2.trans (le_max_left T 0)
      nlinarith)

lemma magneticConeBoundary_datum_bound {d : Datum} (hd : Admissible d)
    (T R : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R,
      |magneticConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumMagneticFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := freeWave_bound_compact (hproj.comp hd.2.2.2.2.1.1)
    (hproj.comp (contDiff_curl hd.2.2.2.1.1)).neg T R
  refine ⟨A+(C+2*D)*max T 0,by positivity,?_⟩
  intro t ht x hx
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_magnetic_cone_flux i hflux ht.1 x n)
  have hem (n : Sphere) (j k : Fin 3) :
      |t*n.1 j*current d.f₀ (x+t • n.1) k|≤t*D := by
    have hn : |n.1 j|≤1 :=
      (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    have hj : |current d.f₀ (x+t • n.1) k|≤D :=
      (norm_coordinate_le _ k).trans (hmom _).2
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        hj (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = _ := by ring
  have hj : |∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure|≤
      (2*t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    exact (abs_sub _ _).trans ((add_le_add (hem n _ _) (hem n _ _)).trans (by ring_nf; rfl))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure)|≤2*t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((2*t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hj hp
      _ = 2*t*D := by field_simp
  have hf := hfree t ⟨ht.1.le,ht.2⟩ x hx
  simp only [magneticConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)).trans (by
      have htT := ht.2.trans (le_max_left T 0)
      nlinarith)

lemma boundaryLorentzForce_datum_bound {d : Datum} (hd : Admissible d) (T R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T, ∀ x∈closedBall (0:Vec) R, ∀ a : Vec,
      ‖a‖≤1 → ‖boundaryLorentzForce (datumBoundarySolution d) t x a‖≤C := by
  classical
  choose C hC hb using electricConeBoundary_datum_bound hd T R
  choose D hD hd' using magneticConeBoundary_datum_bound hd T R
  let A := ∑ i : Fin 3, C i
  let B := ∑ i : Fin 3, D i
  have hA : 0≤A := Finset.sum_nonneg (fun i _ => hC i)
  have hB : 0≤B := Finset.sum_nonneg (fun i _ => hD i)
  refine ⟨3*A+3*B,by positivity,?_⟩
  intro t ht x hx a ha
  have he : ‖electricBoundaryField (datumBoundarySolution d) t x‖≤3*A := by
    apply norm_le_three_of_coordinate_bound hA
    intro i
    exact (hb i t ht x hx).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
  have hm : ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤3*B := by
    apply norm_le_three_of_coordinate_bound hB
    intro i
    exact (hd' i t ht x hx).trans (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i))
  exact (norm_add_le _ _).trans (add_le_add he ((norm_cross_le _ _).trans
    ((mul_le_mul ha hm (norm_nonneg _) zero_le_one).trans_eq (one_mul _))))

end RVM

end

end OAI
