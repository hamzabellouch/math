import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.PositiveExtension
import OAI.Analysis.VlasovMaxwell.Retarded.SourceWaveSpatialIbp

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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma RegularParticle.time_moment_derivative {f : Particle} (hf : RegularParticle f)
    {w : Vec → ℝ} (hw : ContDiff ℝ 1 w) {t : ℝ} (ht : 0<t) (x : Vec) :
    dirD (fun p : ℝ × Vec => ∫ v : Vec, w v*f (p.1,p.2,v)) (1,0) (t,x) =
      ∫ v : Vec, w v*fderiv ℝ f (t,x,v) (1,0,0) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ := hf.local_data ht x
  change fderiv ℝ (fun p => ∫ v : Vec, w v*particleBySpacetime f (p,v)) (t,x) (1,0)=_
  rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF hw hzero]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [fderiv_particleBySpacetime (particle_differentiableAt_positive (s:=⟨f,0,0⟩) hf.1 ht x v)]

lemma RegularParticle.time_moment_integrable {f : Particle} (hf : RegularParticle f)
    {w : Vec → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0<t) (x : Vec) :
    Integrable (fun v : Vec => w v*fderiv ℝ f (t,x,v) (1,0,0)) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ := hf.local_data ht x
  have hi := integrable_param_fderiv_apply_weight hU hK hp hF hw hzero (((1:ℝ),(0:Vec)),(0:Vec))
  simpa only [fderiv_particleBySpacetime (particle_differentiableAt_positive (s:=⟨f,0,0⟩) hf.1 ht x _)] using hi

lemma RegularParticle.scalar_moment_integrable {f : Particle} (hf : RegularParticle f)
    {w : Vec → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0≤t) (x : Vec) :
    Integrable (fun v : Vec => w v*f (t,x,v)) := by
  simpa only [smul_eq_mul,mul_comm] using hf.moment_integrable hw ht x

lemma current_eq_integral_component {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0≤t) (x : Vec) (i : Fin 3) :
    current (fun z => f (t,z)) x i = ∫ v : Vec, velocity v i*f (t,x,v) := by
  have hi := hf.moment_integrable (contDiff_velocity (k:=1)).continuous ht x
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simpa only [current,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,mul_comm] using he.symm

lemma dirD_rho {f : Particle} (hf : RegularParticle f) {t : ℝ} (ht : 0<t) (x : Vec) :
    dirD (fun p : ℝ × Vec => rho (fun z => f (p.1,z)) p.2) (1,0) (t,x) =
      ∫ v : Vec, fderiv ℝ f (t,x,v) (1,0,0) := by
  simpa only [one_mul,rho] using hf.time_moment_derivative (contDiff_const (c:=(1:ℝ))) ht x

lemma dirD_current_component {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    dirD (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2 i) (1,0) (t,x) =
      ∫ v : Vec, velocity v i*fderiv ℝ f (t,x,v) (1,0,0) := by
  have he : (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2 i) =ᶠ[𝓝 (t,x)]
      (fun p : ℝ × Vec => ∫ v : Vec, velocity v i*f (p.1,p.2,v)) := by
    filter_upwards [((isOpen_lt continuous_const (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)] with p hp
    exact current_eq_integral_component hf hp.le p.2 i
  unfold dirD
  rw [he.fderiv_eq]
  exact hf.time_moment_derivative ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity) ht x

lemma classical_retarded_electric_moment_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : Equations s) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (i : Fin 3) :
    ((coneRadius x y)^2)⁻¹*coneDirection x y i*rho (fun z => s.f (t-coneRadius x y,z)) y +
      (coneDirection x y i/coneRadius x y)*
        dirD (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2) (1,0) (t-coneRadius x y,y) -
      (coneRadius x y)⁻¹*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 i) (1,0) (t-coneRadius x y,y) =
    (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
      physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))) i) -
    divergence (fun z => ∫ v : Vec,
      (retardedDensity s.f t x (z,v)*retardedG x (z,v) i) • velocity v) y := by
  have hr : RegularParticle s.f := ⟨hf,hc⟩
  have hvel : ContDiff ℝ 1 (fun v => velocity v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity
  have hfI : Integrable (fun v : Vec => s.f (t-coneRadius x y,y,v)) := by
    simpa only [one_mul] using hr.scalar_moment_integrable (continuous_const (y:=(1:ℝ))) ht.le y
  have htI : Integrable (fun v : Vec => fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) := by
    simpa only [one_mul] using hr.time_moment_integrable (continuous_const (y:=(1:ℝ))) ht y
  have hjI := hr.time_moment_integrable hvel.continuous ht y
  have hsum : Integrable (fun v : Vec =>
      ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i/coneRadius x y)*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) :=
    (hfI.const_mul _).add (htI.const_mul _)
  rw [dirD_rho hr ht y,dirD_current_component hr ht y i,rho]
  rw [← integral_const_mul,← integral_const_mul,← integral_const_mul,
    ← integral_add (hfI.const_mul _) (htI.const_mul _),
    ← integral_sub hsum (hjI.const_mul _)]
  convert classical_retarded_electric_integral_identity hf hc heq hxy ht i using 1
  congr 1
  funext v
  dsimp only
  ring

def shiftedRho (s : Solution) (a : ℝ) : ℝ × Vec → ℝ :=
  positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2)
def shiftedCurrent (s : Solution) (a : ℝ) : Field :=
  positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)
def electricMomentDensity (ρ : ℝ × Vec → ℝ) (j : Field)
    (t : ℝ) (x : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  -(z i/‖z‖^3*ρ (t-‖z‖,x+z)) - z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) -
    dirD (fun p => j p i) (1,0) (t-‖z‖,x+z)/‖z‖

lemma integrableOn_electricMomentDensity {ρ : ℝ × Vec → ℝ} {j : Field}
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) {t : ℝ} (ht : 0≤t) (x : Vec) (i : Fin 3) :
    IntegrableOn (electricMomentDensity ρ j t x i) (ball (0:Vec) t) := by
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  exact ((integrableOn_ball_direction_div_norm_pow (hρ.continuous.comp harg) 2 (by norm_num) t i).neg.sub
    (integrableOn_ball_direction_div_norm_pow ((contDiff_dirD hρ _).continuous.comp harg) 1 (by norm_num) t i)).sub
    (integrable_conePotential (contDiff_dirD (contDiff_component hj i) (1,0)).continuous ht x)

lemma contDiff_shifted_moments {d : Datum} {s : Solution} (hs : Classical d s)
    (hm : SmoothOnFiniteHorizons s) {a : ℝ} (ha : 0<a) :
    ContDiff ℝ ∞ (shiftedRho s a) ∧ ContDiff ℝ ∞ (shiftedCurrent s a) :=
  ⟨contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).1),
   contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)⟩

lemma retardedElectricDensity_component {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    retardedElectricDensity s t x y i =
    ∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
      physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))) i := by
  have hr : RegularParticle s.f := ⟨hf,hc⟩
  obtain ⟨hreg,hcomp⟩ := hr.slice ht y
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hi : Integrable (fun v : Vec => (s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))) •
      physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) :=
    ((hreg.continuous.mul hd).smul hk).integrable_of_hasCompactSupport (hcomp.mul_right.smul_right)
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simpa only [retardedElectricDensity,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul] using he.symm

lemma coneDirection_add (x z : Vec) : coneDirection x (x+z)=-(‖z‖⁻¹ • z) := by
  unfold coneDirection
  rw [coneRadius_add,show x-(x+z) = -z by abel,smul_neg]

lemma electricMomentDensity_actual {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ} (ha : 0<a)
    (x : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (hzt : ‖z‖<T) :
    electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z =
      retardedElectricDensity s (a+T) x (x+z) i -
      divergence (retardedElectricFlux s (a+T) x i) (x+z) := by
  have hc := hs.2.2.2.2.2.2.1
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<a+T-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hp : 0<a+(T-‖z‖) := by linarith
  have hρ := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).1
  have hj := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).2
  have hji : DifferentiableAt ℝ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 i)
      (a+(T-‖z‖),x+z) :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp _ hj).differentiableAt (by simp)
  have herr : (fun p => shiftedCurrent s a p i)=
      positiveTimeShift a (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 i) := by
    funext p
    simp only [shiftedCurrent,positiveTimeShift,positiveTimeExtend,PiLp.smul_apply,smul_eq_mul]
  unfold electricMomentDensity
  rw [herr]
  have hρeq : shiftedRho s a (T-‖z‖,x+z)=rho (fun q => s.f (a+(T-‖z‖),q)) (x+z) :=
    positiveTimeShift_eq ha (sub_nonneg.mpr hzt.le) _ _
  rw [hρeq]
  unfold dirD shiftedRho
  rw [fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ (hρ.differentiableAt (by simp)),
    fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ hji]
  have he := classical_retarded_electric_moment_identity hs.1 hc hs.2.2.2.2.2.2.2.1 hxy ht i
  rw [← retardedElectricDensity_component hs.1 hc hxy ht.le i] at he
  change _ = _ - divergence (retardedElectricFlux s (a+T) x i) (x+z) at he
  rw [← he]
  simp only [coneRadius_add,coneDirection_add,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
    dirD,show a+T-‖z‖=a+(T-‖z‖) by ring]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma integrated_electricMomentDensity_actual {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) T, electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) =
      (∫ z in ball (0:Vec) T, retardedElectricDensity s (a+T) x (x+z) i) -
      ∫ n : Sphere, T^2*dot n.1 (retardedElectricFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure := by
  have hc := hs.2.2.2.2.2.2.1
  have hρj := contDiff_shifted_moments hs hm ha
  have hM := integrableOn_electricMomentDensity hρj.1 hρj.2 hT.le x i
  have hD := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
    (integrableOn_retardedElectricDensity hs.1 hs.2.1 hs.2.2.1 hc hT.le
      (show T<a+T by linarith) x)
  change IntegrableOn (fun z : Vec => retardedElectricDensity s (a+T) x (x+z) i) (ball (0:Vec) T) at hD
  let F : Vec → Vec := fun z => retardedElectricFlux s (a+T) x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) T)]
      (fun z => retardedElectricDensity s (a+T) x (x+z) i -
        electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := electricMomentDensity_actual hs hm ha x i hz0 (by simpa only [mem_ball_zero_iff] using hz)
    dsimp only [F]
    rw [divergence_add_right]
    linarith
  have hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<a+T → ContDiffAt ℝ 1 F z := by
    intro z hz hzT
    have hxy : x≠x+z := by
      intro h
      apply (norm_pos_iff.mp hz)
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    have hp : x+z ∈ retardedSpaceDomain (a+T) x := ⟨hxy,by rw [coneRadius_add]; linarith⟩
    exact ((contDiffOn_retarded_flux hs.1 hc (by linarith) x i).contDiffAt
      ((isOpen_retardedSpaceDomain (a+T) x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) T) :=
    (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular hT (show T<a+T by linarith) hF hi
    (retarded_flux_tip hs.1 hc (show 0<a+T by linarith) x i)
  have hh : (∫ z in ball (0:Vec) T, divergence F z) =
      (∫ z in ball (0:Vec) T, retardedElectricDensity s (a+T) x (x+z) i) -
      (∫ z in ball (0:Vec) T, electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, T^2*dot n.1 (retardedElectricFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure at hg
  linarith

lemma classical_shifted_electric_physical_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (x : Vec) (i : Fin 3) :
    s.E (a+T,x) i =
      freeWave (fun y => s.E (a,y) i) (fun y => curl (fun z => s.B (a,z)) y i) (T,x) +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedElectricDensity s (a+T) x (x+z) i) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
        (retardedElectricFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T*n.1 i*rho (fun z => s.f (a,z)) (x+T • n.1) ∂sphereMeasure) -
      waveK (fun y => current (fun z => s.f (a,z)) y i) (T,x) := by
  have hρj := contDiff_shifted_moments hs hm ha
  rw [classical_shifted_electric_potential_representation hs hm ha hT.le x i]
  change _ + electricPotentialComponent (shiftedRho s a) (shiftedCurrent s a) i (T,x)=_
  rw [electricPotentialComponent_ball hρj.1 hρj.2 hT]
  change _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T,
      electricMomentDensity (shiftedRho s a) (shiftedCurrent s a) T x i z) - _ - _)=_
  rw [integrated_electricMomentDensity_actual hs hm ha hT x i]
  have hρ0 : (fun n : Sphere => T*n.1 i*shiftedRho s a (0,x+T • n.1)) =
      (fun n : Sphere => T*n.1 i*rho (fun z => s.f (a,z)) (x+T • n.1)) := by
    funext n
    simp only [shiftedRho,positiveTimeShift_eq ha (le_refl 0),add_zero]
  have hj0 : (fun y => shiftedCurrent s a (0,y) i)=(fun y => current (fun z => s.f (a,z)) y i) := by
    funext y
    simp only [shiftedCurrent,positiveTimeShift_eq ha (le_refl 0),add_zero]
  rw [hρ0,hj0]
  ring
end RVM

end

end OAI
