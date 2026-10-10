import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RetardedWeightedIntegralBound
import OAI.Analysis.VlasovMaxwell.Regularity.ContinuousIntegralSphere
import OAI.Analysis.VlasovMaxwell.LocalPDE.VlasovConstruction

namespace OAI

noncomputable section

section
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

lemma tendsto_right_of_continuousOn_Icc {W : Type*} [TopologicalSpace W]
    {F : ℝ → W} {R : ℝ} (hR : 0<R) (hF : ContinuousOn F (Icc 0 R)) :
    Tendsto F (𝓝[>] (0:ℝ)) (𝓝 (F 0)) := by
  apply (hF 0 ⟨le_rfl,hR.le⟩).mono_left
  apply le_inf nhdsWithin_le_nhds
  apply Filter.le_principal_iff.mpr
  filter_upwards [Ioo_mem_nhdsGT hR] with a ha
  exact ⟨ha.1.le,ha.2.le⟩

lemma RegularParticle.rho_continuous_slab {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0≤T) : ContinuousOn (fun p : ℝ × Vec => rho (fun z => f (p.1,z)) p.2)
      (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have h := hf.moment_continuous_slab (w:=fun _ => (1:ℝ)) continuous_const hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v, f (p.1,p.2,v) • (1:ℝ)) _ at h
  simpa only [rho,smul_eq_mul,mul_one] using h

lemma RegularParticle.current_continuous_slab {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0≤T) : ContinuousOn (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2)
      (Icc 0 T ×ˢ (univ : Set Vec)) :=
  hf.moment_continuous_slab (contDiff_velocity (k:=1)).continuous hT

lemma continuousOn_cone_boundary_comp {W : Type*} [TopologicalSpace W] {H : ℝ × Vec → W}
    {T : ℝ} (hT : 0<T) (hH : ContinuousOn H (Icc 0 T ×ˢ (univ : Set Vec))) (x : Vec) :
    ContinuousOn (fun p : ℝ × Vec => H (p.1,x+(T-p.1) • p.2))
      (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  apply hH.comp (continuous_fst.prodMk
    (continuous_const.add ((continuous_const.sub continuous_fst).smul continuous_snd))).continuousOn
  intro p hp
  exact ⟨⟨hp.1.1,by linarith [hp.1.2]⟩,mem_univ _⟩

def electricConeBoundary (s : Solution) (T : ℝ) (x : Vec) (i : Fin 3) (a : ℝ) : ℝ :=
  freeWave (fun y => s.E (a,y) i) (fun y => curl (fun z => s.B (a,z)) y i) (T-a,x) -
    (4*Real.pi)⁻¹ * (∫ n : Sphere, (T-a)^2*dot n.1
      (retardedElectricFlux s T x i (x+(T-a) • n.1)) ∂sphereMeasure) -
    (4*Real.pi)⁻¹ * (∫ n : Sphere, (T-a)*n.1 i*
      rho (fun z => s.f (a,z)) (x+(T-a) • n.1) ∂sphereMeasure) -
    waveK (fun y => current (fun z => s.f (a,z)) y i) (T-a,x)

def magneticConeBoundary (s : Solution) (T : ℝ) (x : Vec) (i : Fin 3) (a : ℝ) : ℝ :=
  freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T-a,x) -
    (4*Real.pi)⁻¹ * (∫ n : Sphere, (T-a)^2*dot n.1
      (retardedMagneticFlux s T x i (x+(T-a) • n.1)) ∂sphereMeasure) +
    (4*Real.pi)⁻¹ * (∫ n : Sphere,
      (T-a)*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+(T-a) • n.1) (curlB i) -
      (T-a)*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+(T-a) • n.1) (curlA i) ∂sphereMeasure)

lemma continuousOn_electricConeBoundary {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (electricConeBoundary s T x i) (Icc 0 (T/2)) := by
  have hc := hs.2.2.2.2.2.2.1
  have hE : ContDiffOn ℝ ∞ s.E (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.1.mono (fun p hp => hp.1)
  have hB : ContDiffOn ℝ ∞ s.B (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.2.mono (fun p hp => hp.1)
  have hcurl := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
    (continuousOn_slab_curl hT (hB.of_le (by decide)))
  have hfree := (continuousOn_freeWave_slab hT hE hcurl x i).mono
    (show Icc 0 (T/2) ⊆ Icc 0 T from fun a ha => ⟨ha.1,by linarith [ha.2]⟩)
  have hflux := continuousOn_electric_flux_boundary hs.1 hc hT x i
  have hdot := (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hflux)
  have hflux' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).pow 2).mul hdot)
  have hrho := continuousOn_cone_boundary_comp hT (hs.regularParticle.rho_continuous_slab hT.le) x
  have hni : Continuous (fun p : ℝ × Vec => p.2 i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_snd
  have hrho' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).mul hni.continuousOn).mul hrho)
  have hj := continuousOn_cone_boundary_comp hT (hs.regularParticle.current_continuous_slab hT.le) x
  have hji := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn hj
  have hj' := continuousOn_integral_sphere hji
  exact ((hfree.sub (hflux'.const_mul ((4*Real.pi)⁻¹))).sub
    (hrho'.const_mul ((4*Real.pi)⁻¹))).sub
      ((((continuousOn_const (c:=T)).sub continuousOn_id).mul hj').const_mul ((4*Real.pi)⁻¹))

lemma continuousOn_magneticConeBoundary {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (magneticConeBoundary s T x i) (Icc 0 (T/2)) := by
  have hc := hs.2.2.2.2.2.2.1
  have hE : ContDiffOn ℝ ∞ s.E (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.1.mono (fun p hp => hp.1)
  have hB : ContDiffOn ℝ ∞ s.B (Icc 0 T ×ˢ (univ : Set Vec)) := (hm T hT.le).2.2.mono (fun p hp => hp.1)
  have hcurl := ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
    (continuousOn_slab_curl hT (hE.of_le (by decide)))).neg
  have hfree := (continuousOn_freeWave_slab hT hB hcurl x i).mono
    (show Icc 0 (T/2) ⊆ Icc 0 T from fun a ha => ⟨ha.1,by linarith [ha.2]⟩)
  have hflux := continuousOn_magnetic_flux_boundary hs.1 hc hT x i
  have hdot := (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hflux)
  have hflux' := continuousOn_integral_sphere
    ((((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).pow 2).mul hdot)
  have hj := continuousOn_cone_boundary_comp hT (hs.regularParticle.current_continuous_slab hT.le) x
  have hterm (j k : Fin 3) := (((continuousOn_const (c:=T)).sub continuous_fst.continuousOn).mul
    (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp continuous_snd).continuousOn)).mul
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).continuous.comp_continuousOn hj)
  have hj' := continuousOn_integral_sphere ((hterm (curlA i) (curlB i)).sub (hterm (curlB i) (curlA i)))
  exact (hfree.sub (hflux'.const_mul ((4*Real.pi)⁻¹))).add (hj'.const_mul ((4*Real.pi)⁻¹))

lemma classical_electric_physical_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    s.E (T,x) i = electricConeBoundary s T x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedElectricDensity s T x (x+z) i) := by
  have hc := hs.2.2.2.2.2.2.1
  have hD : IntegrableOn (fun z => retardedElectricDensity s T x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedElectricDensity_le hs.1 hs.2.1 hs.2.2.1 hc hT.le le_rfl x)
  have hlim := (tendsto_right_of_continuousOn_Icc (show 0<T/2 by linarith)
    (continuousOn_electricConeBoundary hs hm hT x i)).add
    ((integral_ball_radius_tendsto hT hD).const_mul ((4*Real.pi)⁻¹))
  have heq : (fun a : ℝ => electricConeBoundary s T x i a + (4*Real.pi)⁻¹ *
      (∫ z in ball (0:Vec) (T-a), retardedElectricDensity s T x (x+z) i)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => s.E (T,x) i) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    have he := classical_shifted_electric_physical_representation hs hm ha.1
      (show 0<T-a by linarith [ha.2]) x i
    rw [show a+(T-a)=T by ring] at he
    unfold electricConeBoundary
    linarith
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds |>.symm

lemma classical_magnetic_physical_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    s.B (T,x) i = magneticConeBoundary s T x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s T x (x+z) i) := by
  have hc := hs.2.2.2.2.2.2.1
  have hD : IntegrableOn (fun z => retardedMagneticDensity s T x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedMagneticDensity_le hs.1 hs.2.1 hs.2.2.1 hc hT.le le_rfl x)
  have hlim := (tendsto_right_of_continuousOn_Icc (show 0<T/2 by linarith)
    (continuousOn_magneticConeBoundary hs hm hT x i)).add
    ((integral_ball_radius_tendsto hT hD).const_mul ((4*Real.pi)⁻¹))
  have heq : (fun a : ℝ => magneticConeBoundary s T x i a + (4*Real.pi)⁻¹ *
      (∫ z in ball (0:Vec) (T-a), retardedMagneticDensity s T x (x+z) i)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun _ => s.B (T,x) i) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with a ha
    have he := classical_shifted_magnetic_physical_representation hs hm ha.1
      (show 0<T-a by linarith [ha.2]) x i
    rw [show a+(T-a)=T by ring] at he
    unfold magneticConeBoundary
    linarith
  exact tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds |>.symm

end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma transport_retarded_electric_integral_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hV : TransportFor s s.E s.B) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (i : Fin 3) :
    (∫ v : Vec, ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y)))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedG x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedG x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedG hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hki : Continuous (fun v => physicalElectricKernel (coneRadius x y) (coneDirection x y)
      (velocity v) (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
        cross (velocity v) (s.B (t-coneRadius x y,y)))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hk
  have hid := classical_retarded_integral_identity
    (L := fun v => ((coneRadius x y)^2)⁻¹*coneDirection x y i*s.f (t-coneRadius x y,y,v) +
      (coneDirection x y i-velocity v i)/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    exact hV (t-coneRadius x y) (y,v)
  simpa only [retardedDensity,mul_assoc] using retarded_electric_density_identity hf' hxy hv i

lemma transport_retarded_magnetic_integral_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hV : TransportFor s s.E s.B) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (i : Fin 3) :
    (∫ v : Vec, -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y))))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedH x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedH x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedH hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hkc : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y)))))) :=
    (contDiff_cross (k:=1)).continuous.comp (continuous_const.prodMk hk)
  have hki : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y))))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hkc
  have hid := classical_retarded_integral_identity
    (L := fun v => -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    exact hV (t-coneRadius x y) (y,v)
  simpa only [retardedDensity,mul_assoc] using retarded_magnetic_density_identity hf' hxy hv i

lemma transport_retarded_electric_moment_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hV : TransportFor s s.E s.B) {x y : Vec} {t : ℝ}
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
  convert transport_retarded_electric_integral_identity hf hc hV hxy ht i using 1
  congr 1
  funext v
  dsimp only
  ring

lemma transport_retarded_magnetic_moment_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hV : TransportFor s s.E s.B) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (i : Fin 3) :
    -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (current (fun z => s.f (t-coneRadius x y,z)) y) i -
      (coneRadius x y)⁻¹*(coneDirection x y (curlA i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlB i)) (1,0) (t-coneRadius x y,y) -
        coneDirection x y (curlB i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlA i)) (1,0) (t-coneRadius x y,y)) =
      retardedMagneticDensity s t x y i - divergence (retardedMagneticFlux s t x i) y := by
  have hr : RegularParticle s.f := ⟨hf,hc⟩
  have hcv : ContDiff ℝ 1 (fun v : Vec => cross (coneDirection x y) (velocity v) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp
      (contDiff_cross.comp (contDiff_const.prodMk contDiff_velocity))
  have hi := hr.moment_integrable (contDiff_velocity (k:=1)).continuous ht.le y
  have hcross : cross (coneDirection x y) (current (fun z => s.f (t-coneRadius x y,z)) y) i =
      ∫ v : Vec, cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) := by
    have hi' := (crossCLM (coneDirection x y)).integrable_comp hi
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi'
    unfold current
    rw [← integral_cross_left hi]
    simpa only [crossCLM_apply,PiLp.proj_apply,cross_smul_right,PiLp.smul_apply,smul_eq_mul,mul_comm] using he.symm
  have hdt : coneDirection x y (curlA i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlB i)) (1,0) (t-coneRadius x y,y) -
        coneDirection x y (curlB i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlA i)) (1,0) (t-coneRadius x y,y) =
      ∫ v : Vec, cross (coneDirection x y) (velocity v) i*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0) := by
    have hInt (k : Fin 3) : Integrable (fun v : Vec => velocity v k*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) := hr.time_moment_integrable
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).continuous.comp (contDiff_velocity (k:=1)).continuous) ht y
    rw [dirD_current_component hr ht y,dirD_current_component hr ht y,
      ← integral_const_mul,← integral_const_mul,← integral_sub ((hInt _).const_mul _) ((hInt _).const_mul _)]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [cross_apply_cyclic]
    ring
  rw [hcross,hdt,retardedMagneticDensity_component hf hc hxy ht.le i,
    ← integral_const_mul,← integral_const_mul,
    ← integral_sub ((hr.scalar_moment_integrable hcv.continuous ht.le y).const_mul _)
      ((hr.time_moment_integrable hcv.continuous ht y).const_mul _)]
  unfold retardedMagneticFlux
  convert transport_retarded_magnetic_integral_identity hf hc hV hxy ht i using 1
  congr 1
  funext v
  dsimp only
  ring

lemma electricMomentDensity_transport {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hV : TransportFor s s.E s.B) {t : ℝ} (x : Vec) (i : Fin 3)
    {z : Vec} (hz : z≠0) (hzt : ‖z‖<t) :
    electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
      (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z =
      retardedElectricDensity s t x (x+z) i -
        divergence (retardedElectricFlux s t x i) (x+z) := by
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<t-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have he := transport_retarded_electric_moment_identity hf hc hV hxy ht i
  rw [← retardedElectricDensity_component hf hc hxy ht.le i] at he
  change _ = _ - divergence (retardedElectricFlux s t x i) (x+z) at he
  rw [← he]
  simp only [electricMomentDensity,coneRadius_add,coneDirection_add,PiLp.neg_apply,
    PiLp.smul_apply,smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma magneticMomentDensity_transport {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (hV : TransportFor s s.E s.B) {t : ℝ} (x : Vec) (i : Fin 3)
    {z : Vec} (hz : z≠0) (hzt : ‖z‖<t) :
    magneticMomentDensity (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z =
      retardedMagneticDensity s t x (x+z) i -
        divergence (retardedMagneticFlux s t x i) (x+z) := by
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<t-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have he := transport_retarded_magnetic_moment_identity hf hc hV hxy ht i
  rw [← he]
  simp only [magneticMomentDensity,coneRadius_add,coneDirection_add,PiLp.neg_apply,
    PiLp.smul_apply,smul_eq_mul,cross_apply_cyclic]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma divergence_ball_singular_closed_outer {t : ℝ} (ht : 0<t) {F : Vec → Vec}
    (hF : ∀ z, 0<‖z‖ → ‖z‖<t → ContDiffAt ℝ 1 F z)
    (hi : IntegrableOn (divergence F) (ball (0:Vec) t))
    (hzero : Tendsto (fun ε : ℝ => ∫ n : Sphere,
      ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) (𝓝[>] (0:ℝ)) (𝓝 0))
    (hb : ContinuousOn (fun p : ℝ × Vec => F ((t-p.1) • p.2))
      (Icc 0 (t/2) ×ˢ sphere (0:Vec) 1)) :
    (∫ z in ball (0:Vec) t, divergence F z) =
      ∫ n : Sphere, t^2*dot n.1 (F (t • n.1)) ∂sphereMeasure := by
  have hG : ContinuousOn (fun a : ℝ => ∫ n : Sphere,
      (t-a)^2*dot n.1 (F ((t-a) • n.1)) ∂sphereMeasure) (Icc 0 (t/2)) := by
    apply continuousOn_integral_sphere (F:=fun p : ℝ × Vec =>
      (t-p.1)^2*dot p.2 (F ((t-p.1) • p.2)))
    exact ((continuous_const.sub continuous_fst).pow 2).continuousOn.mul
      ((contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
        (continuous_snd.continuousOn.prodMk hb))
  have hlim := tendsto_right_of_continuousOn_Icc (show 0<t/2 by linarith) hG
  simp only [sub_zero] at hlim
  have he : (fun a : ℝ => ∫ z in ball (0:Vec) (t-a), divergence F z) =ᶠ[𝓝[>] (0:ℝ)]
      (fun a => ∫ n : Sphere, (t-a)^2*dot n.1 (F ((t-a) • n.1)) ∂sphereMeasure) := by
    filter_upwards [Ioo_mem_nhdsGT ht] with a ha
    exact divergence_ball_singular (show 0<t-a by linarith [ha.2])
      (show t-a<t by linarith [ha.1]) hF (hi.mono_set (ball_subset_ball (by linarith [ha.1]))) hzero
  exact tendsto_nhds_unique (integral_ball_radius_tendsto ht hi) (hlim.congr' he.symm)

lemma integrated_electricMomentDensity_transport {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) t, electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
      (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) =
      (∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) i) -
      ∫ n : Sphere, t^2*dot n.1 (retardedElectricFlux s t x i (x+t • n.1)) ∂sphereMeasure := by
  have hM := integrableOn_electricMomentDensity hρ hj ht.le x i
  have hD := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
    (integrableOn_retardedElectricDensity_le hf hE hB hc ht.le le_rfl x)
  change IntegrableOn (fun z : Vec => retardedElectricDensity s t x (x+z) i) (ball (0:Vec) t) at hD
  let F : Vec → Vec := fun z => retardedElectricFlux s t x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) t)]
      (fun z => retardedElectricDensity s t x (x+z) i - electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
      (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := electricMomentDensity_transport hf hc hV x i hz0
      (by simpa only [mem_ball_zero_iff] using hz)
    dsimp only [F]
    rw [divergence_add_right]
    linarith
  have hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<t → ContDiffAt ℝ 1 F z := by
    intro z hz hzt
    have hxy : x≠x+z := by
      intro h
      apply (norm_pos_iff.mp hz)
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    have hp : x+z ∈ retardedSpaceDomain t x := ⟨hxy,by rw [coneRadius_add]; linarith⟩
    exact ((contDiffOn_retarded_flux hf hc ht.le x i).contDiffAt
      ((isOpen_retardedSpaceDomain t x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) t) := (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular_closed_outer ht hF hi
    (retarded_flux_tip hf hc ht x i)
    (continuousOn_electric_flux_boundary hf hc ht x i)
  have hh : (∫ z in ball (0:Vec) t, divergence F z) =
      (∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) i) -
      (∫ z in ball (0:Vec) t, electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
      (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, t^2*dot n.1 (retardedElectricFlux s t x i (x+t • n.1)) ∂sphereMeasure at hg
  linarith

lemma integrated_magneticMomentDensity_transport {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) t, magneticMomentDensity (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) =
      (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) i) -
      ∫ n : Sphere, t^2*dot n.1 (retardedMagneticFlux s t x i (x+t • n.1)) ∂sphereMeasure := by
  have hM := integrableOn_magneticMomentDensity hj t x i
  have hD := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
    (integrableOn_retardedMagneticDensity_le hf hE hB hc ht.le le_rfl x)
  change IntegrableOn (fun z : Vec => retardedMagneticDensity s t x (x+z) i) (ball (0:Vec) t) at hD
  let F : Vec → Vec := fun z => retardedMagneticFlux s t x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) t)]
      (fun z => retardedMagneticDensity s t x (x+z) i - magneticMomentDensity (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := magneticMomentDensity_transport hf hc hV x i hz0
      (by simpa only [mem_ball_zero_iff] using hz)
    dsimp only [F]
    rw [divergence_add_right]
    linarith
  have hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<t → ContDiffAt ℝ 1 F z := by
    intro z hz hzt
    have hxy : x≠x+z := by
      intro h
      apply (norm_pos_iff.mp hz)
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    have hp : x+z ∈ retardedSpaceDomain t x := ⟨hxy,by rw [coneRadius_add]; linarith⟩
    exact ((contDiffOn_retardedMagnetic_flux hf hc ht.le x i).contDiffAt
      ((isOpen_retardedSpaceDomain t x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) t) := (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular_closed_outer ht hF hi
    (retarded_magnetic_flux_tip hf hc ht x i)
    (continuousOn_magnetic_flux_boundary hf hc ht x i)
  have hh : (∫ z in ball (0:Vec) t, divergence F z) =
      (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) i) -
      (∫ z in ball (0:Vec) t, magneticMomentDensity (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, t^2*dot n.1 (retardedMagneticFlux s t x i (x+t • n.1)) ∂sphereMeasure at hg
  linarith

lemma mixed_electric_physical_representation {s : Solution} {E' B' : Field}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor {s with E:=E',B:=B'}) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    E' (t,x) i = electricConeBoundary {s with E:=E',B:=B'} t x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z) i) := by
  have he := maxwell_electric_potential_representation hE' hB' hj hρ ht.le
    (fun r hr y => (hM r hr.1 y).1)
    (fun r hr y => (hM r hr.1.le y).2.1)
    (fun r hr y => by
      rw [← spaceDiv_slice (hE'.differentiable (by simp))]
      exact (hM r hr.1.le y).2.2.1) x i
  rw [electricPotentialComponent_ball hρ hj ht] at he
  change E' (t,x) i = _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t,
    electricMomentDensity (fun p => rho (fun q => s.f (p.1,q)) p.2)
      (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) - _ - _) at he
  rw [integrated_electricMomentDensity_transport hf hE hB hc hV hρ hj ht] at he
  simp_rw [spaceCurl_slice (hB'.differentiable (by simp))] at he
  simp only [electricConeBoundary,sub_zero,retardedElectricFlux] at he ⊢
  linarith

lemma mixed_magnetic_physical_representation {s : Solution} {E' B' : Field}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s s.E s.B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor {s with E:=E',B:=B'}) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    B' (t,x) i = magneticConeBoundary {s with E:=E',B:=B'} t x i 0 +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z) i) := by
  have he := maxwell_magnetic_potential_representation hE' hB' hj ht.le
    (fun r hr y => (hM r hr.1.le y).1)
    (fun r hr y => (hM r hr.1 y).2.1)
    (fun r hr y => by
      rw [← spaceDiv_slice (hB'.differentiable (by simp))]
      exact (hM r hr.1.le y).2.2.2) x i
  rw [magneticPotentialComponent_ball hj ht] at he
  change B' (t,x) i = _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t,
    magneticMomentDensity (fun p => current (fun q => s.f (p.1,q)) p.2) t x i z) + _) at he
  rw [integrated_magneticMomentDensity_transport hf hE hB hc hV hj ht] at he
  simp_rw [spaceCurl_slice (hE'.differentiable (by simp))] at he
  simp only [magneticConeBoundary,sub_zero,retardedMagneticFlux] at he ⊢
  linarith

end RVM

end

end OAI
