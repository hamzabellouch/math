import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ShiftedRho
import OAI.Analysis.VlasovMaxwell.Geometry.CrossCLM

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

lemma contDiffOn_retardedMagneticDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedMagneticDensity s t x) (retardedSpaceDomain t x) := by
  intro y hy
  have hn : ContDiffAt ℝ 1 (coneDirection x) y := contDiffAt_coneDirection hy.1
  exact (contDiff_cross.contDiffAt.comp y (hn.prodMk
    ((contDiffOn_retardedElectricDensity hf hE hB hc ht x).contDiffAt
      ((isOpen_retardedSpaceDomain t x).mem_nhds hy)))).contDiffWithinAt

lemma integrableOn_retardedMagneticDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) :
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt.le
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont := (contDiffOn_retardedMagneticDensity hf hE hB hc ht x).continuousOn.comp
    (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=C) (by norm_num) hcont
  intro z hz hzR
  have hxy : x≠x+z := (hm ⟨by simpa only [mem_ball_zero_iff] using hzR,by simpa only [mem_singleton_iff] using norm_pos_iff.mp hz⟩).1
  calc
    ‖retardedMagneticDensity s t x (x+z)‖ ≤ ‖coneDirection x (x+z)‖*‖retardedElectricDensity s t x (x+z)‖ := norm_cross_le _ _
    _ = ‖retardedElectricDensity s t x (x+z)‖ := by rw [coneDirection_norm hxy,one_mul]
    _ ≤ C/‖z‖^2 := hbound z hz hzR.le
    _ = C*‖z‖^(-(2:ℝ)) := by rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]; rfl

def magneticMomentDensity (j : Field) (t : ℝ) (x : Vec) (i : Fin 3) (z : Vec) : ℝ :=
  z (curlA i)/‖z‖^2*dirD (fun p => j p (curlB i)) (1,0) (t-‖z‖,x+z) +
    z (curlA i)/‖z‖^3*j (t-‖z‖,x+z) (curlB i) -
    (z (curlB i)/‖z‖^2*dirD (fun p => j p (curlA i)) (1,0) (t-‖z‖,x+z) +
    z (curlB i)/‖z‖^3*j (t-‖z‖,x+z) (curlA i))

lemma integrableOn_magneticMomentDensity {j : Field} (hj : ContDiff ℝ ∞ j)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    IntegrableOn (magneticMomentDensity j t x i) (ball (0:Vec) t) := by
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi (a b : Fin 3) : IntegrableOn (fun z : Vec =>
      z a/‖z‖^2*dirD (fun p => j p b) (1,0) (t-‖z‖,x+z) +
      z a/‖z‖^3*j (t-‖z‖,x+z) b) (ball (0:Vec) t) :=
    Integrable.add (integrableOn_ball_direction_div_norm_pow
      ((contDiff_dirD (contDiff_component hj b) _).continuous.comp harg) 1 (by norm_num) t a)
      (integrableOn_ball_direction_div_norm_pow
        ((contDiff_component hj b).continuous.comp harg) 2 (by norm_num) t a)
  exact (hi _ _).sub (hi _ _)

lemma classical_retarded_magnetic_moment_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : Equations s) {x y : Vec} {t : ℝ}
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
  convert classical_retarded_magnetic_integral_identity hf hc heq hxy ht i using 1
  congr 1
  funext v
  dsimp only
  ring

lemma magneticMomentDensity_actual {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ} (ha : 0<a)
    (x : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (hzt : ‖z‖<T) :
    magneticMomentDensity (shiftedCurrent s a) T x i z =
      retardedMagneticDensity s (a+T) x (x+z) i -
      divergence (retardedMagneticFlux s (a+T) x i) (x+z) := by
  have hc := hs.2.2.2.2.2.2.1
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<a+T-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hp : 0<a+(T-‖z‖) := by linarith
  have hj := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).2
  have hji (k : Fin 3) : DifferentiableAt ℝ
      (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) (a+(T-‖z‖),x+z) :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).contDiff.contDiffAt.comp _ hj).differentiableAt (by simp)
  have herr (k : Fin 3) : (fun p => shiftedCurrent s a p k)=
      positiveTimeShift a (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) := by
    funext p
    simp only [shiftedCurrent,positiveTimeShift,positiveTimeExtend,PiLp.smul_apply,smul_eq_mul]
  have hjder (k : Fin 3) : dirD (fun p => shiftedCurrent s a p k) (1,0) (T-‖z‖,x+z) =
      dirD (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) (1,0) (a+(T-‖z‖),x+z) := by
    rw [herr]
    unfold dirD
    rw [fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ (hji k)]
  have hjval : shiftedCurrent s a (T-‖z‖,x+z)=current (fun q => s.f (a+(T-‖z‖),q)) (x+z) :=
    positiveTimeShift_eq ha (sub_nonneg.mpr hzt.le) _ _
  unfold magneticMomentDensity
  rw [hjder,hjder,hjval]
  have he := classical_retarded_magnetic_moment_identity hs.1 hc hs.2.2.2.2.2.2.2.1 hxy ht i
  rw [← he,cross_apply_cyclic]
  simp only [coneRadius_add,coneDirection_add,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
    show a+T-‖z‖=a+(T-‖z‖) by ring]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma integrated_magneticMomentDensity_actual {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure := by
  have hc := hs.2.2.2.2.2.2.1
  have hρj := contDiff_shifted_moments hs hm ha
  have hM := integrableOn_magneticMomentDensity hρj.2 T x i
  have hD : IntegrableOn (fun z : Vec => retardedMagneticDensity s (a+T) x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedMagneticDensity hs.1 hs.2.1 hs.2.2.1 hc hT.le (show T<a+T by linarith) x)
  let F : Vec → Vec := fun z => retardedMagneticFlux s (a+T) x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) T)]
      (fun z => retardedMagneticDensity s (a+T) x (x+z) i -
        magneticMomentDensity (shiftedCurrent s a) T x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := magneticMomentDensity_actual hs hm ha x i hz0 (by simpa only [mem_ball_zero_iff] using hz)
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
    exact ((contDiffOn_retardedMagnetic_flux hs.1 hc (by linarith) x i).contDiffAt
      ((isOpen_retardedSpaceDomain (a+T) x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) T) := (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular hT (show T<a+T by linarith) hF hi
    (retarded_magnetic_flux_tip hs.1 hc (show 0<a+T by linarith) x i)
  have hh : (∫ z in ball (0:Vec) T, divergence F z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure at hg
  linarith

lemma classical_shifted_magnetic_physical_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
        (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) +
      (4*Real.pi)⁻¹ * (∫ n : Sphere,
        T*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlB i) -
        T*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlA i) ∂sphereMeasure) := by
  have hρj := contDiff_shifted_moments hs hm ha
  rw [classical_shifted_magnetic_potential_representation hs hm ha hT.le x i]
  change _ + magneticPotentialComponent (shiftedCurrent s a) i (T,x)=_
  rw [magneticPotentialComponent_ball hρj.2 hT]
  change _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T,
      magneticMomentDensity (shiftedCurrent s a) T x i z) + _)=_
  rw [integrated_magneticMomentDensity_actual hs hm ha hT x i]
  have hj0 (y : Vec) : shiftedCurrent s a (0,y)=current (fun z => s.f (a,z)) y := by
    simp only [shiftedCurrent,positiveTimeShift_eq ha (le_refl 0),add_zero]
  simp_rw [hj0]
  ring
end RVM

end

end OAI
