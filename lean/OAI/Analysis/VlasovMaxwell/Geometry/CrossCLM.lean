import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.WithinFlow
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

lemma cross_apply_cyclic (n v : Vec) (i : Fin 3) :
    cross n v i=n (curlA i)*v (curlB i)-n (curlB i)*v (curlA i) := by
  fin_cases i <;> simp [cross,curlA,curlB]

def crossCLM (n : Vec) : Vec →L[ℝ] Vec :=
  LinearMap.mkContinuous
    { toFun := cross n
      map_add' := by intro a b; ext i; fin_cases i <;> simp [cross] <;> ring
      map_smul' := by intro a b; exact cross_smul_right n b a }
    ‖n‖ (fun v => norm_cross_le n v)

lemma crossCLM_apply (n v : Vec) : crossCLM n v=cross n v := rfl

lemma integral_cross_left {F : Vec → Vec} (hF : Integrable F) (n : Vec) :
    (∫ v : Vec, cross n (F v))=cross n (∫ v : Vec, F v) :=
  (crossCLM n).integral_comp_comm hF

def retardedMagneticDensity (s : Solution) (t : ℝ) (x y : Vec) : Vec :=
  cross (coneDirection x y) (retardedElectricDensity s t x y)

def retardedMagneticFlux (s : Solution) (t : ℝ) (x : Vec) (i : Fin 3) (y : Vec) : Vec :=
  ∫ v : Vec, (retardedDensity s.f t x (y,v)*retardedH x (y,v) i) • velocity v

lemma integrable_retardedElectricDensity_integrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) :
    Integrable (fun v : Vec =>
      (s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))) •
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) := by
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht y
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  exact ((hreg.continuous.mul hd).smul hk).integrable_of_hasCompactSupport (hcomp.mul_right.smul_right)

lemma retardedMagneticDensity_component {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    retardedMagneticDensity s t x y i =
    ∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
      cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) i := by
  have hi := integrable_retardedElectricDensity_integrand hf hc hxy ht
  have hcross := (crossCLM (coneDirection x y)).integrable_comp hi
  unfold retardedMagneticDensity retardedElectricDensity
  rw [← integral_cross_left hi]
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hcross
  simpa only [crossCLM_apply,PiLp.proj_apply,cross_smul_right,PiLp.smul_apply,smul_eq_mul] using he.symm

lemma integrable_retarded_flux_integrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    Integrable (fun v : Vec => (retardedDensity s.f t x (y,v)*retardedG x (y,v) i) • velocity v) := by
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht y
  have hG : Continuous (fun v : Vec => retardedG x (y,v) i) :=
    (PiLp.continuous_apply 2 _ i).comp (contDiff_retardedG_velocity (k:=1) hxy).continuous
  exact ((hreg.continuous.mul hG).smul (contDiff_velocity (k:=1)).continuous).integrable_of_hasCompactSupport
    (hcomp.mul_right.smul_right)

lemma retardedMagneticFlux_components {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    retardedMagneticFlux s t x i y =
      coneDirection x y (curlA i) • retardedElectricFlux s t x (curlB i) y -
      coneDirection x y (curlB i) • retardedElectricFlux s t x (curlA i) y := by
  have hA : Integrable (fun v : Vec => coneDirection x y (curlA i) •
      ((retardedDensity s.f t x (y,v)*retardedG x (y,v) (curlB i)) • velocity v)) :=
    (integrable_retarded_flux_integrand hf hc hxy ht (curlB i)).fun_smul (coneDirection x y (curlA i))
  have hB : Integrable (fun v : Vec => coneDirection x y (curlB i) •
      ((retardedDensity s.f t x (y,v)*retardedG x (y,v) (curlA i)) • velocity v)) :=
    (integrable_retarded_flux_integrand hf hc hxy ht (curlA i)).fun_smul (coneDirection x y (curlB i))
  unfold retardedMagneticFlux retardedElectricFlux
  rw [← integral_smul,← integral_smul,← integral_sub hA hB]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [retardedH,cross_apply_cyclic]
  simp only [smul_smul,← sub_smul]
  congr 1
  ring

lemma contDiffOn_retardedMagnetic_flux {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0≤t) (x : Vec) (i : Fin 3) :
    ContDiffOn ℝ 1 (retardedMagneticFlux s t x i) (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,hF,hz⟩ := retarded_local_data hf hc ht x
  have hG : ContDiffOn ℝ 1 (fun z => retardedH x z i) (retardedSpaceDomain t x ×ˢ univ) := by
    intro z hz
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp z
      (contDiffAt_retardedH hz.1.1)).contDiffWithinAt
  apply contDiffOn_integral_uniform_support (isOpen_retardedSpaceDomain t x) hK
    ((hF.mul hG).smul (contDiff_velocity.comp contDiff_snd).contDiffOn)
  intro y hy v hv
  change (retardedDensity s.f t x (y,v)*retardedH x (y,v) i) • velocity v=0
  rw [hz y hy v hv,zero_mul,zero_smul]

lemma retarded_magnetic_flux_norm_bound {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖retardedMagneticFlux s t x i (x+z)‖≤C/‖z‖ := by
  obtain ⟨CA,hCA,hA⟩ := retarded_flux_norm_bound hf hc hR hRt x (curlA i)
  obtain ⟨CB,hCB,hB⟩ := retarded_flux_norm_bound hf hc hR hRt x (curlB i)
  refine ⟨CA+CB,add_nonneg hCA hCB,?_⟩
  intro z hz hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0≤t-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hn (j : Fin 3) : ‖coneDirection x (x+z) j‖≤1 :=
    (PiLp.norm_apply_le _ j).trans_eq (coneDirection_norm hxy)
  rw [retardedMagneticFlux_components hf hc hxy ht i]
  calc
    _ ≤ ‖coneDirection x (x+z) (curlA i) • retardedElectricFlux s t x (curlB i) (x+z)‖ +
        ‖coneDirection x (x+z) (curlB i) • retardedElectricFlux s t x (curlA i) (x+z)‖ := norm_sub_le _ _
    _ ≤ CB/‖z‖+CA/‖z‖ := by
      apply add_le_add
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hn _)).trans (hB z hz hzR)
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hn _)).trans (hA z hz hzR)
    _ = (CA+CB)/‖z‖ := by ring

lemma retarded_magnetic_flux_tip {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1
      (retardedMagneticFlux s t x i (x+ε • n.1)) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := retarded_magnetic_flux_norm_bound hf hc (show 0≤t/2 by linarith)
    (show t/2<t by linarith) x i
  apply spherical_flux_tendsto_zero (C:=C) (R:=t/2)
    (F:=fun z => retardedMagneticFlux s t x i (x+z)) (show 0<t/2 by linarith)
  intro z hz hzR
  exact hbound z hz hzR.le
end RVM

end

end OAI
