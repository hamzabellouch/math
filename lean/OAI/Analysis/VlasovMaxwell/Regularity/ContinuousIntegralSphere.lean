import Mathlib
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

lemma continuousOn_integral_sphere {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {S : Set H} {F : H × Vec → W}
    (hF : ContinuousOn F (S ×ˢ sphere (0:Vec) 1)) :
    ContinuousOn (fun p => ∫ n : Sphere, F (p,n.1) ∂sphereMeasure) S := by
  have hc : ContinuousOn (fun p : H × Sphere => F (p.1,p.2.1)) (S ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1,p.2.2⟩)
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc
  intro p n _ hn
  exact (hn (mem_univ n)).elim

lemma integral_ball_radius_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t : ℝ} (ht : 0<t) (hF : IntegrableOn F (ball (0:Vec) t)) :
    Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) (t-a), F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t, F z)) := by
  have hh : Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) t,
      (ball (0:Vec) (t-a)).indicator F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t, F z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    · exact Eventually.of_forall (fun a => hF.aestronglyMeasurable.indicator measurableSet_ball)
    · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => norm_indicator_le_norm_self _ _))
    · exact hF.norm
    · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      have hn : ‖z‖<t := by simpa only [mem_ball_zero_iff] using hz
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (show 0<t-‖z‖ by linarith)] with a ha
      symm
      apply indicator_of_mem
      simpa only [mem_ball_zero_iff] using (show ‖z‖<t-a by linarith [ha.2])
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  rw [setIntegral_indicator measurableSet_ball,inter_eq_right.mpr (ball_subset_ball (by linarith [ha.1]))]

lemma freeWave_sphere {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (r : ℝ) (x : Vec) :
    freeWave g h (r,x) = (4*Real.pi)⁻¹ *
      ((∫ n : Sphere, g (x+r • n.1) ∂sphereMeasure) +
        r*(∫ n : Sphere, fderiv ℝ g (x+r • n.1) n.1 ∂sphereMeasure)) +
      (4*Real.pi)⁻¹ * (r*∫ n : Sphere, h (x+r • n.1) ∂sphereMeasure) := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp))]
  have hd := ((hasDerivAt_id r).mul (sphereSum_radial_deriv (hg.of_le (by simp)) x r)).const_mul ((4*Real.pi)⁻¹)
  change HasDerivAt (fun t => waveK g (t,x)) _ r at hd
  rw [hd.deriv]
  simp only [id_eq,one_mul,waveK,sphereSum]

lemma contDiff_slab_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × Vec → W} {k : ℕ∞ω} {T a : ℝ}
    (hF : ContDiffOn ℝ k F (Icc 0 T ×ˢ (univ : Set Vec))) (ha : a ∈ Icc 0 T) :
    ContDiff ℝ k (fun y => F (a,y)) := by
  apply contDiffOn_univ.mp
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y _ => ⟨ha,mem_univ y⟩)

lemma spatialPartial_spaceDerivative {F : Field} {T a : ℝ}
    (hF : ContDiffOn ℝ 1 F (Icc 0 T ×ˢ (univ : Set Vec))) (ha : a ∈ Icc 0 T)
    (y : Vec) (i j : Fin 3) :
    spatialPartial (fun z => F (a,z) i) y j = spaceDerivative F (a,y) (basis j) i := by
  have h := hasFDerivAt_time_slice hF ha y
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y h
  change HasFDerivAt (fun z => F (a,z) i) _ y at hi
  rw [spatialPartial,hi.fderiv,spaceDerivative,h.fderiv]
  rfl

lemma continuousOn_slab_curl {F : Field} {T : ℝ} (hT : 0<T)
    (hF : ContDiffOn ℝ 2 F (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContinuousOn (fun p : ℝ × Vec => curl (fun y => F (p.1,y)) p.2)
      (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hc := (contDiffOn_spaceDerivative hT hF).continuousOn
  have hh (i j : Fin 3) : ContinuousOn
      (fun p : ℝ × Vec => spatialPartial (fun y => F (p.1,y) i) p.2 j)
      (Icc 0 T ×ˢ (univ : Set Vec)) := by
    have ht := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
      (hc.clm_apply (continuousOn_const (c:=basis j)))
    apply ht.congr
    intro p hp
    exact spatialPartial_spaceDerivative (hF.of_le (by decide)) hp.1 p.2 i j
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  fin_cases i <;> exact (hh _ _).sub (hh _ _)

lemma continuousOn_freeWave_slab {F : Field} {H : ℝ × Vec → ℝ} {T : ℝ} (hT : 0<T)
    (hF : ContDiffOn ℝ ∞ F (Icc 0 T ×ˢ (univ : Set Vec)))
    (hH : ContinuousOn H (Icc 0 T ×ˢ (univ : Set Vec))) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun a : ℝ => freeWave (fun y => F (a,y) i) (fun y => H (a,y)) (T-a,x))
      (Icc 0 T) := by
  let S : Set (ℝ × Vec) := Icc 0 T ×ˢ sphere (0:Vec) 1
  let A : ℝ × Vec → ℝ × Vec := fun p => (p.1,x+(T-p.1) • p.2)
  have hA : Continuous A := continuous_fst.prodMk
    (continuous_const.add ((continuous_const.sub continuous_fst).smul continuous_snd))
  have hmap : MapsTo A S (Icc 0 T ×ˢ (univ : Set Vec)) := fun p hp => ⟨hp.1,mem_univ _⟩
  have hval : ContinuousOn (fun p : ℝ × Vec => F (p.1,x+(T-p.1) • p.2) i) S :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
      (hF.continuousOn.comp hA.continuousOn hmap)
  have hder : ContinuousOn (fun p : ℝ × Vec => spaceDerivative F (p.1,x+(T-p.1) • p.2) p.2 i) S :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn
      (((contDiffOn_spaceDerivative hT (hF.of_le (by decide))).continuousOn.comp hA.continuousOn hmap).clm_apply
        continuous_snd.continuousOn)
  have hH' := hH.comp hA.continuousOn hmap
  have hv := continuousOn_integral_sphere hval
  have hd := continuousOn_integral_sphere hder
  have hh := continuousOn_integral_sphere hH'
  have he := (hv.add (((continuousOn_const (c:=T)).sub continuousOn_id).mul hd)).const_mul ((4*Real.pi)⁻¹)
  have he' := he.add ((((continuousOn_const (c:=T)).sub continuousOn_id).mul hh).const_mul ((4*Real.pi)⁻¹))
  apply he'.congr
  intro a ha
  have hf := contDiff_component (contDiff_slab_slice hF ha) i
  dsimp only [A,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,id_eq,Function.comp_apply]
  rw [freeWave_sphere hf]
  congr 2
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with n
  have h := hasFDerivAt_time_slice (hF.of_le (by decide)) ha (x+(T-a) • n.1)
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp _ h
  change HasFDerivAt (fun y => F (a,y) i) _ (x+(T-a) • n.1) at hi
  rw [hi.fderiv,spaceDerivative,h.fderiv]
  rfl

lemma coneBoundary_radius {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : coneRadius x (x+(T-a) • n)=T-a := by
  rw [coneRadius_add,norm_smul,Real.norm_of_nonneg (by linarith [ha.2]),
    show ‖n‖=1 by simpa only [mem_sphere,dist_zero_right] using hn,mul_one]

lemma coneBoundary_ne {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : x≠x+(T-a) • n := by
  intro he
  have hh := coneBoundary_radius hT ha hn x
  rw [← he,coneRadius,sub_self,norm_zero] at hh
  linarith [ha.2]

lemma continuousOn_weighted_cone_boundary {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {T : ℝ} (hT : 0<T) (x : Vec) {w : Phase → W}
    (hw : ∀ z : Phase, x≠z.1 → ContinuousAt w z) :
    ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, s.f (p.1,x+(T-p.1) • p.2,v) •
      w (x+(T-p.1) • p.2,v)) (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  obtain ⟨K,hK,hz⟩ := hc T hT.le
  let S : Set (ℝ × Vec) := Icc 0 (T/2) ×ˢ sphere (0:Vec) 1
  have harg : Continuous (fun p : (ℝ × Vec) × Vec => (p.1.1,x+(T-p.1.1) • p.1.2,p.2)) :=
    continuous_fst.fst.prodMk ((continuous_const.add
      ((continuous_const.sub continuous_fst.fst).smul continuous_fst.snd)).prodMk continuous_snd)
  have hcf := hf.continuousOn.comp harg.continuousOn (show MapsTo _ (S ×ˢ univ) particleHalfSpace from
    fun p hp => hp.1.1.1)
  have hwc : ContinuousOn (fun p : (ℝ × Vec) × Vec => w (x+(T-p.1.1) • p.1.2,p.2)) (S ×ˢ univ) := by
    intro p hp
    exact ((hw _ (coneBoundary_ne hT hp.1.1 hp.1.2 x)).comp
      (harg.snd.continuousAt)).continuousWithinAt
  apply continuousOn_integral_uniform_support (hK.image continuous_snd) (hcf.smul hwc)
  intro p hp v hv
  have ht : p.1 ∈ Icc 0 T := ⟨hp.1.1,by linarith [hp.1.2]⟩
  have hfz : s.f (p.1,x+(T-p.1) • p.2,v)=0 := by
    by_contra hne
    exact hv ⟨(x+(T-p.1) • p.2,v),hz _ ht (subset_tsupport _ hne),rfl⟩
  change s.f (p.1,x+(T-p.1) • p.2,v) • w (x+(T-p.1) • p.2,v)=0
  rw [hfz,zero_smul]

lemma continuousOn_electric_flux_boundary {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun p : ℝ × Vec => retardedElectricFlux s T x i (x+(T-p.1) • p.2))
      (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  have hw (z : Phase) (hz : x≠z.1) : ContinuousAt (fun z : Phase => retardedG x z i • velocity z.2) z :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp
      (contDiffAt_retardedG (k:=1) hz).continuousAt).smul
      ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousAt
  apply (continuousOn_weighted_cone_boundary hf hc hT x hw).congr
  intro p hp
  unfold retardedElectricFlux retardedDensity
  dsimp only
  rw [coneBoundary_radius hT hp.1 hp.2 x,sub_sub_cancel]
  congr 1
  funext v
  simp only [smul_smul]

lemma continuousOn_magnetic_flux_boundary {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {T : ℝ} (hT : 0<T) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun p : ℝ × Vec => retardedMagneticFlux s T x i (x+(T-p.1) • p.2))
      (Icc 0 (T/2) ×ˢ sphere (0:Vec) 1) := by
  have hw (z : Phase) (hz : x≠z.1) : ContinuousAt (fun z : Phase => retardedH x z i • velocity z.2) z :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp
      (contDiffAt_retardedH (k:=1) hz).continuousAt).smul
      ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousAt
  apply (continuousOn_weighted_cone_boundary hf hc hT x hw).congr
  intro p hp
  unfold retardedMagneticFlux retardedDensity
  dsimp only
  rw [coneBoundary_radius hT hp.1 hp.2 x,sub_sub_cancel]
  congr 1
  funext v
  simp only [smul_smul]

end RVM

end

end OAI
