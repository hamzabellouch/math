import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.InitialPuncturedCone
import OAI.Analysis.VlasovMaxwell.Geometry.ClippedRamp
import OAI.Analysis.VlasovMaxwell.Continuation.PrefixMomentumForce

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


def retardedMomentumForce (s : Solution) (α : Phase→ℝ→Phase) (T : ℝ)
    (zX zY : Phase) (σ : ℝ) : Vec :=
  let τ := branchTime α zX zY T σ
  let n := branchDirection α zX zY T σ
  ((1-dot n (velocity (α zY σ).2))/(1-dot n (velocity (α zX τ).2))) •
    (lorentzField s.E s.B (τ,α zX τ)).2

lemma PhaseFlowOn.momentumForce_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (fun t=>(lorentzField s.E s.B (t,F.flow z t)).2) (Ioo 0 T) := by
  have hf : ContinuousOn (F.flow z) (Ioo 0 T) :=
    (F.continuousOn_time z).mono Ioo_subset_Icc_self
  have hp : ContinuousOn (fun t=>(t,(F.flow z t).1)) (Ioo 0 T) :=
    continuousOn_id.prodMk hf.fst
  have hE := hs.E_smooth.continuousOn.comp hp
    (fun t ht=> ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hB := hs.B_smooth.continuousOn.comp hp
    (fun t ht=> ⟨Ioo_subset_Icc_self ht,mem_univ _⟩)
  have hu := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))

lemma PhaseFlowOn.retardedMomentum_regular {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c,(F.flow zX r).1≠(F.flow zY r).1) :
    ContDiffOn ℝ 1 (fun r=>(F.flow zX (branchTime F.flow zX zY T r)).2) (uIcc b c) ∧
    ContinuousOn (retardedMomentumForce s F.flow T zX zY) (uIcc b c) := by
  let τ := branchTime F.flow zX zY T
  have ht : ∀ r∈uIcc b c,τ r∈Ioo 0 T := by
    intro r hr
    have hh := F.branch_time_mem zX zY (hS hr) (hne r hr)
    exact ⟨(hS hr).1.1.trans hh.1,hh.2⟩
  have hτ : ContDiffOn ℝ 1 τ (uIcc b c) := fun r hr=>
    (F.branch_differential zX zY (hS hr) (hne r hr)).1.contDiffWithinAt
  have hX := (F.flow_contDiffOn hs zX).comp hτ ht
  obtain ⟨_,ha,hu,hn,_,_⟩ := F.actual_branch_regular hs zX zY hS hne
  have hd : ContinuousOn (fun r=>1-dot (branchDirection F.flow zX zY T r)
      (velocity (F.flow zY r).2)) (uIcc b c) :=
    continuousOn_const.sub ((contDiff_dot_pair (k:=0)).continuous.comp_continuousOn
      (hn.continuousOn.prodMk hu.continuousOn))
  have hD : ContinuousOn (fun r=>1-dot (branchDirection F.flow zX zY T r)
      (velocity (F.flow zX (τ r)).2)) (uIcc b c) :=
    continuousOn_const.sub ((contDiff_dot_pair (k:=0)).continuous.comp_continuousOn
      (hn.continuousOn.prodMk ha.continuousOn))
  refine ⟨hX.snd,?_⟩
  exact (hd.div hD (fun r hr=>(cone_denom_pos _ _
    (F.branchDirection_norm zX zY (hS hr) (hne r hr))).ne')).smul
    ((F.momentumForce_continuousOn hs zX).comp hτ.continuousOn ht)

lemma PhaseFlowOn.actual_projector_regular {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c,(F.flow zX r).1≠(F.flow zY r).1)
    (hv : ∀ r∈uIcc b c,(F.flow zX (branchTime F.flow zX zY T r)).2≠0) (w : ℝ) :
    let V := fun r=>(F.flow zX (branchTime F.flow zX zY T r)).2
    let W := fun r=>angularMultiplierCLM w (V r)
    let W' := fun r=>angularDerivativeCLM w (V r) (retardedMomentumForce s F.flow T zX zY r)
    ContDiffOn ℝ 1 W (uIcc b c) ∧ ContinuousOn W' (uIcc b c) ∧
      ∀ r∈uIoo b c,HasDerivAt W (W' r) r := by
  obtain ⟨hV,hK⟩ := F.retardedMomentum_regular hs zX zY hS hne
  refine ⟨?_,continuousOn_angularDerivativeCLM hV.continuousOn hK hv w,?_⟩
  · intro r hr
    exact (contDiffAt_angularMultiplierCLM w (hv r hr) (k:=1) (by simp)).comp_contDiffWithinAt r (hV r hr)
  · intro r hr
    have hh := Ioo_subset_Icc_self hr
    exact hasDerivAt_angularMultiplierCLM
      (F.retardedMomentum_hasDerivAt zX zY (hS hh) (hne r hh)) (hv r hh) w

lemma PhaseFlowOn.actual_selected_projected_identity {s : Solution} {T b c : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX zY : Phase)
    (hS : uIcc b c⊆branchDomain F.flow zX zY T)
    (hne : ∀ r∈uIcc b c,(F.flow zX r).1≠(F.flow zY r).1)
    (hv : ∀ r∈uIcc b c,(F.flow zX (branchTime F.flow zX zY T r)).2≠0)
    (w : ℝ) (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ}
    (hψ : AbsolutelyContinuousOnInterval ψ b c) :
    let χ := fun σ=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX zY σ)
    let τ := branchTime F.flow zX zY T
    let r := fun σ=>τ σ-σ
    let a := fun σ=>velocity (F.flow zX (τ σ)).2
    let u := fun σ=>velocity (F.flow zY σ).2
    let n := branchDirection F.flow zX zY T
    let W := fun σ=>angularMultiplierCLM w (F.flow zX (τ σ)).2
    let W' := fun σ=>angularDerivativeCLM w (F.flow zX (τ σ)).2
      (retardedMomentumForce s F.flow T zX zY σ)
    ∫ σ in b..c,(ψ σ*χ σ) • W σ (signedForceKernel (r σ) (a σ) (u σ) (n σ)
      (phaseAcceleration s.E s.B F.flow zY σ)) =
      (ψ b*χ b) • W b (retardedPrimitive (r b) (a b) (u b) (n b)) -
      (ψ c*χ c) • W c (retardedPrimitive (r c) (a c) (u c) (n c)) +
      ∫ σ in b..c,deriv (fun ξ=>ψ ξ*χ ξ) σ • W σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ)) +
        (ψ σ*χ σ) • (W' σ (retardedPrimitive (r σ) (a σ) (u σ) (n σ)) +
          W σ (signedRemainder (r σ) (a σ) (u σ) (n σ)
            (phaseAcceleration s.E s.B F.flow zX (τ σ)))) := by
  obtain ⟨hW,hW',hWd⟩ := F.actual_projector_regular hs zX zY hS hne hv w
  exact F.actual_selected_weighted_identity hs zX zY hS hne Q hψ hW hW' hWd

lemma angularDerivativeCLM_smul_force (w c : ℝ) (v K : Vec) :
    angularDerivativeCLM w v (c • K)=c • angularDerivativeCLM w v K := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [smul_apply,angularDerivativeCLM_apply,dot_smul_right,
    transverseProjection_smul,dot_smul_left]
  module

lemma moving_projector_measure_identity (w f r : ℝ) (v u n K : Vec)
    (hd : 1-dot n u≠0) (hD : 1-dot n (velocity v)≠0) :
    (f*(1-dot n (velocity v))) •
      angularDerivativeCLM w v (((1-dot n u)/(1-dot n (velocity v))) • K)
        (retardedPrimitive r (velocity v) u n) =
      (f/r) • angularDerivativeCLM w v K (signedPrimitive (velocity v) u n) := by
  rw [angularDerivativeCLM_smul_force,smul_apply,retardedPrimitive,map_smul]
  simp only [smul_smul]
  congr 1
  field_simp

lemma time_weight_measure_identity (f r c : ℝ) (a u n : Vec)
    (hd : 1-dot n u≠0) (hD : 1-dot n a≠0) :
    (f*(1-dot n a)) • ((c*((1-dot n u)/(1-dot n a))) • retardedPrimitive r a u n) =
      (f*c/r) • signedPrimitive a u n := by
  simp only [retardedPrimitive,smul_smul]
  congr 1
  field_simp

lemma moving_projector_small_kernel {w f r θ φ : ℝ} {v u n K : Vec}
    (hf : 0≤f) (hr : 0<r) (hv : v≠0) (hn : ‖n‖=1)
    (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1)
    (hD : φ^2/2≤1-dot n (velocity v)) (hun : ‖u-n‖≤4*θ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularDerivativeCLM w v K (signedPrimitive (velocity v) u n)‖ ≤
      156*f*|w| *θ*‖K‖/(r*‖v‖^2*φ) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hf hr.le)]
  calc
    _ ≤ (f/r)*(‖angularDerivativeCLM w v K‖*‖signedPrimitive (velocity v) u n‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (f/r)*((3*|w|/‖v‖^2*‖K‖)*(52*θ/φ)) := by
      gcongr
      · exact angularDerivativeCLM_norm_le w v K hv
      · exact small_primitive_norm hn hθ hφ hφ1 hD hun he
    _ = _ := by ring

lemma projected_time_weight_small_kernel {w f r θ φ : ℝ} {v u n : Vec}
    (hf : 0≤f) (hr : 0<r) (hθ : 0≤θ) (hφ : 0<φ)
    (hD : φ^2/2≤1-dot n (velocity v)) (hun : ‖u-n‖≤4*θ)
    (han : ‖velocity v-n‖≤4*φ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularMultiplierCLM w v (signedPrimitive (velocity v) u n)‖ ≤
      196*f*|w| *θ/(r*‖v‖) := by
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,norm_smul,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hf hr.le),
    abs_div,abs_norm]
  calc
    _ ≤ (f/r)*(|w|/‖v‖*(196*θ)) := by
      gcongr
      exact small_primitive_transverse hθ hφ hD hun han he
    _ = _ := by ring



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma projected_primitive_highband_kernel {w f r θ φ : ℝ} {v u n : Vec}
    (hw : 0<w) (hv : w/16≤‖v‖) (hf : 0≤f) (hr : 0<r)
    (hθ : 0≤θ) (hφ : 0<φ) (hD : φ^2/2≤1-dot n (velocity v))
    (hun : ‖u-n‖≤4*θ) (han : ‖velocity v-n‖≤4*φ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularMultiplierCLM w v (signedPrimitive (velocity v) u n)‖≤
      (3136*θ/r)*f := by
  have hvp : 0<‖v‖ := (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le hv
  have hratio : w/‖v‖≤16 := (div_le_iff₀ hvp).mpr (by linarith)
  calc
    _ ≤ 196*f*|w| *θ/(r*‖v‖) := projected_time_weight_small_kernel hf hr hθ hφ hD hun han he
    _ = (f/r)*((w/‖v‖)*(196*θ)) := by rw [abs_of_pos hw]; ring
    _ ≤ (f/r)*(16*(196*θ)) := by gcongr
    _ = _ := by ring

lemma moving_projector_highband_kernel {w f r θ φ : ℝ} {v u n K : Vec}
    (hw : 0<w) (hv : w/16≤‖v‖) (hf : 0≤f) (hr : 0<r) (hn : ‖n‖=1)
    (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hD : φ^2/2≤1-dot n (velocity v))
    (hun : ‖u-n‖≤4*θ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularDerivativeCLM w v K (signedPrimitive (velocity v) u n)‖≤
      (39936*θ/(w*φ))*‖K‖*(f/r) := by
  have hvp : 0<‖v‖ := (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le hv
  have hrho : w/‖v‖^2≤256/w := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hvp) hw).mpr
    nlinarith [sq_nonneg (‖v‖-w/16)]
  calc
    _ ≤ 156*f*|w| *θ*‖K‖/(r*‖v‖^2*φ) := moving_projector_small_kernel hf hr
      (norm_pos_iff.mp hvp) hn hθ hφ hφ1 hD hun he
    _ = (156*θ/φ*‖K‖*(f/r))*(w/‖v‖^2) := by rw [abs_of_pos hw]; ring
    _ ≤ (156*θ/φ*‖K‖*(f/r))*(256/w) := by gcongr
    _ = _ := by ring

def physicalProjectedPrimitiveDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (w : ℝ) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

lemma physicalProjectedPrimitiveDensity_bound {s : Solution} {X V : ℝ→Vec}
    {B : ClosedConeBin} {w θ φ : ℝ} {z : ConeCoordinate}
    (hw : 0<w) (hv : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤1-dot z.2.2.1 (velocity (V z.1)))
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalProjectedPrimitiveDensity s X V B w z≤
      ENNReal.ofReal (3136*θ)*ENNReal.ofReal (z.1-z.2.1)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have hhan : ‖velocity (V z.1)-z.2.2.1‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le (sphere_norm _).le (by positivity)
    rw [dot_comm]
    nlinarith
  have hpoint : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖≤
      ENNReal.ofReal (3136*θ/(z.1-z.2.1))*ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    have hdv : 1-dot z.2.2.1 (velocity v)≤8*θ^2 := hvbin.2.1.2.trans hd
    have hun : ‖velocity v-z.2.2.1‖≤4*θ := by
      apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le (sphere_norm _).le (by positivity)
      rw [dot_comm]
      nlinarith
    have he := small_deficit_difference (sphere_norm z.2.2) hθ hφ.le hsmall
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).le hdv hun hhan
    rw [←ENNReal.ofReal_mul (by positivity : 0≤3136*θ/(z.1-z.2.1))]
    exact ENNReal.ofReal_le_ofReal (projected_primitive_highband_kernel hw hv (hf v) hr hθ hφ hDlo hun hhan he)
  unfold physicalProjectedPrimitiveDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (3136*θ/(z.1-z.2.1))*ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      exact setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(3136*θ/(z.1-z.2.1))=(3136*θ)*(z.1-z.2.1) := by
        field_simp [hr.ne']
      rw [he,ENNReal.ofReal_mul (by positivity : 0≤3136*θ)]
      rfl

lemma physicalProjectedPrimitive_near {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {X V : ℝ→Vec} (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ)
    (hsmall : θ≤φ) (hr : 0<B.rmin) (hDlo : φ^2/2≤B.Dmin)
    (hDhi : B.Dmax≤8*φ^2) (hd : B.dmax≤8*θ^2)
    (hband : ∀t∈J,w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*C*p^3*θ^2))
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻z : ConeCoordinate,g z.1*physicalProjectedPrimitiveDensity s X V B w z
      ∂physicalBinMeasure V B J)≤
    (∫⁻t in J,g t)*ENNReal.ofReal (154140672*C*(p*θ)^3*φ^2*B.rmax*(B.rmax-B.rmin)) := by
  by_cases hwidth : B.rmin≤B.rmax
  · have hb := physicalBin_radial_density_near hV B hJ hC hp hθ hφ.le (hr.le.trans hwidth) hDhi hdensity hg
    calc
      _ ≤ ∫⁻z : ConeCoordinate,ENNReal.ofReal (3136*θ)*
          (g z.1*ENNReal.ofReal (z.1-z.2.1)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
        have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
        have hk := physicalProjectedPrimitiveDensity_bound (X:=X) (s:=s) (z:=z) hw (hband z.1 hz.1)
          (hr.trans_le hz.2.2.1.1) hθ hφ hsmall hd (hDlo.trans hz.2.2.2.2.1)
          (hz.2.2.2.2.2.trans hDhi) (fun v=>hs.nonnegative _ hzT _)
        convert mul_le_mul' (a:=g z.1) (b:=g z.1) le_rfl hk using 1; ac_rfl
      _ = ENNReal.ofReal (3136*θ)*
          (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
            ∂physicalBinMeasure V B J) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (3136*θ)*((∫⁻t in J,g t)*
          ENNReal.ofReal (49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin))) := mul_le_mul' le_rfl hb
      _ = _ := by
        have he : 154140672*C*(p*θ)^3*φ^2*B.rmax*(B.rmax-B.rmin)=
            (3136*θ)*(49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)) := by ring
        rw [he,ENNReal.ofReal_mul (by positivity : 0≤3136*θ)]
        ac_rfl
  · have he : physicalBinBase V B J=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hwidth (hz.2.2.1.1.trans hz.2.2.1.2)
    simp only [physicalBinMeasure,he,Measure.restrict_empty,lintegral_zero_measure]
    exact bot_le

lemma Admissible.projected_primitive_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(X V : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) (w p θ φ : ℝ),
      Measurable V → MeasurableSet J → J⊆Icc 0 T →
      0<w → 0≤p → 0≤θ → 0<φ → θ≤φ → 0<B.rmin →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.dmax≤8*θ^2 → B.qmax≤p →
      (∀t∈J,w/16≤‖V t‖) → ∀g : ℝ→ℝ≥0∞,Measurable g →
      (∫⁻z : ConeCoordinate,g z.1*physicalProjectedPrimitiveDensity s X V B w z
        ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,g t)*ENNReal.ofReal (C*(p*θ)^3*φ^2*B.rmax*(B.rmax-B.rmin)) := by
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨154140672*C,by positivity,?_⟩
  intro s T F hs h0 X V B J w p θ φ hV hJ hJT hw hp hθ hφ hsmall hr hDlo hDhi hd hq hband g hg
  apply physicalProjectedPrimitive_near hs hV B hJ hJT hw hC hp hθ hφ hsmall hr hDlo hDhi hd hband _ hg
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma selected_multiplier_support_congr (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H G' H' : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ))
    (hG' : EqOn G' H' (tsupport ψ)) :
    selectedMultiplierForce s α zX T Q ψ G=selectedMultiplierForce s α zX T Q ψ H ∧
    selectedMultiplierCosts s α zX T Q ψ G G'=selectedMultiplierCosts s α zX T Q ψ H H' := by
  constructor <;> funext p
  · by_cases ht : labelReceiverTime α zX T p∈tsupport ψ
    · simp only [selectedMultiplierForce,hG ht]
    · have hz := image_eq_zero_of_notMem_tsupport ht
      simp only [selectedMultiplierForce,selectedLabelSignedForce,labelWeight,hz,zero_mul,zero_smul,map_zero]
  · by_cases ht : labelReceiverTime α zX T p∈tsupport ψ
    · simp only [selectedMultiplierCosts,hG ht,hG' ht]
    · have hz := image_eq_zero_of_notMem_tsupport ht
      have hdz : deriv ψ (labelReceiverTime α zX T p)=0 := by
        by_contra hn
        exact ht (support_deriv_subset hn)
      simp only [selectedMultiplierCosts,selectedLabelCosts,labelWeight,hz,hdz,zero_mul,zero_smul,map_zero,add_zero]

lemma selected_initial_support_congr (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ)) :
    selectedInitialKernel α zX T f Q ψ G=selectedInitialKernel α zX T f Q ψ H := by
  funext z
  by_cases hz : z∈initialPuncturedCone α zX T
  · simp only [selectedInitialKernel,indicator_of_mem hz]
    by_cases ht : branchTime α zX z T 0∈tsupport ψ
    · rw [hG ht]
    · simp only [image_eq_zero_of_notMem_tsupport ht,mul_zero,zero_mul,zero_smul]
  · simp only [selectedInitialKernel,indicator_of_notMem hz]

lemma PhaseFlowOn.selected_angular_fubini {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (hw : 0<w)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal}
    (hψ : LipschitzWith L ψ) (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    (hS : tsupport ψ⊆Icc 0 T) (hband : ∀t∈tsupport ψ,w/16≤‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    let G' := fun t=>angularDerivativeCLM w (F.flow zX t).2
      (lorentzField s.E s.B (t,F.flow zX t)).2
    (∫σ : ℝ,∫z : Phase,selectedMultiplierForce s F.flow zX T Q ψ G (σ,z)) =
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ G z)+
      ∫σ : ℝ,∫z : Phase,selectedMultiplierCosts s F.flow zX T Q ψ G G' (σ,z) := by
  dsimp only
  obtain ⟨hW,hW',hd⟩ := F.prefixAngular_regular hs hT hw zX
  have he := F.selected_multiplier_fubini hs hT zX Q hψ hψb hψT hW hW' hd
  have hG : EqOn (prefixAngularMultiplier s F.flow T w hw zX)
      (fun t=>angularMultiplierCLM w (F.flow zX t).2) (tsupport ψ) :=
    fun t ht=>(prefixAngular_highband hw zX (hS ht) (hband t ht)).1
  have hG' : EqOn (prefixAngularRate s F.flow T w hw zX)
      (fun t=>angularDerivativeCLM w (F.flow zX t).2
        (lorentzField s.E s.B (t,F.flow zX t)).2) (tsupport ψ) :=
    fun t ht=>(prefixAngular_highband hw zX (hS ht) (hband t ht)).2
  obtain ⟨eF,eC⟩ := selected_multiplier_support_congr s F.flow zX T Q ψ hG hG'
  rw [eF,eC,selected_initial_support_congr F.flow zX T (fun z=>s.f (0,z)) Q ψ hG] at he
  exact he

lemma directionWeight_tsupport {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    tsupport (directionWeight a b ℓ)⊆Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have he : directionWeight a b ℓ t=0 := by
    rcases not_and_or.mp hn with ht|ht
    all_goals rw [not_le] at ht
    · rw [directionWeight,clippedRamp_of_le hℓ ht.le,clippedRamp_of_le hℓ (by linarith),sub_self]
    · rw [directionWeight,clippedRamp_of_ge hℓ (by linarith),clippedRamp_of_ge hℓ (by linarith),sub_self]
  exact ht he

lemma continuousOn_angular_force {S : Set ℝ} {V K : ℝ→Vec}
    (hV : ContinuousOn V S) (hK : ContinuousOn K S) (hv : ∀t∈S,V t≠0) (w : ℝ) :
    ContinuousOn (fun t=>angularMultiplier w (V t) (K t)) S := by
  have hG : ContinuousOn (fun t=>angularMultiplierCLM w (V t)) S := by
    intro t ht
    exact (contDiffAt_angularMultiplierCLM w (hv t ht) (k:=1) (by simp)).continuousAt.comp_continuousWithinAt (hV t ht)
  simpa only [angularMultiplierCLM_apply] using hG.clm_apply hK

lemma exists_weighted_exit_of_modulus {g g' : ℝ→Vec} {a b δ ε : ℝ}
    (hab : a≤b) (hδ : 0<δ) (hε : 0<ε)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t)
    (hsmall : ∀s∈Icc a b,∀t∈Icc a b,|t-s|<ε→‖g t-g s‖<δ/4)
    (hex : δ≤‖g b-g a‖) :
    ∃ℓ : ℝ,0<ℓ ∧ 2*ℓ≤b-a ∧
      (δ/2≤‖∫t in a..b,directionWeight a b ℓ t • g' t‖) ∧
      (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 ∧
      tsupport (directionWeight a b ℓ)⊆Icc a b := by
  have hlen : ε≤b-a := by
    by_contra hn
    have hh := hsmall a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab)
      (show |b-a|<ε by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; exact lt_of_not_ge hn)
    linarith
  let ℓ := ε/2
  have hℓ : 0<ℓ := by dsimp [ℓ]; positivity
  have hsep : 2*ℓ≤b-a := by dsimp [ℓ]; linarith
  have hleft : ∀t∈Icc a (a+ℓ),‖g t-g a‖≤δ/4 := by
    intro t ht
    exact (hsmall a (left_mem_Icc.mpr hab) t
      ⟨ht.1,by dsimp [ℓ] at ht; linarith [ht.2]⟩
      (by rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]; dsimp [ℓ] at ht; linarith [ht.2])).le
  have hright : ∀t∈Icc (b-ℓ) b,‖g t-g b‖≤δ/4 := by
    intro t ht
    exact (hsmall b (right_mem_Icc.mpr hab) t
      ⟨by dsimp [ℓ] at ht; linarith [ht.1],ht.2⟩
      (by rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; dsimp [ℓ] at ht; linarith [ht.1])).le
  exact ⟨ℓ,hℓ,hsep,directionWeight_signed_exit hℓ hsep hg hg' hd hleft hright hex,
    directionWeight_total_variation hℓ hsep,directionWeight_tsupport hℓ hsep⟩

lemma IncrementBootstrap.direction_modulus {V : ℝ→Vec} {T M A P L a b δ : ℝ}
    (H : IncrementBootstrap V T M A P L) (k : ℕ) (hk : 16≤(2:ℝ)^k)
    (hJ : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    (hM : 0<M) (hA : 0<A) (hP : 0<P) (hL : 0<L) (hδ : 0<δ) :
    ∃ε : ℝ,0<ε ∧ ∀s∈Icc a b,∀t∈Icc a b,|t-s|<ε→
      ‖momentumDirection (V t)-momentumDirection (V s)‖<δ := by
  have hB : 0<(32/(2:ℝ)^k)*M*P := by positivity
  have hC : 0<(32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k) := by positivity
  refine ⟨min ((δ/(4*((32/(2:ℝ)^k)*M*P)))^2)
    (δ/(4*((32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k)))),by positivity,?_⟩
  intro s hs t ht hst
  apply (H.direction_increment k hk hJ hband hs ht).trans_lt
  convert sqrt_linear_small hB hC hδ (abs_nonneg (t-s)) hst using 1; first | rfl | ring

lemma IncrementBootstrap.exists_weighted_angular_exit {V K : ℝ→Vec}
    {T M A P L a b δ : ℝ} (H : IncrementBootstrap V T M A P L)
    (k : ℕ) (hk : 16≤(2:ℝ)^k) (hJ : Icc a b⊆Icc 0 T) (hab : a≤b)
    (hV : ContinuousOn V (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt V (K t) t)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    (hM : 0<M) (hA : 0<A) (hP : 0<P) (hL : 0<L) (hδ : 0<δ)
    (hexit : δ≤‖momentumDirection (V b)-momentumDirection (V a)‖) :
    ∃ℓ : ℝ,0<ℓ ∧ 2*ℓ≤b-a ∧
      ((2:ℝ)^k*δ/2≤‖∫t in a..b,directionWeight a b ℓ t • angularMultiplier ((2:ℝ)^k) (V t) (K t)‖) ∧
      (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 ∧
      tsupport (directionWeight a b ℓ)⊆Icc a b := by
  have hw : 0<(2:ℝ)^k := by positivity
  have hv (t : ℝ) (ht : t∈Icc a b) : V t≠0 := by
    apply norm_pos_iff.mp
    exact (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le
      (norm_momentum_of_high_band hk (hband t ht).1)
  obtain ⟨ε,hε,hsmall⟩ := H.direction_modulus k hk hJ hband hM hA hP hL
    (show 0<δ/4 by positivity)
  apply exists_weighted_exit_of_modulus (g:=fun t=>((2:ℝ)^k) • momentumDirection (V t)) hab
    (mul_pos hw hδ) hε ((continuousOn_momentumDirection hV hv).const_smul ((2:ℝ)^k))
    (continuousOn_angular_force hV hK hv _)
  · intro t ht
    convert (hasDerivAt_momentumDirection (hd t ht) (hv t (Ioo_subset_Icc_self ht))).const_smul ((2:ℝ)^k) using 1 <;>
      first | rfl | simp only [angularMultiplier,smul_smul,div_eq_mul_inv]
  · intro s hs t ht hst
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hw]
    convert mul_lt_mul_of_pos_left (hsmall s hs t ht hst) hw using 1; first | rfl | ring
  · rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left hexit hw.le



open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


def physicalMovingProjectorDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (w : ℝ) (K : ℝ→Vec) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularDerivativeCLM w (V z.1) (K z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

lemma physicalMovingProjectorDensity_bound {s : Solution} {X V K : ℝ→Vec}
    {B : ClosedConeBin} {w θ φ : ℝ} {z : ConeCoordinate}
    (hw : 0<w) (hv : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤1-dot z.2.2.1 (velocity (V z.1)))
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalMovingProjectorDensity s X V B w K z≤
      ENNReal.ofReal (39936*θ/(w*φ)*‖K z.1‖)*ENNReal.ofReal (z.1-z.2.1)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have hhan : ‖velocity (V z.1)-z.2.2.1‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le (sphere_norm _).le (by positivity)
    rw [dot_comm]
    nlinarith
  have hpoint : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularDerivativeCLM w (V z.1) (K z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖≤
      ENNReal.ofReal (39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    have hdv : 1-dot z.2.2.1 (velocity v)≤8*θ^2 := hvbin.2.1.2.trans hd
    have hun : ‖velocity v-z.2.2.1‖≤4*θ := by
      apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le (sphere_norm _).le (by positivity)
      rw [dot_comm]
      nlinarith
    have he := small_deficit_difference (sphere_norm z.2.2) hθ hφ.le hsmall
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).le hdv hun hhan
    rw [←ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))]
    apply ENNReal.ofReal_le_ofReal
    convert moving_projector_highband_kernel hw hv (hf v) hr (sphere_norm z.2.2) hθ hφ hφ1 hDlo hun he using 1; ring
  unfold physicalMovingProjectorDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      exact setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))=(39936*θ/(w*φ)*‖K z.1‖)*(z.1-z.2.1) := by
        field_simp [hr.ne']
      rw [he,ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ)*‖K z.1‖)]
      rfl

lemma physicalMovingProjector_near {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {X V K : ℝ→Vec} (hV : Measurable V) (hK : Measurable K) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ)
    (hφ1 : φ≤1) (hsmall : θ≤φ) (hr : 0<B.rmin) (hDlo : φ^2/2≤B.Dmin)
    (hDhi : B.Dmax≤8*φ^2) (hd : B.dmax≤8*θ^2)
    (hband : ∀t∈J,w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalMovingProjectorDensity s X V B w K z
      ∂physicalBinMeasure V B J)≤
    (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
      ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
  by_cases hwidth : B.rmin≤B.rmax
  · have hb := physicalBin_radial_density_near hV B hJ hC hp hθ hφ.le (hr.le.trans hwidth) hDhi hdensity hK.norm.ennreal_ofReal
    calc
      _ ≤ ∫⁻z : ConeCoordinate,ENNReal.ofReal (39936*θ/(w*φ))*
          (ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
        have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
        have hk := physicalMovingProjectorDensity_bound (X:=X) (s:=s) (z:=z) (K:=K) hw (hband z.1 hz.1)
          (hr.trans_le hz.2.2.1.1) hθ hφ hφ1 hsmall hd (hDlo.trans hz.2.2.2.2.1)
          (hz.2.2.2.2.2.trans hDhi) (fun v=>hs.nonnegative _ hzT _)
        rw [ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ))] at hk
        convert hk using 1; ac_rfl
      _ = ENNReal.ofReal (39936*θ/(w*φ))*
          (∫⁻z : ConeCoordinate,ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
            ∂physicalBinMeasure V B J) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (39936*θ/(w*φ))*((∫⁻t in J,ENNReal.ofReal ‖K t‖)*
          ENNReal.ofReal (49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin))) := mul_le_mul' le_rfl hb
      _ = _ := by
        have he : 1962934272*C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)=
            (39936*θ/(w*φ))*(49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)) := by
          field_simp; ring
        rw [he,ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ))]
        ac_rfl
  · have he : physicalBinBase V B J=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hwidth (hz.2.2.1.1.trans hz.2.2.1.2)
    simp only [physicalBinMeasure,he,Measure.restrict_empty,lintegral_zero_measure]
    exact bot_le

lemma Admissible.moving_projector_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(X V K : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) (w p θ φ : ℝ),
      Measurable V → Measurable K → MeasurableSet J → J⊆Icc 0 T →
      0<w → 0≤p → 0≤θ → 0<φ → φ≤1 → θ≤φ → 0<B.rmin →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.dmax≤8*θ^2 → B.qmax≤p →
      (∀t∈J,w/16≤‖V t‖) →
      (∫⁻z : ConeCoordinate,physicalMovingProjectorDensity s X V B w K z
        ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨1962934272*C,by positivity,?_⟩
  intro s T F hs h0 X V K B J w p θ φ hV hK hJ hJT hw hp hθ hφ hφ1 hsmall hr hDlo hDhi hd hq hband
  apply physicalMovingProjector_near hs hV hK B hJ hJT hw hC hp hθ hφ hφ1 hsmall hr hDlo hDhi hd hband
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)

lemma selected_radial_factor {x h : ℝ} (hx : 0≤x) (hh : 0≤h)
    (hsel : x*Real.sqrt h≤1) : x^3*h^2≤Real.sqrt h := by
  have hs : 0≤Real.sqrt h := Real.sqrt_nonneg h
  have hsq := Real.sq_sqrt hh
  calc
    x^3*h^2 = (x*Real.sqrt h)^3*Real.sqrt h := by
      nth_rw 1 [←hsq]
      ring
    _ ≤ 1^3*Real.sqrt h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hx hs) hsel 3) hs
    _ = _ := by norm_num

lemma selected_radial_width {x h r R : ℝ} (hx : 0≤x) (hh : 0≤h)
    (hsel : x*Real.sqrt h≤1) (_hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    x^3*R*(R-r)≤4*Real.sqrt h := by
  calc
    _ = x^3*(R*(R-r)) := by ring
    _ ≤ x^3*((2*h)*(2*h)) := mul_le_mul_of_nonneg_left
      (mul_le_mul hhi hw (sub_nonneg.mpr hwidth) (by positivity)) (by positivity)
    _ = 4*(x^3*h^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (selected_radial_factor hx hh hsel) (by norm_num)

lemma selected_projected_coefficient {C p θ φ h r R : ℝ}
    (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hh : 0≤h)
    (hsel : p*θ*Real.sqrt h≤1) (hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    C*(p*θ)^3*φ^2*R*(R-r)≤4*C*Real.sqrt h*φ^2 := by
  have h := mul_le_mul_of_nonneg_left (selected_radial_width (mul_nonneg hp hθ) hh hsel hR hwidth hhi hw)
    (mul_nonneg hC (sq_nonneg φ))
  convert h using 1 <;> first | rfl | ring

lemma selected_moving_coefficient {C p θ φ w h r R : ℝ}
    (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0≤φ) (hw₀ : 0≤w) (hh : 0≤h)
    (hsel : p*θ*Real.sqrt h≤1) (hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    C*(p*θ)^3*φ/w*R*(R-r)≤4*C*Real.sqrt h*φ/w := by
  have h := mul_le_mul_of_nonneg_left (selected_radial_width (mul_nonneg hp hθ) hh hsel hR hwidth hhi hw)
    (div_nonneg (mul_nonneg hC hφ) hw₀)
  convert h using 1 <;> first | rfl | ring

lemma radial_half_decay (n : ℕ) : Real.sqrt ((1/2:ℝ)^n)≤(3/4:ℝ)^n := by
  have hs : Real.sqrt (1/2:ℝ)≤3/4 := (Real.sqrt_le_iff).mpr (by norm_num)
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ,Real.sqrt_mul (by positivity),pow_succ]
      exact mul_le_mul ih hs (Real.sqrt_nonneg _) (by positivity)

lemma sum_radial_half_decay (N : ℕ) : ∑n∈Finset.range N,Real.sqrt ((1/2:ℝ)^n)≤4 := by
  calc
    _ ≤ ∑n∈Finset.range N,(3/4:ℝ)^n := Finset.sum_le_sum (fun n _=>radial_half_decay n)
    _ ≤ ∑'n : ℕ,(3/4:ℝ)^n := (summable_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖<1)).sum_le_tsum
      (Finset.range N) (fun n _=>by positivity)
    _ = 4 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖<1)]; norm_num

lemma sum_angular_half_decay (N : ℕ) : ∑n∈Finset.range N,(1/2:ℝ)^n≤2 := by
  calc
    _ ≤ ∑'n : ℕ,(1/2:ℝ)^n := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).sum_le_tsum
      (Finset.range N) (fun n _=>by positivity)
    _ = 2 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]; norm_num

lemma sum_selected_radial_angular (Nr Nφ : ℕ) :
    ∑i∈Finset.range Nr,∑j∈Finset.range Nφ,
      Real.sqrt ((1/2:ℝ)^i)*(1/2:ℝ)^j≤8 := by
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul]
  exact (mul_le_mul (sum_radial_half_decay Nr) (sum_angular_half_decay Nφ)
    (Finset.sum_nonneg (fun i _=>by positivity)) (by norm_num)).trans_eq (by norm_num)

end RVM

end

end OAI
