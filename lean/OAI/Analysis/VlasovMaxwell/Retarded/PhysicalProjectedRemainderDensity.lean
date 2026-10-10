import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.PhysicalGeometryCutoffDensity

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma angularMultiplierCLM_highband_transverse {w : ℝ} {W x : Vec}
    (hw : 0<w) (hW : w/16 ≤ ‖W‖) :
    ‖angularMultiplierCLM w W x‖ ≤ 16*‖transverseProjection W x‖ := by
  have hρ : 0<‖W‖ := lt_of_lt_of_le (by positivity) hW
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hw hρ)]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hρ).mpr (by linarith)) (norm_nonneg _)

lemma signedRemainder_projected_norm {r f θ φ w : ℝ} (W K u n : Vec)
    (hr : 0<r) (hf : 0 ≤ f) (hn : ‖n‖=1) (hw : 0<w) (hW : w/16 ≤ ‖W‖)
    (hθ : 0 ≤ θ) (hφ : 0<φ) (hsmall : θ ≤ φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity W)) (hDu : 1-dot n (velocity W) ≤ 8*φ^2)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot (velocity W) u)-(1-dot n (velocity W))| ≤ 24*φ*θ) :
    ‖angularMultiplierCLM w W ((f*(1-dot n (velocity W))) •
      signedRemainder r (velocity W) u n (fderiv ℝ velocity W K))‖ ≤
      (6272*φ/r^2+1974272*θ/(w*φ)*‖K‖/r)*f := by
  have hDp : 0<1-dot n (velocity W) := cone_denom_pos W n hn
  have hratio := small_energy_ratio hθ hφ hsmall hD he
  have hpair := receiver_small_primitive_pairing W K u n hn hθ hφ hD hDu hun he
  have hK : 0 ≤ ‖K‖/q W := div_nonneg (norm_nonneg _) (q_pos W).le
  have hpairD : |dot (fderiv ℝ velocity W K) (signedPrimitive (velocity W) u n)/
      (1-dot n (velocity W))| ≤ 1928*θ*(‖K‖/q W)/φ^2 := by
    rw [abs_div,abs_of_pos hDp]
    apply (div_le_iff₀ hDp).mpr
    have hm := mul_le_mul_of_nonneg_left hD
      (by positivity : 0 ≤ 1928*θ*(‖K‖/q W)/φ^2)
    have heq : 1928*θ*(‖K‖/q W)/φ^2*(φ^2/2)=964*θ*(‖K‖/q W) := by field_simp; ring
    rw [heq] at hm
    exact hpair.trans hm
  let c : Vec := ((1-dot (velocity W) (velocity W))/(1-dot n (velocity W))) • n-velocity W
  have hcentral : ‖angularMultiplierCLM w W c‖ ≤ 128*φ := by
    exact (angularMultiplierCLM_highband_transverse hw hW).trans
      ((mul_le_mul_of_nonneg_left (receiver_bulk_transverse_bound hn hφ.le hDu) (by norm_num)).trans_eq (by ring))
  have hnormal : ‖angularMultiplierCLM w W n‖ ≤ 64*φ := by
    have hp : ‖transverseProjection W n‖ ≤ 4*φ := by
      apply (transverseProjection_normal_bound W n hn).trans
      exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
    exact (angularMultiplierCLM_highband_transverse hw hW).trans
      ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans_eq (by ring))
  have hq : w/16 ≤ q W := hW.trans (norm_lt_q _).le
  have hqK : ‖K‖/q W ≤ ‖K‖/(w/16) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hq
  rw [signedRemainder_physical_decomposition hr.ne' hDp.ne',map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(f/r^2*((1-dot (velocity W) u)/(1-dot n (velocity W)))) •
          (angularMultiplierCLM w W c)‖+
        ‖(f/r*(dot (fderiv ℝ velocity W K) (signedPrimitive (velocity W) u n)/(1-dot n (velocity W)))) •
          (angularMultiplierCLM w W n)‖ := norm_add_le _ _
    _ ≤ (f/r^2*49)*(128*φ)+(f/r*(1928*θ*(‖K‖/q W)/φ^2))*(64*φ) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hf (sq_nonneg r)),abs_of_nonneg (div_nonneg hf hr.le)]
      exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hcentral (norm_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left hpairD (by positivity)) hnormal (norm_nonneg _) (by positivity))
    _ ≤ (f/r^2*49)*(128*φ)+(f/r*(1928*θ*(‖K‖/(w/16))/φ^2))*(64*φ) := by gcongr
    _ = _ := by field_simp; ring

def physicalProjectedRemainderDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (w : ℝ) (K : ℝ→Vec) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖angularMultiplierCLM w (V z.1)
        ((s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (1-dot z.2.2.1 (velocity (V z.1)))) •
          signedRemainder (z.1-z.2.1) (velocity (V z.1)) (velocity v) z.2.2.1
            (fderiv ℝ velocity (V z.1) (K z.1)))‖

lemma physicalProjectedRemainderDensity_bound {s : Solution} {X V K : ℝ→Vec}
    {B : ClosedConeBin} {w θ φ : ℝ} {z : ConeCoordinate}
    (hw : 0<w) (hv : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤1-dot z.2.2.1 (velocity (V z.1)))
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalProjectedRemainderDensity s X V B w K z≤
      ENNReal.ofReal (6272*φ)*physicalBinDensity s X V B z.1 z.2.1 z.2.2+
      ENNReal.ofReal (1974272*θ/(w*φ)*‖K z.1‖)*ENNReal.ofReal (z.1-z.2.1)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have han : ‖velocity (V z.1)-z.2.2.1‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le (sphere_norm _).le (by positivity)
    rw [dot_comm]
    nlinarith
  have hpoint : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖angularMultiplierCLM w (V z.1)
        ((s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (1-dot z.2.2.1 (velocity (V z.1)))) •
          signedRemainder (z.1-z.2.1) (velocity (V z.1)) (velocity v) z.2.2.1
            (fderiv ℝ velocity (V z.1) (K z.1)))‖≤
      ENNReal.ofReal (6272*φ/(z.1-z.2.1)^2+1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*
        ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    have hdv : 1-dot z.2.2.1 (velocity v)≤8*θ^2 := hvbin.2.1.2.trans hd
    have hun : ‖velocity v-z.2.2.1‖≤4*θ := by
      apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le (sphere_norm _).le (by positivity)
      rw [dot_comm]
      nlinarith
    have he := small_deficit_difference (sphere_norm z.2.2) hθ hφ.le hsmall
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).le hdv hun han
    rw [←ENNReal.ofReal_mul (by positivity :
      0≤6272*φ/(z.1-z.2.1)^2+1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))]
    exact ENNReal.ofReal_le_ofReal (signedRemainder_projected_norm (V z.1) (K z.1)
      (velocity v) z.2.2.1 hr (hf v) (sphere_norm z.2.2) hw hv hθ hφ hsmall hDlo hDhi hun he)
  unfold physicalProjectedRemainderDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (6272*φ/(z.1-z.2.1)^2+1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :=
      mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hpoint)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(6272*φ/(z.1-z.2.1)^2+
          1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))=
          6272*φ+(1974272*θ/(w*φ)*‖K z.1‖)*(z.1-z.2.1) := by field_simp [hr.ne']
      rw [he,ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0≤1974272*θ/(w*φ)*‖K z.1‖),add_mul]
      rfl

lemma physicalProjectedRemainder_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V K : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {w θ φ : ℝ}
    (hw : 0<w) (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hr : 0<B.rmin) (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hband : ∀t∈J,w/16≤‖V t‖) :
    (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s X V B w K z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal (6272*φ)*(∫⁻z : ConeCoordinate,
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal (1974272*θ/(w*φ))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hb : (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s X V B w K z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,ENNReal.ofReal (6272*φ)*physicalBinDensity s X V B z.1 z.2.1 z.2.2+
        ENNReal.ofReal (1974272*θ/(w*φ))*(ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2) ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hb := physicalProjectedRemainderDensity_bound (X:=X) (K:=K) hw (hband z.1 hz.1)
      (hr.trans_le hz.2.2.1.1) hθ hφ hsmall hd (hDlo.trans hz.2.2.2.2.1)
      (hz.2.2.2.2.2.trans hDhi) (fun v=>hs.nonnegative _ hzT _)
    rw [ENNReal.ofReal_mul (by positivity : 0≤1974272*θ/(w*φ))] at hb
    convert hb using 1
    ac_rfl
  refine hb.trans_eq ?_
  rw [lintegral_add_left' (hN.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma PhaseFlowOn.projected_remainder_near_far {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hS0 : tsupport (fun z=>s.f (0,z))⊆S) (hJ : Icc a b⊆Icc 0 T)
    {C w p θ φ : ℝ} (hC : 0≤C) (hp : 0≤p)
    (hw : 0<w) (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hD : 0<B.Dmin)
    (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hband : ∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖)
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b),
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      B w (prefixMomentumForce s F.flow T zX) z
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b))≤
      ENNReal.ofReal (6272*φ)*min
        (ENNReal.ofReal (128*C*p^3*θ^2)*(volume (Icc a b)*
          ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)))
        (coneOccupation F.flow zX T s.f
          (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
            ENNReal.ofReal (B.rmin^2*B.Dmin))+
      ENNReal.ofReal (1974272*θ/(w*φ))*
        ((∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
          ENNReal.ofReal (49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin))) := by
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hb := physicalProjectedRemainder_integral_bound (X:=fun t=>(prefixFlow F.flow T zX t).1)
      hs hT hα.fst.measurable hα.snd.measurable B measurableSet_Icc hJ hw hθ hφ hsmall
      hr hd hDlo hDhi (fun t ht=>by simpa only [prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht)
      (K:=prefixMomentumForce s F.flow T zX)
  have hnear := physicalBin_density_near hα.snd.measurable B measurableSet_Icc hφ.le hDhi hdensity
  have hfar := F.physicalBin_density_far hs hT zX B hS hS0 hJ hr hD
  have hK : Measurable (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) :=
    (F.continuous_prefixMomentumForce hs hT zX).norm.measurable.ennreal_ofReal
  have hac := physicalBin_radial_density_near hα.snd.measurable B measurableSet_Icc
    hC hp hθ hφ.le hrmax hDhi hdensity hK
  exact hb.trans (add_le_add (mul_le_mul' le_rfl (le_min hnear hfar)) (mul_le_mul' le_rfl hac))

def coneReceiverJacobian (V : ℝ→Vec) (z : ConeCoordinate) : ℝ :=
  (z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1)))

def coneFoot (X : ℝ→Vec) (z : ConeCoordinate) : ℝ×Vec :=
  (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)

lemma measurable_coneFoot {X : ℝ→Vec} (hX : Measurable X) : Measurable (coneFoot X) := by
  exact (measurable_fst.comp measurable_snd).prodMk
    ((hX.comp measurable_fst).sub ((measurable_fst.sub (measurable_fst.comp measurable_snd)).smul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))

lemma measurable_coneReceiverJacobian {V : ℝ→Vec} (hV : Measurable V) :
    Measurable (coneReceiverJacobian V) := by
  exact ((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).mul
    (measurable_const.sub (continuous_dot.measurable.comp
      ((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).prodMk
        ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))

lemma PhaseFlowOn.physicalBin_spatial_budget {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
    (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2)))
    {g : ℝ×Vec→ℝ≥0∞} (hg : Measurable g) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻ z : ConeCoordinate,ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z)
      ∂physicalBinMeasure V C (Icc a b)) ≤
    ∫⁻ σ in Icc (max 0 (a-C.rmax)) (min T (b-C.rmin)),∫⁻ y : Vec,
      (arrivalAngularSet F.flow zX T k j).indicator g (σ,y) := by
  classical
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let J' := Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))
  let U := arrivalAngularSet F.flow zX T k j
  let H : Set (ℝ×Vec) := {p | p.1∈J'} ∩ U
  let G := H.indicator g
  have hU : MeasurableSet U := F.measurable_arrivalAngularSet zX k j
  have hH : MeasurableSet H := (measurableSet_Icc.preimage measurable_fst).inter hU
  have hG : Measurable G := hg.indicator hH
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  let K : ConeCoordinate→ℝ≥0∞ := fun z=>ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z)
  have hK : Measurable K := (measurable_coneReceiverJacobian hV).ennreal_ofReal.mul
    (hg.comp (measurable_coneFoot hX))
  change (∫⁻z,K z ∂physicalBinMeasure V C (Icc a b))≤_
  rw [physicalBin_integral_eq_triangle hV C measurableSet_Icc hJ hK,
    ←lintegral_retarded_triangle_parameter sphereMeasure T
      (hK.indicator (measurableSet_physicalBinBase hV C measurableSet_Icc))]
  calc
    _ ≤ ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow zX (σ+r)).2)))*
          G (σ,(F.flow zX (σ+r)).1-r • n.1) ∂volume ∂sphereMeasure := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro σ hσ
      apply lintegral_mono
      intro n
      apply setLIntegral_mono' measurableSet_Ioo
      intro r hr
      have ht : σ+r∈Icc 0 T := ⟨by linarith [hσ.1,hr.1],by linarith [hr.2]⟩
      by_cases hz : (σ+r,σ,n)∈physicalBinBase V C (Icc a b)
      · rw [indicator_of_mem hz]
        have hσJ : σ∈J' := by
          refine ⟨max_le hσ.1.le ?_,le_min hσ.2.le ?_⟩
          · linarith [hz.1.1,hz.2.2.1.2]
          · linarith [hz.1.2,hz.2.2.1.1]
        have hdom := F.arrival_polar_mem zX hσ hr n
        have htime := F.arrival_polar_time zX hσ hr n
        have hdir := F.arrival_polar_direction zX hσ hr n
        have hmem : (σ,(F.flow zX (σ+r)).1-r • n.1)∈U := by
          apply Or.inl
          refine ⟨hdom,?_⟩
          rw [hdir,arrivalVelocity,htime]
          apply hangle
          simpa only [V,prefixFlow,prefixClamp_eq ht] using hz.2.2.2.2
        rw [show G (σ,(F.flow zX (σ+r)).1-r • n.1)=
          g (σ,(F.flow zX (σ+r)).1-r • n.1) from indicator_of_mem (show (σ,(F.flow zX (σ+r)).1-r • n.1)∈H from ⟨hσJ,hmem⟩) g]
        exact le_of_eq (by simp only [K,coneReceiverJacobian,coneFoot,X,V,prefixFlow,
          prefixClamp_eq ht,add_sub_cancel_left])
      · rw [indicator_of_notMem hz]
        exact zero_le
    _ = ∫⁻σ in Ioo (0:ℝ) T,∫⁻y in ball (F.flow zX T).1 (T-σ),G (σ,y) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      exact (F.receiver_polar_lintegral (Ioo_subset_Icc_self hσ) zX
        (hG.comp (measurable_const.prodMk measurable_id))).symm
    _ ≤ ∫⁻σ in Ioo (0:ℝ) T,∫⁻y : Vec,G (σ,y) := by
      apply lintegral_mono
      intro σ
      exact setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻σ : ℝ,∫⁻y : Vec,G (σ,y) := setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [←lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro σ
      by_cases hσ : σ∈J'
      · rw [indicator_of_mem hσ]
        apply lintegral_congr
        intro y
        change G (σ,y)=U.indicator g (σ,y)
        by_cases hy : (σ,y)∈U
        · simp only [G,indicator_of_mem (show (σ,y)∈H from ⟨hσ,hy⟩),indicator_of_mem hy]
        · simp only [G,indicator_of_notMem (show (σ,y)∉H from fun h=>hy h.2),indicator_of_notMem hy]
      · rw [indicator_of_notMem hσ]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro y
        exact indicator_of_notMem (show (σ,y)∉H from fun h=>hσ h.1) g

def prefixConeMagnetic (s : Solution) (T : ℝ) (X : ℝ→Vec) (z : ConeCoordinate) : ℝ :=
  ‖prefixField s.B T (coneFoot X z)‖

lemma EnergyPrefix.measurable_prefixConeMagnetic {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X : ℝ→Vec} (hX : Measurable X) :
    Measurable (prefixConeMagnetic s T X) :=
  ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp
    (measurable_coneFoot hX)).norm

lemma PhaseFlowOn.physicalBin_magneticField {s : Solution} {T a b I φ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
    (hI : 0<I) (hD : φ^2/2≤C.Dmin)
    (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2))) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
      ∂physicalBinMeasure V C (Icc a b)) ≤
    ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
      (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j := by
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let J' := Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))
  have hclip : J'⊆Icc 0 T := fun _ h=>⟨(le_max_left _ _).trans h.1,h.2.trans (min_le_left _ _)⟩
  let g : ℝ×Vec→ℝ≥0∞ := fun p=>ENNReal.ofReal (‖prefixField s.B T p‖^2)
  have hg : Measurable g := ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.norm.pow_const 2).ennreal_ofReal
  have ho := F.physicalBin_spatial_budget hs hT zX C k j hJ hangle hg
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hsp : (∫⁻σ in J',∫⁻y : Vec,(arrivalAngularSet F.flow zX T k j).indicator g (σ,y))=
      ENNReal.ofReal I*magneticFieldBudget s F.flow zX T k
        (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j := by
    rw [magneticFieldBudget,←mul_assoc,ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hI).ne'
      ENNReal.ofReal_ne_top,one_mul]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro σ hσ
    apply lintegral_congr
    intro y
    by_cases hy : (σ,y)∈arrivalAngularSet F.flow zX T k j
    · simp only [indicator_of_mem hy,g,prefixField,prefixClamp_eq (hclip hσ)]
    · simp only [indicator_of_notMem hy]
  change (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
    ∂physicalBinMeasure V C (Icc a b))≤_
  calc
    _ ≤ ∫⁻z : ConeCoordinate,(2:ℝ≥0∞)*(ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z))
        ∂physicalBinMeasure V C (Icc a b) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable C measurableSet_Icc)] with z hz
      have hDz : φ^2≤2*(1-dot z.2.2.1 (velocity (V z.1))) := by
        linarith [hD.trans hz.2.2.2.2.1]
      have hpos : 0≤coneReceiverJacobian V z :=
        mul_nonneg (sq_nonneg _) (cone_denom_pos _ _ (sphere_norm _)).le
      rw [←ENNReal.ofReal_mul hpos]
      calc
        _ ≤ ENNReal.ofReal (2*(coneReceiverJacobian V z*‖prefixField s.B T (coneFoot X z)‖^2)) := by
          apply ENNReal.ofReal_le_ofReal
          change (z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2≤
            2*((z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1)))*prefixConeMagnetic s T X z^2)
          nlinarith [mul_le_mul_of_nonneg_left hDz (mul_nonneg (sq_nonneg (z.1-z.2.1))
            (sq_nonneg (prefixConeMagnetic s T X z)))]
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num
    _ = (2:ℝ≥0∞)*(∫⁻z : ConeCoordinate,ENNReal.ofReal (coneReceiverJacobian V z)*g (coneFoot X z)
        ∂physicalBinMeasure V C (Icc a b)) := lintegral_const_mul' _ _ (by norm_num)
    _ ≤ (2:ℝ≥0∞)*(ENNReal.ofReal I*magneticFieldBudget s F.flow zX T k
        (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j) :=
      mul_le_mul' le_rfl (ho.trans_eq hsp)
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]; norm_num; ring

lemma Admissible.uniform_actual_magnetic_Cauchy {d : Datum} (hd₀ : Admissible d) :
    ∃ C₀ : ℝ, 0≤C₀ ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀ z,s.f (0,z)=d.f₀ z) → ∀ (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
      (a b I P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z => s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<P → 0≤θ → 0≤φ → 0≤σ → 0<C.rmin → 0<C.Dmin → φ^2/2≤C.Dmin →
      C.qmax≤P → C.dmax≤8*θ^2 → C.Dmax≤8*φ^2 → C.emax≤8*σ^2 →
      (∀ D∈Icc C.Dmin C.Dmax, DyadicWindow k j (Real.sqrt (D/2))) →
      let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
      let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
      let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
      let D := ENNReal.ofReal (128*C₀*P^3*(min θ σ)^2)
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
          ENNReal.ofReal (C.rmin^2*C.Dmin)
      (∫⁻ z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1) * ENNReal.ofReal φ *
        ENNReal.ofReal (prefixConeMagnetic s T X z) * N z ∂physicalBinMeasure V C (Icc a b)) ≤
      (ENNReal.ofReal (2*I) * magneticFieldBudget s F.flow zX T k
          (max 0 (a-C.rmax)) (min T (b-C.rmin)) I j)^(1/2:ℝ) *
        (min (D^2*(volume (Icc a b)*ENNReal.ofReal (C.rmax-C.rmin)*ENNReal.ofReal (384*φ^2)))
          (D*M))^(1/2:ℝ) := by
  obtain ⟨C₀,hC₀,hbound⟩ := hd₀.uniform_physicalBinDensity_constant
  refine ⟨C₀,hC₀,?_⟩
  intro s T F hs hT h0 zX C S a b I P θ φ σ k j hS hS0 hJ hI hP hθ hφ hσ hR hD hDlow hq hd hDmax he hangle
  dsimp only
  let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
  let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
  let N : ConeCoordinate → ℝ≥0∞ := fun z => physicalBinDensity s X V C z.1 z.2.1 z.2.2
  let μ := physicalBinMeasure V C (Icc a b)
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hN : AEMeasurable N μ :=
    physicalBinDensity_aemeasurable hs hT hX hV C measurableSet_Icc hJ
  have hG := hs.measurable_prefixConeMagnetic hT hX
  have hW : AEMeasurable (fun z : ConeCoordinate => ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
      ENNReal.ofReal (prefixConeMagnetic s T X z)) μ :=
    ((measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal.mul_const (ENNReal.ofReal φ) |>.mul hG.ennreal_ofReal).aemeasurable
  apply lintegral_product_bound_two μ hW hN
  · have hfield := F.physicalBin_magneticField hs hT zX C k j hJ hI hDlow hangle
    apply le_trans _ hfield
    apply le_of_eq
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    have hg : 0≤prefixConeMagnetic s T X z := norm_nonneg _
    dsimp only
    rw [mul_pow,mul_pow,←ENNReal.ofReal_pow hr,←ENNReal.ofReal_pow hφ,
      ←ENNReal.ofReal_pow hg,←ENNReal.ofReal_mul (sq_nonneg _),
      ←ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  · apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    exact hbound s T F hs h0 X V C z.1 z.2.1 z.2.2 P θ σ
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩ hP.le hθ hσ hq hd he
  · have hmass := F.physicalBin_weighted_occupation hs hT zX C hS hS0 hJ hR.le hD.le
    have hμ : physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b) = μ := by
      unfold μ physicalBinMeasure V
      rw [physicalBinBase_prefix zX C hJ]
    rw [hμ] at hmass
    have hne : ENNReal.ofReal (C.rmin^2*C.Dmin)≠0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    apply (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top)).mpr
    rw [mul_comm]
    convert hmass using 1
    congr 1
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    simp only [N,X,V,physicalBinDensity,prefixFlow,prefixClamp_eq (hJ hz.1)]
  · exact physicalBinMeasure_volume hV C measurableSet_Icc hφ hDmax

lemma magneticFieldBudget_mono (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (k j : ℕ) (I : ℝ) {a b lo hi : ℝ} (hsub : Icc a b⊆Icc lo hi) :
    magneticFieldBudget s α zX T k a b I j ≤ magneticFieldBudget s α zX T k lo hi I j := by
  exact mul_le_mul' le_rfl (lintegral_mono_set hsub)

lemma PhaseFlowOn.physicalBin_magneticField_common {s : Solution} {T a b lo hi I φ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) (k j : ℕ) (hJ : Icc a b⊆Icc 0 T)
    (hI : 0<I) (hD : φ^2/2≤C.Dmin)
    (hangle : ∀D∈Icc C.Dmin C.Dmax,DyadicWindow k j (Real.sqrt (D/2)))
    (hsub : Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))⊆Icc lo hi) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻z : ConeCoordinate,ENNReal.ofReal ((z.1-z.2.1)^2*φ^2*prefixConeMagnetic s T X z^2)
      ∂physicalBinMeasure V C (Icc a b))≤
      ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k lo hi I j := by
  exact (F.physicalBin_magneticField hs hT zX C k j hJ hI hD hangle).trans
    (mul_le_mul' le_rfl (magneticFieldBudget_mono s F.flow zX T k j I hsub))

lemma radial_source_interval_common {T a b R : ℝ} {C : ClosedConeBin}
    (hmin : 0≤C.rmin) (hmax : C.rmax≤R) :
    Icc (max 0 (a-C.rmax)) (min T (b-C.rmin))⊆Icc (max 0 (a-R)) (min T b) := by
  intro σ hσ
  constructor
  · exact (max_le_max le_rfl (sub_le_sub_left hmax a)).trans hσ.1
  · exact hσ.2.trans (min_le_min le_rfl (by linarith))

lemma EnergyPrefix.shared_magneticFieldBudget {s : Solution} {T a b I c : ℝ}
    (hs : EnergyPrefix s T) (α : Phase→ℝ→Phase) (zX : Phase) (k : ℕ)
    (hI : 0<I) (hc : 0≤c) (hlen : b-a≤I) :
    (∑' j : ℕ,magneticFieldBudget s α zX T k (max 0 (a-c*I)) (min T b) I j)≤
      (2*(4*k+1):ℕ)*ENNReal.ofReal (1+c)*
        ENNReal.ofReal (2*(∫x : Vec,totalEnergy s (0,x))) := by
  apply hs.magneticFieldBudget_uniform α zX k (fun _ h=>⟨(le_max_left _ _).trans h.1,h.2.trans (min_le_left _ _)⟩)
    hI (by positivity)
  have hhi : min T b≤b := min_le_right _ _
  have hlo : a-c*I ≤ max 0 (a-c*I) := le_max_right _ _
  nlinarith

end RVM

end

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma projected_source_direct_bin_bound {r w p θ φ : ℝ} (n W v E B : Vec)
    (hr : 0<r) (hw : 0<w) (hW : w/16≤‖W‖) (hn : ‖n‖=1)
    (hp : 0<p) (hθ : 0<θ) (hq : p≤q v)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖angularMultiplierCLM w W (forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖≤
      (3840*φ^2/(r*p))*(goodField E B n/θ^2+‖B‖) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hprim := angularMultiplierCLM_highband_transverse
    (x:=forceSourceKernel r n (velocity W) v (fderiv ℝ velocity v (E+cross (velocity v) B))) hw hW
  have hsrc := transverse_forceSourceKernel_bound r n W v E B hr hn
  change _ ≤ (15*D)/(r*q v*d)*(goodField E B n+d*‖B‖) at hsrc
  have hc : 240*D/(r*q v)≤1920*φ^2/(r*p) := by
    calc
      240*D/(r*q v)≤240*(8*φ^2)/(r*p) := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/d≤2*(goodField E B n/θ^2) := by
    calc
      goodField E B n/d≤goodField E B n/(θ^2/2) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 16*((15*D)/(r*q v*d)*(goodField E B n+d*‖B‖)) :=
      hprim.trans (mul_le_mul_of_nonneg_left hsrc (by norm_num))
    _ = (240*D/(r*q v))*(goodField E B n/d+‖B‖) := by field_simp; ring
    _ ≤ (1920*φ^2/(r*p))*(2*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul hc _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

lemma projected_source_cutoff_bin_bound {C T r f w p θ φ : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hp : 0<p) (hθ : 0<θ) (hq : p≤q v)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hDhi : 1-dot n (velocity W)≤8*φ^2)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      (94080000*C*φ^2/(r*p))*(goodField E B n/θ^2+‖B‖)*f := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hG : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb := projected_source_cutoff_cost (T:=T) (E:=E) (B:=B) hC0 hC hn hw hW hr hf hsmall Q
  change _≤5880000*C*(f/r)*((Real.sqrt (D/2))^2/q v)*
    (goodField E B n/(Real.sqrt (d/2))^2+‖B‖) at hb
  rw [Real.sq_sqrt (by positivity : 0≤D/2),Real.sq_sqrt (by positivity : 0≤d/2)] at hb
  have hc : (D/2)/q v≤4*φ^2/p := by
    calc
      (D/2)/q v≤((8*φ^2)/2)/p := by gcongr
      _ = _ := by ring
  have hg : goodField E B n/(d/2)≤4*(goodField E B n/θ^2) := by
    calc
      goodField E B n/(d/2)≤goodField E B n/((θ^2/2)/2) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 5880000*C*(f/r)*((D/2)/q v)*(goodField E B n/(d/2)+‖B‖) := hb
    _ ≤ 5880000*C*(f/r)*(4*φ^2/p)*(4*(goodField E B n/θ^2+‖B‖)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) _ (by positivity) (by positivity)
      linarith [norm_nonneg B]
    _ = _ := by ring

lemma projected_source_combined_bin_bound {C T r f w p θ φ : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16≤‖W‖) (hr : 0<r) (hf : 0≤f)
    (hp : 0<p) (hθ : 0<θ) (hq : p≤q v)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hDhi : 1-dot n (velocity W)≤8*φ^2)
    (hsmall : 1-dot n (velocity v)≤1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖f • angularMultiplierCLM w W (forceSourceKernel r n (velocity W) v
      (fderiv ℝ velocity v (E+cross (velocity v) B)))‖+
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      ((3840+94080000*C)*φ^2/(r*p))*(goodField E B n/θ^2+‖B‖)*f := by
  have hdir := projected_source_direct_bin_bound n W v E B hr hw hW hn hp hθ hq hdlo hDhi
  have hcut := projected_source_cutoff_bin_bound (T:=T) (E:=E) (B:=B) hC0 hC hn hw hW hr hf hp hθ hq hdlo hDhi hsmall Q
  rw [norm_smul,Real.norm_of_nonneg hf]
  exact (add_le_add (mul_le_mul_of_nonneg_left hdir hf) hcut).trans_eq (by ring)

def physicalProjectedSourceDensity (s : Solution) (X V : ℝ→Vec)
    (C : ClosedConeBin) (T w : ℝ) (Q : Set (Fin 4→ℕ)) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
      let r := z.1-z.2.1
      let n := z.2.2.1
      let W := V z.1
      let y := X z.1-r • n
      let f := s.f (z.2.1,(y,v))
      let K := s.E (z.2.1,y)+cross (velocity v) (s.B (z.2.1,y))
      ENNReal.ofReal (‖f • angularMultiplierCLM w W
        (forceSourceKernel r n (velocity W) v (fderiv ℝ velocity v K))‖+
        ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (r,n,v,W) (cutoffSourceTangent K)) •
          angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖)

lemma physicalProjectedSourceDensity_bound {s : Solution} {X V : ℝ→Vec}
    {C : ClosedConeBin} {T w p θ φ c : ℝ} {z : ConeCoordinate} (Q : Set (Fin 4→ℕ))
    (hc : 0≤c) (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤c)
    (hw : 0<w) (hW : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ)
    (hq : p≤C.qmin) (hd : θ^2/2≤C.dmin)
    (hD : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hsmall : C.dmax≤1-dot z.2.2.1 (velocity (V z.1)))
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalProjectedSourceDensity s X V C T w Q z ≤
      ENNReal.ofReal (((3840+94080000*c)*φ^2/p)*(z.1-z.2.1)*
        (goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
          (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1/θ^2+
          ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖))*
        physicalBinDensity s X V C z.1 z.2.1 z.2.2 := by
  let G := goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
    (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1
  let b := ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖
  have hG : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hb : 0≤b := norm_nonneg _
  unfold physicalProjectedSourceDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2) *
        ∫⁻v in coneBinMomentumSet C z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (((3840+94080000*c)*φ^2/((z.1-z.2.1)*p))*(G/θ^2+b))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity :
        0≤((3840+94080000*c)*φ^2/((z.1-z.2.1)*p))*(G/θ^2+b))]
      exact ENNReal.ofReal_le_ofReal (projected_source_combined_bin_bound hc hcut (sphere_norm _)
        hw hW hr (hf v) hp hθ (hq.trans hv.1.1) (hd.trans hv.2.1.1) hD
        (hv.2.1.2.trans hsmall) Q)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp [hr.ne']
      rfl

lemma physicalProjectedSource_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {w p θ φ c : ℝ}
    (Q : Set (Fin 4→ℕ)) (hc : 0≤c)
    (hcut : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤c)
    (hw : 0<w) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hr : 0<B.rmin) (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin)
    (hDhi : B.Dmax≤8*φ^2) (hsmall : B.dmax≤B.Dmin)
    (hband : ∀t∈J,w/16≤‖V t‖) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal ((3840+94080000*c)*φ/p)*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*ENNReal.ofReal (prefixConeMagnetic s T X z)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hG := hs.measurable_prefixConeGood hT hX
  have hR : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal (z.1-z.2.1)) :=
    (measurable_fst.sub (measurable_fst.comp measurable_snd)).ennreal_ofReal
  have hb : (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,
        ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)+
        ENNReal.ofReal ((3840+94080000*c)*φ/p)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal φ*
          ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2)
          ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hrz : 0<z.1-z.2.1 := hr.trans_le hz.2.2.1.1
    have hb := physicalProjectedSourceDensity_bound (X:=X) (T:=T) Q hc hcut hw (hband z.1 hz.1)
      hrz hp hθ hq hdlo (hz.2.2.2.2.2.trans hDhi) (hsmall.trans hz.2.2.2.2.1)
      (fun v=>hs.nonnegative _ hzT _)
    apply hb.trans_eq
    let G := prefixConeGood s T X z
    let b := prefixConeMagnetic s T X z
    have hG0 : 0≤G := add_nonneg (norm_nonneg _) (abs_nonneg _)
    have hb0 : 0≤b := norm_nonneg _
    have heG : goodField (s.E (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1))
        (s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)) z.2.2.1=G := by
      simp [G,prefixConeGood,prefixField,prefixClamp_eq hzT]
    have heb : ‖s.B (z.2.1,X z.1-(z.1-z.2.1) • z.2.2.1)‖=b := by
      simp [b,prefixConeMagnetic,coneFoot,prefixField,prefixClamp_eq hzT]
    rw [heG,heb]
    have he : ((3840+94080000*c)*φ^2/p)*(z.1-z.2.1)*(G/θ^2+b)=
        ((3840+94080000*c)*φ^2/(p*θ^2))*((z.1-z.2.1)*G)+
          ((3840+94080000*c)*φ/p)*((z.1-z.2.1)*φ*b) := by ring
    rw [he,ENNReal.ofReal_add (by positivity) (by positivity),add_mul]
    simp only [ENNReal.ofReal_mul (by positivity : 0≤(3840+94080000*c)*φ^2/(p*θ^2)),
      ENNReal.ofReal_mul (by positivity : 0≤(3840+94080000*c)*φ/p),
      ENNReal.ofReal_mul (mul_nonneg hrz.le hφ.le),ENNReal.ofReal_mul hrz.le]
    dsimp only [G,b]
    ac_rfl
  refine hb.trans_eq ?_
  have hMG : AEMeasurable (fun z : ConeCoordinate=>
      ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*(ENNReal.ofReal (z.1-z.2.1)*
          ENNReal.ofReal (prefixConeGood s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2))
      (physicalBinMeasure V B J) := by
    simpa only [Pi.mul_apply] using (((hR.mul hG.ennreal_ofReal).aemeasurable.mul hN).const_mul
      (ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))))
  rw [lintegral_add_left' hMG,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma Admissible.projected_source_two_budget_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb c : ℝ, 0≤Cg ∧ 0≤Cb ∧ 0≤c ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (B : ClosedConeBin) (S : Set Phase) (Q : Set (Fin 4→ℕ))
      (a b I w p P θ φ σ : ℝ) (k j : ℕ), IsCompact S →
      tsupport (fun z=>s.f (0,z))⊆S → Icc a b⊆Icc 0 T →
      0<I → 0<w → 0<p → 0<P → 0<θ → 0<φ → 0≤σ → 0<B.rmin → 0<B.Dmin →
      p≤B.qmin → B.qmax≤P → θ^2/2≤B.dmin → B.dmax≤8*θ^2 →
      φ^2/2≤B.Dmin → B.Dmax≤8*φ^2 → B.emax≤8*σ^2 → B.dmax≤B.Dmin →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      (∀t∈Icc a b,w/16≤‖(prefixFlow F.flow T zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let M := coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
          ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*P^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*P^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal ((3840+94080000*c)*φ^2/(p*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*M))^(1/2:ℝ))+
        ENNReal.ofReal ((3840+94080000*c)*φ/p)*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*M))^(1/2:ℝ)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd₀.uniform_actual_bin_Cauchy
  obtain ⟨Cb,hCb,hmag⟩ := hd₀.uniform_actual_magnetic_Cauchy
  obtain ⟨c,hc,hcut⟩ := dyadicFactor_log_derivative_bound
  refine ⟨Cg,Cb,c,hCg,hCb,hc,?_⟩
  intro s T F hs hT h0 zX B S Q a b I w p P θ φ σ k j hS hS0 hJ hI hw hp hP hθ hφ hσ
    hR hD hqlo hqhi hdlo hdhi hDlo hDhi he hsmall hangle hband
  dsimp only
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hb := physicalProjectedSource_integral_bound hs hT hα.fst.measurable hα.snd.measurable B
    measurableSet_Icc hJ Q hc hcut hw hp hθ hφ hR hqlo hdlo hDhi hsmall hband
  exact hb.trans (add_le_add
    (mul_le_mul' le_rfl (hgood s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hqhi hdhi hDhi he hangle))
    (mul_le_mul' le_rfl (hmag s T F hs hT h0 zX B S a b I P θ φ σ k j hS hS0 hJ
      hI hP hθ.le hφ.le hσ hR hD hDlo hqhi hdhi hDhi he hangle)))

end RVM

end

end OAI
