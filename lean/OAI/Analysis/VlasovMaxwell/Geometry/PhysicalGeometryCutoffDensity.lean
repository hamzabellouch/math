import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.CutoffSourceTangent

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

lemma projected_geometry_cutoff_bin_cost {A T r f w θ φ : ℝ} {n v W : Vec}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hn : ‖n‖=1) (hw : 0<w) (hW : w/16 ≤ ‖W‖) (hr : 0<r) (hf : 0 ≤ f)
    (hθ : 0<θ) (_hφ : 0 ≤ φ) (hd : θ^2/2 ≤ 1-dot n (velocity v))
    (hD : 1-dot n (velocity W) ≤ 8*φ^2)
    (hsmall : 1-dot n (velocity v) ≤ 1-dot n (velocity W)) (Q : Set (Fin 4→ℕ)) :
    ‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity W)))
          (velocity W) (velocity v) n)) •
      angularMultiplierCLM w W (signedPrimitive (velocity W) (velocity v) n)‖ ≤
      (78400000*A*φ^2/θ/r^2)*f := by
  let θa := Real.sqrt ((1-dot n (velocity v))/2)
  let φa := Real.sqrt ((1-dot n (velocity W))/2)
  have hθa : 0<θa := Real.sqrt_pos.mpr (div_pos (cone_denom_pos v n hn) (by norm_num))
  have hφa : 0 ≤ φa := Real.sqrt_nonneg _
  have hθl : θ/2 ≤ θa := by
    apply (Real.le_sqrt (by positivity) (div_nonneg (cone_denom_pos v n hn).le (by norm_num))).mpr
    nlinarith
  have hφl : φa^2 ≤ 4*φ^2 := by
    dsimp [φa]
    rw [Real.sq_sqrt (div_nonneg (cone_denom_pos W n hn).le (by norm_num))]
    linarith
  have hb := projected_geometry_cutoff_cost (T:=T) hA0 hA hn hw hW hr hf hsmall Q
  change _ ≤ 9800000*A*f*φa^2/(r^2*θa) at hb
  calc
    _ ≤ 9800000*A*f*φa^2/(r^2*θa) := hb
    _ ≤ 9800000*A*f*(4*φ^2)/(r^2*(θ/2)) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
    _ = _ := by field_simp; ring

def physicalGeometryCutoffDensity (s : Solution) (X V : ℝ→Vec)
    (B : ClosedConeBin) (T w : ℝ) (Q : Set (Fin 4→ℕ)) (z : ConeCoordinate) : ℝ≥0∞ :=
  ENNReal.ofReal ((z.1-z.2.1)^2) *
    ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffGeometryTangent (z.1-z.2.1)
            ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1))))
            (velocity (V z.1)) (velocity v) z.2.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖

lemma physicalGeometryCutoffDensity_bound {s : Solution} {X V : ℝ→Vec}
    {B : ClosedConeBin} {A T w θ φ : ℝ} {z : ConeCoordinate}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hw : 0<w) (hv : w/16 ≤ ‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0<θ) (hφ : 0 ≤ φ) (hd : θ^2/2 ≤ B.dmin)
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1)) ≤ 8*φ^2)
    (hsmall : B.dmax ≤ 1-dot z.2.2.1 (velocity (V z.1)))
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))
    (Q : Set (Fin 4→ℕ)) :
    physicalGeometryCutoffDensity s X V B T w Q z ≤
      ENNReal.ofReal (78400000*A*φ^2/θ)*physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have hp : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (V z.1)))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
        fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,V z.1)
          (cutoffGeometryTangent (z.1-z.2.1)
            ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (V z.1))))
            (velocity (V z.1)) (velocity v) z.2.2.1)) •
        angularMultiplierCLM w (V z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖ ≤
      ENNReal.ofReal (78400000*A*φ^2/θ/(z.1-z.2.1)^2)*
        ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 78400000*A*φ^2/θ/(z.1-z.2.1)^2)]
    exact ENNReal.ofReal_le_ofReal (projected_geometry_cutoff_bin_cost hA0 hA (sphere_norm z.2.2)
      hw hv hr (hf v) hθ hφ (hd.trans hvbin.2.1.1) hDhi (hvbin.2.1.2.trans hsmall) Q)
  unfold physicalGeometryCutoffDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)* ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        ENNReal.ofReal (78400000*A*φ^2/θ/(z.1-z.2.1)^2)*
          ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :=
      mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hp)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(78400000*A*φ^2/θ/(z.1-z.2.1)^2)=78400000*A*φ^2/θ := by field_simp [hr.ne']
      rw [he]
      rfl

lemma physicalGeometryCutoff_integral_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {X V : ℝ→Vec} (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {A w θ φ : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hw : 0<w) (hθ : 0<θ) (hφ : 0 ≤ φ) (hsmall : B.dmax ≤ B.Dmin)
    (hr : 0<B.rmin) (hd : θ^2/2 ≤ B.dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hband : ∀t∈J,w/16 ≤ ‖V t‖) (Q : Set (Fin 4→ℕ)) :
    (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s X V B T w Q z ∂physicalBinMeasure V B J) ≤
      ENNReal.ofReal (78400000*A*φ^2/θ)*∫⁻z : ConeCoordinate,
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
  have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
  exact physicalGeometryCutoffDensity_bound hA0 hA hw (hband z.1 hz.1)
    (hr.trans_le hz.2.2.1.1) hθ hφ hd (hz.2.2.2.2.2.trans hDhi)
    (hsmall.trans hz.2.2.2.2.1) (fun v=>hs.nonnegative _ hzT _) Q

lemma physicalBin_density_near {s : Solution} {X V : ℝ→Vec}
    (hV : Measurable V) (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {C p θ φ : ℝ} (hφ : 0 ≤ φ) (hD : B.Dmax ≤ 8*φ^2)
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) ≤
      ENNReal.ofReal (128*C*p^3*θ^2)*
        (volume J*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
  have hb : (∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) ≤
      ∫⁻_z : ConeCoordinate,ENNReal.ofReal (128*C*p^3*θ^2) ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    exact hdensity z hz
  refine hb.trans ?_
  rw [lintegral_const]
  exact mul_le_mul' le_rfl (physicalBinMeasure_volume hV B hJ hφ hD)

lemma PhaseFlowOn.physicalBin_density_far {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hS0 : tsupport (fun z=>s.f (0,z))⊆S) (hJ : Icc a b⊆Icc 0 T)
    (hr : 0<C.rmin) (hD : 0<C.Dmin) :
    (∫⁻z : ConeCoordinate,physicalBinDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      C z.1 z.2.1 z.2.2 ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b)) ≤
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
      ENNReal.ofReal (C.rmin^2*C.Dmin) := by
  have hmass := F.physicalBin_weighted_occupation hs hT zX C hS hS0 hJ hr.le hD.le
  have hμ : physicalBinMeasure (fun t=>(F.flow zX t).2) C (Icc a b)=
      physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b) := by
    unfold physicalBinMeasure
    rw [physicalBinBase_prefix zX C hJ]
  rw [hμ] at hmass
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have he : (∫⁻z : ConeCoordinate,physicalBinDensity s
      (fun t=>(F.flow zX t).1) (fun t=>(F.flow zX t).2) C z.1 z.2.1 z.2.2
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b))=
      ∫⁻z : ConeCoordinate,physicalBinDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      C z.1 z.2.1 z.2.2 ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable C measurableSet_Icc)] with z hz
    simp only [physicalBinDensity,prefixFlow,prefixClamp_eq (hJ hz.1)]
  rw [he] at hmass
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr (by positivity)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  simpa only [mul_comm] using hmass

lemma PhaseFlowOn.geometry_cutoff_near_far {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hS0 : tsupport (fun z=>s.f (0,z))⊆S) (hJ : Icc a b⊆Icc 0 T)
    {A C w p θ φ : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x| ≤ A)
    (hw : 0<w) (hθ : 0<θ) (hφ : 0 ≤ φ) (hsmall : B.dmax ≤ B.Dmin)
    (hr : 0<B.rmin) (hD : 0<B.Dmin) (hd : θ^2/2 ≤ B.dmin) (hDhi : B.Dmax ≤ 8*φ^2)
    (hband : ∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) (Q : Set (Fin 4→ℕ))
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b),
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      B T w Q z ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B (Icc a b)) ≤
    min (ENNReal.ofReal (78400000*A*φ^2/θ)*ENNReal.ofReal (128*C*p^3*θ^2)*
          (volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)))
        (ENNReal.ofReal (78400000*A*φ^2/θ)*
          (coneOccupation F.flow zX T s.f
            (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
              ENNReal.ofReal (B.rmin^2*B.Dmin))) := by
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hb := physicalGeometryCutoff_integral_bound (X := fun t => (prefixFlow F.flow T zX t).1)
    hs hα.snd.measurable B measurableSet_Icc hJ
    hA0 hA hw hθ hφ hsmall hr hd hDhi
    (fun t ht=>by simpa only [prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht) Q
  refine le_min (hb.trans ?_) (hb.trans ?_)
  · exact (mul_le_mul' le_rfl
      (physicalBin_density_near hα.snd.measurable B measurableSet_Icc hφ hDhi hdensity)).trans_eq
        (mul_assoc _ _ _).symm
  · exact mul_le_mul' le_rfl (F.physicalBin_density_far hs hT zX B hS hS0 hJ hr hD)

lemma PhaseFlowOn.closedEulerian_stable_budget {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax) (hrad : B.rmax ≤ len)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hI : 0 < I) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (40*B.rmax)/ENNReal.ofReal (p/256)*
        (ENNReal.ofReal (∫ x : Vec,totalEnergy s (0,x))+
          ENNReal.ofReal I/ENNReal.ofReal len*jointEnergyBudget s F.flow zX T 4
            (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf)) := by
  have hp0 : 0 < p := by rw [hp]; positivity
  have ho := F.small_closed_bin_refined_stable hs hT zX B hS np nf hp hφeq
    ha hb hlen hM hA hP hL hm hφ hφ1 hconst hstable hqmin hqmax hmq hmw
    hr hrmax hrad hd hDlo hDhi hw HX HZ hI
  have hbnd := occupation_divide_cell
    (p:=ENNReal.ofReal (p/256)) (len:=ENNReal.ofReal len)
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr hlen).ne' ENNReal.ofReal_ne_top ho
  have he := F.closedBinEulerian_occupation_le (c:=max 0 (a-B.rmax)) (d:=min T (b-B.rmin))
    hs hT zX B hS (Icc_subset_Icc ha hb)
    (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  refine he.trans ((show labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) from ?_).trans hbnd)
  unfold labelOccupation
  apply lintegral_mono
  intro z
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro u ⟨hz,hu,t,ht,hbin⟩
  exact ⟨hz,⟨(le_max_left _ _).trans hu.1,hu.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩

end RVM

end

end OAI
