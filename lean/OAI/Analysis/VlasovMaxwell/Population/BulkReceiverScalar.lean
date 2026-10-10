import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma receiver_bin_ratio {d D θ φ w qW : ℝ} (hθ : 0<θ) (hφ : 0<φ) (hw : 0<w)
    (hd : d∈Icc (θ^2/2) (8*θ^2)) (hD : D∈Icc (φ^2/2) (8*φ^2))
    (hq : w/8≤qW) :
    Real.sqrt (d/2)/(qW*(Real.sqrt (D/2))^2)≤64*(θ/(w*φ^2)) := by
  have hdt := (deficit_sqrt_representative_bounds hθ hd).2
  have hDφ := (deficit_sqrt_representative_bounds hφ hD).1
  have hlo : (w/8)*(φ/2)^2≤qW*(Real.sqrt (D/2))^2 :=
    mul_le_mul hq ((sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mpr hDφ)
      (sq_nonneg _) ((by positivity : 0≤w/8).trans hq)
  calc
    _≤(2*θ)/((w/8)*(φ/2)^2) := div_le_div₀ (by positivity) hdt (by positivity) hlo
    _=_ := by field_simp; ring

lemma unprojected_receiver_bin_cost {C T r f θ φ w : ℝ} {n v W K : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f) (hθ : 0<θ) (hφ : 0<φ) (hw : 0<w)
    (hsmall : θ≤φ/16) (hd : 1-dot n (velocity v)∈Icc (θ^2/2) (8*θ^2))
    (hD : 1-dot n (velocity W)∈Icc (φ^2/2) (8*φ^2)) (hq : w/8≤q W)
    (Q : Set (Fin 4→ℕ)) :
    r^2*‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffReceiverTangent ((1-dot n (velocity v))/(1-dot n (velocity W))) K)) •
      signedPrimitive (velocity W) (velocity v) n‖≤
      (2080000*C)*(θ/(w*φ^2))*‖K‖*r*f := by
  have hdsmall := small_bin_deficit_order hθ hφ hsmall hd hD
  have hb := unprojected_receiver_cutoff_cost (T:=T) (K:=K) hC0 hC hn hr hf hdsmall Q
  dsimp only at hb
  calc
    _≤r^2*(32500*C*f*Real.sqrt ((1-dot n (velocity v))/2)*‖K‖/
      (r*q W*(Real.sqrt ((1-dot n (velocity W))/2))^2)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _=(32500*C*r*f*‖K‖)*(Real.sqrt ((1-dot n (velocity v))/2)/
      (q W*(Real.sqrt ((1-dot n (velocity W))/2))^2)) := by field_simp
    _≤(32500*C*r*f*‖K‖)*(64*(θ/(w*φ^2))) :=
      mul_le_mul_of_nonneg_left (receiver_bin_ratio hθ hφ hw hd hD hq) (by positivity)
    _=_ := by ring

end RVM

end

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.bulkReceiver_pointwise {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) {v : Vec}
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2)) :
    ‖partialCutoffTriangle s F.flow zX T Q (coneReceiverCutoffTangent s F.flow zX) W J (z,v)‖≤
      (2080000*C)*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2))*
        ‖prefixMomentumForce s F.flow T zX z.1‖*(z.1-z.2.1)*
          s.f (z.2.1,((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have ht := hJT hz.1
  have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans ht.2⟩
  have hf := hs.nonnegative _ hσ ((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have heq : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq ht]
    have hK : prefixMomentumForce s F.flow T zX z.1=
        (lorentzField s.E s.B (z.1,F.flow zX z.1)).2 := by
      simp only [prefixMomentumForce,heq,prefixClamp_eq ht]
    have hD : 1-dot z.2.2.1 (velocity (F.flow zX z.1).2)∈
        Icc ((cappedRepresentative (k 2))^2/2) (8*(cappedRepresentative (k 2))^2) := by
      simpa only [heq,representativeClosedBin] using hz.2.2.2.2
    have hq : w/8≤q (F.flow zX z.1).2 := by
      simpa only [heq,representativeClosedBin] using hz.2.2.2.1.1
    rw [heq] at hv ⊢
    rw [hK]
    apply (partialCutoffTriangle_norm_le_polar Q (coneReceiverCutoffTangent s F.flow zX)
      W hz.1 hp (hW _ hz.1)).trans
    simpa only [coneCutoffState,triangleKernelState,coneReceiverCutoffTangent,coneCutoffRate,
      cutoffReceiverTangent] using unprojected_receiver_bin_cost (T:=T) hC0 hC (sphere_norm z.2.2)
        (sub_pos.mpr hp.2.2) (by simpa only [heq] using hf) hθ hφ hw hsmall hv.2.1 hD hq Q
  · rw [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1]
    simp only [triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero]
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    positivity

lemma PhaseFlowOn.bulkReceiver_bin_integral {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal (2080000*C)*representativeReceiverCost s F zX w k a b
        (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  rw [representativeReceiverCost,←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤2080000*C)]
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' (measurableSet_physicalBinBase hV _ measurableSet_Icc)
  intro z hz
  unfold physicalBinDensity
  rw [←mul_assoc,←lintegral_const_mul' _ _
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))]
  apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
  intro v hv
  have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
  have hn : 0≤(2080000*C)*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2)) := by positivity
  simp only [←mul_assoc]
  rw [←ENNReal.ofReal_mul hn,←ENNReal.ofReal_mul (mul_nonneg hn (norm_nonneg _)),
    ←ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hn (norm_nonneg _)) hr)]
  exact ENNReal.ofReal_le_ofReal (F.bulkReceiver_pointwise hs zX hw Q (Icc_subset_Icc ha hb) W hW hC0 hC k hsmall hz hv)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.bulkReceiver_selected_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
      (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (2080000*C)*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k) := by
  let Q := bulkSelection P M A w I
  let R := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  let g := fun p=>ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
    (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p‖
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hg : Measurable g :=
    (F.partialCutoffTriangle_measurable hs zX Q (F.coneReceiverCutoffTangent_continuousOn hs zX) hW measurableSet_Icc).norm.ennreal_ofReal
  have hc : ∀p,g p≠0→∃k∈R,p∈physicalBinPhaseSet
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b) := by
    intro p hp
    have hpn : partialCutoffTriangle s F.flow zX T Q (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p≠0 := by
      intro h; apply hp; simp only [g,h,norm_zero,ENNReal.ofReal_zero]
    obtain ⟨ht,htT,hσ,hbandPrefix,hv,hd⟩ := F.partialCutoffTriangle_physical_nonzero
      zX Q _ W (Icc_subset_Icc ha hb) hband hP hpn
    have hr : 0<p.1.1-p.1.2.1 := sub_pos.mpr hσ.2
    have hrT : p.1.1-p.1.2.1≤ max 1 T := by linarith [hσ.1,le_max_right (1:ℝ) T]
    obtain ⟨bin,hbin,_,_,hpositive,_,_⟩ := stateCutoff_partial_boundary
      (z:=(p.1.1-p.1.2.1,p.1.2.2.1,p.2,(prefixFlow F.flow T zX p.1.1).2))
      Q hr hrT (sphere_norm p.1.2.2) _ hd
    exact ⟨bin,⟨bulkSelection_positive_smallSector (sphere_norm p.1.2.2) hv hbin hpositive,hbin.2⟩,
      physicalCutoff_positive_closedBin (V:=fun time=>(prefixFlow F.flow T zX time).2)
        (n:=p.1.2.2) ht ⟨hσ.1,hσ.2.le⟩ hbandPrefix hpositive⟩
  apply (physicalBinPhase_cover_lintegral hV measurableSet_Icc T w R hg hc).trans
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈R
  · rw [indicator_of_mem hk,indicator_of_mem hk]
    exact F.bulkReceiver_bin_integral hs hT zX hw Q ha hb W hW1 hC0 hC k hk.1.2.2
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,mul_zero]

lemma Admissible.bulk_receiver_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 1≤w → w≤P → 0<I → I≤(w/P)^2 →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
        (coneReceiverCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cs,hCs,hreceiver⟩ := hd.selected_receiver_uniform T₀
  obtain ⟨Cd,hCd,hder⟩ := dyadicFactor_log_derivative_bound
  refine ⟨2080000*Cd*Cs,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hreceiver M A hM hA] with P hr
  intro s T F hs hT hTT zX a b I w ha hb hw hwP hI hIP hphysical hband W hW hW1
  have hg := (F.continuous_prefixMomentumForce hs.energyPrefix hT zX).norm.measurable.ennreal_ofReal
  have hbnd := hr s T F hs hT hTT zX a b I w
    (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) ha hb hw hwP hI hIP hg
    (fun _=>ENNReal.ofReal_ne_top)
  apply (F.bulkReceiver_selected_sum hs.energyPrefix hT zX (zero_lt_one.trans_le hw)
    ha hb hband hphysical hW hW1 hCd hder).trans
  apply (mul_le_mul' le_rfl hbnd).trans
  rw [←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤2080000*Cd)]
  exact le_of_eq (by congr 2; ring)

end RVM

end

end OAI
