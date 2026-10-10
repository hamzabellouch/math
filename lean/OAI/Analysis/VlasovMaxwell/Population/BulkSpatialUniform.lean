import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def bulkSpatialBoundary (P M A w I : ℝ) : Set (Fin 4→ℕ) :=
  {k | k∈centralIndexSector P ∧
    (cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) ∨
      representativeSpatialTransition P M A w I k)}

lemma Admissible.bulk_spatial_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'k : Fin 4→ℕ,(bulkSpatialBoundary P M A w I).indicator
        (fun k=>representativeSpatialCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hstruct⟩ := hd.spatial_structural_uniform T₀
  obtain ⟨Ct,hCt,htrans⟩ := hd.spatial_transition_uniform T₀
  refine ⟨Cs+Ct,add_nonneg hCs hCt,?_⟩
  intro M A hM hA
  filter_upwards [htrans M A hM hA] with P htr
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource HZ
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let fs := fun k=>representativeSpatialCost s F zX w k a b
  let Qs := {k | k∈centralIndexSector P ∧ cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)}
  let Qt := {k | k∈centralIndexSector P ∧ representativeSpatialTransition P M A w I k}
  have hBs : (∑'k,Qs.indicator fs k)≤ENNReal.ofReal (Cs*B) :=
    hstruct M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  have hBt : (∑'k,Qt.indicator fs k)≤ENNReal.ofReal (Ct*B) :=
    htr hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource HZ
  change (∑'k,(bulkSpatialBoundary P M A w I).indicator fs k)≤ENNReal.ofReal ((Cs+Ct)*B)
  calc
    _≤∑'k,(Qs.indicator fs k+Qt.indicator fs k) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈bulkSpatialBoundary P M A w I
      · rw [indicator_of_mem hk]
        rcases hk.2 with h|h
        · have hh : k∈Qs := ⟨hk.1,h⟩
          rw [indicator_of_mem hh]
          exact le_add_of_nonneg_right bot_le
        · have hh : k∈Qt := ⟨hk.1,h⟩
          rw [indicator_of_mem hh]
          exact le_add_of_nonneg_left bot_le
      · rw [indicator_of_notMem hk]; exact bot_le
    _=(∑'k,Qs.indicator fs k)+(∑'k,Qt.indicator fs k) := ENNReal.tsum_add
    _≤ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Ct*B) := add_le_add hBs hBt
    _=_ := by
      have hB : 0≤B := by dsimp [B]; positivity
      rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCt hB)]
      congr 1; ring

lemma PhaseFlowOn.bulkGeometry_pointwise {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) {v : Vec}
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2)) :
    ‖partialCutoffTriangle s F.flow zX T Q (coneGeometryCutoffTangent s F.flow zX) W J (z,v)‖≤
      (650000*C*(cappedRepresentative (k 2)/cappedRepresentative (k 1)))*
        s.f (z.2.1,((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have ht := hJT hz.1
  have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans ht.2⟩
  have hf := hs.nonnegative _ hσ ((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have heq : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq ht]
    rw [heq] at hv ⊢
    have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).ne'
      (ContinuousLinearMap.id ℝ Vec)
      (f:=s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))
      (D:=1-dot z.2.2.1 (velocity (F.flow zX z.1).2))
      (l:=fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
        (cutoffGeometryTangent (z.1-z.2.1)
          ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
          (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1))
      (a:=velocity (F.flow zX z.1).2)
    have htriangle : triangleConeKernel s F.flow zX T
        (normalisedPartialCutoff F.flow zX T Q (coneGeometryCutoffTangent s F.flow zX)) (z,v)=
      (z.1-z.2.1)^2 • ((s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (F.flow zX z.1).2))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
            (cutoffGeometryTangent (z.1-z.2.1)
              ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
              (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) •
        signedPrimitive (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1) := by
      simpa only [triangleConeKernel,indicator_of_mem hp,normalisedPartialCutoff,
        coneGeometryCutoffTangent,coneCutoffRate,coneCutoffState,triangleKernelState,cutoffGeometryTangent,
        ContinuousLinearMap.id_apply] using he
    have hD : 1-dot z.2.2.1 (velocity (F.flow zX z.1).2)∈
        Icc ((cappedRepresentative (k 2))^2/2) (8*(cappedRepresentative (k 2))^2) := by
      simpa only [heq,representativeClosedBin] using hz.2.2.2.2
    have hb := unprojected_geometry_bin_cost (T:=T) hC0 hC (sphere_norm z.2.2)
      (sub_pos.mpr hp.2.2) (by simpa only [heq] using hf) (cappedRepresentative_pos _)
      (cappedRepresentative_pos _) hsmall hv.2.1 hD Q
    rw [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1]
    calc
      _≤‖triangleConeKernel s F.flow zX T
          (normalisedPartialCutoff F.flow zX T Q (coneGeometryCutoffTangent s F.flow zX)) (z,v)‖ := by
        exact ((W z.1).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hW _ hz.1) (norm_nonneg _))
      _≤_ := by rw [htriangle,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]; exact hb
  · rw [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1]
    simp only [triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero]
    exact mul_nonneg (by positivity) hf

lemma PhaseFlowOn.bulkGeometry_bin_integral {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal (650000*C)*representativeSpatialCost s F zX w k a b := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  rw [representativeSpatialCost,←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤650000*C)]
  unfold representativeCentralCost
  dsimp only
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' (measurableSet_physicalBinBase hV _ measurableSet_Icc)
  intro z hz
  unfold physicalBinDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
  intro v hv
  rw [←ENNReal.ofReal_mul (by positivity : 0≤650000*C*(cappedRepresentative (k 2)/cappedRepresentative (k 1)))]
  exact ENNReal.ofReal_le_ofReal (F.bulkGeometry_pointwise hs zX Q (Icc_subset_Icc ha hb) W hW hC0 hC k hsmall hz hv)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.bulkGeometry_spatial_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
      (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (650000*C)*(∑'k : Fin 4→ℕ,(bulkSpatialBoundary P M A w I).indicator
        (fun k=>representativeSpatialCost s F zX w k a b) k) := by
  let Q := bulkSelection P M A w I
  let R := bulkSpatialBoundary P M A w I
  let g := fun p=>ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
    (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) p‖
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hg : Measurable g :=
    (F.partialCutoffTriangle_measurable hs zX Q (F.coneGeometryCutoffTangent_continuousOn hs zX) hW measurableSet_Icc).norm.ennreal_ofReal
  have hc : ∀p,g p≠0→∃k∈R,p∈physicalBinPhaseSet
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b) := by
    intro p hp
    have hpn : partialCutoffTriangle s F.flow zX T Q (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) p≠0 := by
      intro h; apply hp; simp only [g,h,norm_zero,ENNReal.ofReal_zero]
    obtain ⟨k,hk,hr,hpk⟩ := F.bulkCutoffTriangle_support zX _ W (Icc_subset_Icc ha hb) hband hP hpn
    exact ⟨k,⟨hk,hr⟩,hpk⟩
  apply (physicalBinPhase_cover_lintegral hV measurableSet_Icc T w R hg hc).trans
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈R
  · rw [indicator_of_mem hk,indicator_of_mem hk]
    exact F.bulkGeometry_bin_integral hs hT zX Q ha hb W hW1 hC0 hC k hk.1.2.2
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,mul_zero]

lemma Admissible.bulk_geometry_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I)
        (coneGeometryCutoffTangent s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hspatial⟩ := hd.bulk_spatial_uniform T₀
  obtain ⟨Cd,hCd,hder⟩ := dyadicFactor_log_derivative_bound
  refine ⟨650000*Cd*Cs,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hspatial M A hM hA] with P hsp
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource hphysical hband HZ W hW hW1
  apply (F.bulkGeometry_spatial_sum hs.energyPrefix hT zX ha hb hband hphysical hW hW1 hCd hder).trans
  apply (mul_le_mul' le_rfl (hsp hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource HZ)).trans
  rw [←ENNReal.ofReal_mul (by positivity : 0≤650000*Cd)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

end RVM

end

end OAI
