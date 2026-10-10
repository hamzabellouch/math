import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.GoodCrossings
import OAI.Analysis.VlasovMaxwell.Population.ReceiverWeights

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma deficit_sqrt_representative_bounds {d θ : ℝ} (hθ : 0<θ)
    (hd : d∈Icc (θ^2/2) (8*θ^2)) :
    θ/2≤Real.sqrt (d/2) ∧ Real.sqrt (d/2)≤2*θ := by
  have hd0 : 0≤d := by nlinarith [sq_nonneg θ,hd.1]
  constructor
  · apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith [hd.1]
  · apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith [hd.2]⟩

lemma small_bin_deficit_order {d D θ φ : ℝ} (hθ : 0<θ) (hφ : 0<φ)
    (hsmall : θ≤φ/16) (hd : d∈Icc (θ^2/2) (8*θ^2))
    (hD : D∈Icc (φ^2/2) (8*φ^2)) : d≤D := by
  have hh := (sq_le_sq₀ hθ.le (by positivity : 0≤φ/16)).mpr hsmall
  nlinarith [hd.2,hD.1]

lemma unprojected_geometry_bin_cost {C T r f θ φ : ℝ} {n v W : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f) (hθ : 0<θ) (hφ : 0<φ)
    (hsmall : θ≤φ/16) (hd : 1-dot n (velocity v)∈Icc (θ^2/2) (8*θ^2))
    (hD : 1-dot n (velocity W)∈Icc (φ^2/2) (8*φ^2)) (Q : Set (Fin 4→ℕ)) :
    r^2*‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffGeometryTangent r ((1-dot n (velocity v))/(1-dot n (velocity W)))
          (velocity W) (velocity v) n)) •
      signedPrimitive (velocity W) (velocity v) n‖ ≤
      650000*C*(φ/θ)*f := by
  have hdsmall := small_bin_deficit_order hθ hφ hsmall hd hD
  have ht := (deficit_sqrt_representative_bounds hθ hd).1
  have hp := (deficit_sqrt_representative_bounds hφ hD).2
  have hta : 0<Real.sqrt ((1-dot n (velocity v))/2) := Real.sqrt_pos.mpr (by nlinarith [hd.1,sq_pos_of_pos hθ])
  have hb := unprojected_geometry_cutoff_cost (T:=T) hC0 hC hn hr hf hdsmall Q
  dsimp only at hb
  calc
    _ ≤ r^2*(162500*C*f*Real.sqrt ((1-dot n (velocity W))/2)/
      (r^2*Real.sqrt ((1-dot n (velocity v))/2))) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = 162500*C*f*(Real.sqrt ((1-dot n (velocity W))/2)/Real.sqrt ((1-dot n (velocity v))/2)) := by field_simp
    _ ≤ 162500*C*f*((2*φ)/(θ/2)) := mul_le_mul_of_nonneg_left
      (div_le_div₀ (by positivity) hp (by positivity) ht) (by positivity)
    _ = _ := by field_simp; ring

lemma unprojected_source_bin_cost {C T r f p θ φ : ℝ} {n v W E B : Vec}
    (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ)
    (hpv : p/128≤q v)
    (hsmall : θ≤φ/16) (hd : 1-dot n (velocity v)∈Icc (θ^2/2) (8*θ^2))
    (hD : 1-dot n (velocity W)∈Icc (φ^2/2) (8*φ^2)) (Q : Set (Fin 4→ℕ)) :
    r^2*‖(f*(1-dot n (velocity W))/(r*(1-dot n (velocity v)))*
      fderiv ℝ (stateCutoff T Q) (r,n,v,W)
        (cutoffSourceTangent (E+cross (velocity v) B))) •
      signedPrimitive (velocity W) (velocity v) n‖ ≤
      99840000*C*r*(φ/(p*θ^2)*goodField E B n+φ/p*‖B‖)*f := by
  have hGood : 0≤goodField E B n := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hsmall' := small_bin_deficit_order hθ hφ hsmall hd hD
  have ht := (deficit_sqrt_representative_bounds hθ hd).1
  have hφ' := (deficit_sqrt_representative_bounds hφ hD).2
  have hθa : 0<Real.sqrt ((1-dot n (velocity v))/2) :=
    Real.sqrt_pos.mpr (by nlinarith [hd.1,sq_pos_of_pos hθ])
  have hratio : Real.sqrt ((1-dot n (velocity W))/2)/q v≤256*φ/p := by
    calc
      _ ≤ (2*φ)/(p/128) := div_le_div₀ (by positivity) hφ' (by positivity) hpv
    _ = _ := by field_simp; norm_num
  have hden : θ^2/4 ≤ (Real.sqrt ((1-dot n (velocity v))/2))^2 := by
    nlinarith [(sq_le_sq₀ (by positivity : 0≤θ/2) hθa.le).mpr ht]
  have hg : goodField E B n/(Real.sqrt ((1-dot n (velocity v))/2))^2 ≤
      4*(goodField E B n/θ^2) := by
    calc
      _ ≤ goodField E B n/(θ^2/4) := div_le_div_of_nonneg_left hGood (by positivity) hden
    _ = _ := by field_simp
  have hsum : goodField E B n/(Real.sqrt ((1-dot n (velocity v))/2))^2+‖B‖ ≤
      4*(goodField E B n/θ^2+‖B‖) := by nlinarith [norm_nonneg B]
  have hb := unprojected_source_cutoff_cost (T:=T) (E:=E) (B:=B) hC0 hC hn hr hf hsmall' Q
  dsimp only at hb
  calc
    _ ≤ r^2*(97500*C*(f/r)*
      (Real.sqrt ((1-dot n (velocity W))/2)/q v)*
        (goodField E B n/(Real.sqrt ((1-dot n (velocity v))/2))^2+‖B‖)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ r^2*(97500*C*(f/r)*(256*φ/p)*(4*(goodField E B n/θ^2+‖B‖))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hsum (by positivity) (by positivity)
    _ = _ := by field_simp; ring



section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma trianglePartial_eq_polar {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState)
    {p : TrianglePhase} (hp : p∈trianglePhaseDomain T) :
    triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p=
      (p.1.1-p.1.2.1)^2 •
        ((s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2)*
          (1-dot p.1.2.2.1 (velocity (α zX p.1.1).2))/
          ((p.1.1-p.1.2.1)*(1-dot p.1.2.2.1 (velocity p.2)))*
          fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX (triangleKernelState α zX p))
            (H (triangleKernelState α zX p))) •
          signedPrimitive (velocity (α zX p.1.1).2) (velocity p.2) p.1.2.2.1) := by
  have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
    (cone_denom_pos p.2 p.1.2.2.1 (sphere_norm p.1.2.2)).ne'
    (ContinuousLinearMap.id ℝ Vec)
    (f:=s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2))
    (D:=1-dot p.1.2.2.1 (velocity (α zX p.1.1).2))
    (l:=fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX (triangleKernelState α zX p))
      (H (triangleKernelState α zX p))) (a:=velocity (α zX p.1.1).2)
  simpa only [triangleConeKernel,indicator_of_mem hp,normalisedPartialCutoff,
    triangleKernelState,ContinuousLinearMap.id_apply] using he

lemma partialCutoffTriangle_norm_le_polar {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState)
    (W : ℝ→Vec→L[ℝ]Vec) {J : Set ℝ} {p : TrianglePhase}
    (ht : p.1.1∈J) (hp : p∈trianglePhaseDomain T) (hW : ‖W p.1.1‖≤1) :
    ‖partialCutoffTriangle s α zX T Q H W J p‖≤
      (p.1.1-p.1.2.1)^2 *
        ‖((s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2)*
          (1-dot p.1.2.2.1 (velocity (α zX p.1.1).2))/
          ((p.1.1-p.1.2.1)*(1-dot p.1.2.2.1 (velocity p.2)))*
          fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX (triangleKernelState α zX p))
            (H (triangleKernelState α zX p))) •
          signedPrimitive (velocity (α zX p.1.1).2) (velocity p.2) p.1.2.2.1)‖ := by
  rw [partialCutoffTriangle_of_mem ht]
  calc
    _≤‖triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p‖ :=
      ((W p.1.1).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hW (norm_nonneg _))
    _=_ := by rw [trianglePartial_eq_polar Q H hp,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]

def representativeMagneticCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ :=
  let p := sourceRepresentative (k 0)
  let φ := cappedRepresentative (k 2)
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := representativeClosedBin T w k
  ENNReal.ofReal (φ/p) *
    (∫⁻z : ConeCoordinate, ENNReal.ofReal (z.1-z.2.1)*
      ENNReal.ofReal (prefixConeMagnetic s T X z)*physicalBinDensity s X V B z.1 z.2.1 z.2.2
        ∂physicalBinMeasure V B (Icc a b))

lemma PhaseFlowOn.bulkSource_pointwise {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) {v : Vec}
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2)) :
    ‖partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX) W J (z,v)‖≤
      (99840000*C)*(z.1-z.2.1)*
        (cappedRepresentative (k 2)/(sourceRepresentative (k 0)*(cappedRepresentative (k 1))^2)*
          prefixConeGood s T (fun t=>(prefixFlow F.flow T zX t).1) z+
         cappedRepresentative (k 2)/sourceRepresentative (k 0)*
          prefixConeMagnetic s T (fun t=>(prefixFlow F.flow T zX t).1) z)*
          s.f (z.2.1,((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hp0 : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := hJT hz.1
  have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans ht.2⟩
  have hf := hs.nonnegative _ hσ ((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have heq : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq ht]
    have hD : 1-dot z.2.2.1 (velocity (F.flow zX z.1).2)∈
        Icc ((cappedRepresentative (k 2))^2/2) (8*(cappedRepresentative (k 2))^2) := by
      simpa only [heq,representativeClosedBin] using hz.2.2.2.2
    rw [heq] at hv ⊢
    apply (partialCutoffTriangle_norm_le_polar Q (coneSourceCutoffTangent s F.flow zX)
      W hz.1 hp (hW _ hz.1)).trans
    simpa only [coneCutoffState,triangleKernelState,coneSourceCutoffTangent,coneCutoffRate,
      cutoffSourceTangent,prefixConeGood,prefixConeMagnetic,prefixField,coneFoot,
      prefixClamp_eq hσ,heq,lorentzField,lorentzPhase] using unprojected_source_bin_cost (T:=T)
        (E:=s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1))
        (B:=s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)) hC0 hC (sphere_norm z.2.2)
        (sub_pos.mpr hp.2.2) (by simpa only [heq] using hf) hp0 hθ hφ hv.1.1 hsmall hv.2.1 hD Q
  · rw [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1]
    simp only [triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero]
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    have hg : 0≤prefixConeGood s T (fun t=>(prefixFlow F.flow T zX t).1) z :=
      add_nonneg (norm_nonneg _) (abs_nonneg _)
    have hb : 0≤prefixConeMagnetic s T (fun t=>(prefixFlow F.flow T zX t).1) z := norm_nonneg _
    positivity

def representativeSpatialTransition (P M A w I : ℝ) (k : Fin 4→ℕ) : Prop :=
  ¬ representativeSelected P M A w I k ∧
    ∃j : Fin 4→ℕ,representativeSelected P M A w I j ∧
      ∀i,j i≤k i+2 ∧ k i≤j i+2

lemma Admissible.regular_spatial_transition_pair_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np nf : ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤cappedRepresentative nf/16 ∧
          regularCentralIndex P M A I w ![np,nt,nf,nr] ∧
          representativeSpatialTransition P M A w I ![np,nt,nf,nr] then
        representativeSpatialCost s F zX w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal (C*Real.sqrt I*
        representativeSharedRadius s F zX P M A w a b I (np,nf)*
        sourceRepresentative np*cappedRepresentative nf) := by
  classical
  obtain ⟨Cu,hCu,hunselected⟩ := hd.unselected_spatial_polynomial_cap T₀
  obtain ⟨Cr,hCr,hregular⟩ := hd.representative_spatial_regular_shared T₀
  let C₀ := max Cu Cr
  have hC₀ : 0≤C₀ := hCu.trans (le_max_left _ _)
  let α : ℝ := 1/50000
  let γ : ℝ := (1-2*α)/(1-α)
  let K := (2+dyadicBalanceConstant α 1)*dyadicBalanceConstant (γ*((1-α)/(1+α))) γ
  have hα : 0<α := by norm_num [α]
  have hα2 : α<1/2 := by norm_num [α]
  have hγ : 0<γ := by norm_num [γ,α]
  have hK : 0<K := mul_pos (by positivity [dyadicBalanceConstant_pos hα (by norm_num : (0:ℝ)<1)])
    (dyadicBalanceConstant_pos (mul_pos hγ (div_pos (by norm_num [α]) (by norm_num [α]))) hγ)
  refine ⟨32768*C₀*K,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hunselected M A hM hA,eventually_gt_atTop (0:ℝ)] with P hun hP
  intro s T F hs hT hTT zX np nf a b I w hzX ha hb hab hI hJI hw hsource HZ
  let p := sourceRepresentative np
  let φ := cappedRepresentative nf
  let R := representativeSharedRadius s F zX P M A w a b I (np,nf)
  let aa := spatialThresholdA P p φ
  let bb := spatialThresholdB P I p φ
  let cc := R^2/(p*φ)
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hφ : 0<φ := cappedRepresentative_pos _
  have hR : 0<R := zero_lt_one.trans_le (representativeSharedRadius_one_le _ _ _ _ _ _ _ _ _ _ _)
  have haa : 0<aa := spatialThresholdA_pos hP hp hφ
  have hbb : 0<bb := spatialThresholdB_pos hP hI hp hφ
  have hcc : 0<cc := by dsimp [cc]; positivity
  have hpoint (nt nr : ℕ) :
      (if cappedRepresentative nt≤cappedRepresentative nf/16 ∧
          regularCentralIndex P M A I w ![np,nt,nf,nr] ∧
          representativeSpatialTransition P M A w I ![np,nt,nf,nr] then
        representativeSpatialCost s F zX w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal C₀*(if bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
        ENNReal.ofReal (min (aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
          (cc/(cappedRepresentative nt*cappedRepresentative nr))) else 0) := by
    by_cases hk : cappedRepresentative nt≤cappedRepresentative nf/16 ∧
        regularCentralIndex P M A I w ![np,nt,nf,nr] ∧
        representativeSpatialTransition P M A w I ![np,nt,nf,nr]
    · rw [ite_eq_left hk]
      obtain ⟨hj,hreg,htrans⟩ := hk
      obtain ⟨hfail,j,hsel,hneighbor⟩ := htrans
      have hlower := selected_neighbor_radial_condition hP hI hsel hneighbor
      change bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) at hlower
      rw [ite_eq_left hlower,←ENNReal.ofReal_mul hC₀]
      have hu := hun s T F hs hT hTT zX ![np,nt,nf,nr] a b I w hzX ha hb hab hI hJI hw
        hj hfail hsource HZ
      have hr := hregular M A P hM hA.le hP s T F hs hT hTT zX ![np,nt,nf,nr] a b I w
        hzX ha hb hI hJI hw hj hreg HZ
      dsimp only at hu hr
      change _≤ENNReal.ofReal (Cu*(P^2*(selectionWeight P (cappedRepresentative nt) φ (cappedRepresentative nr))^2*cappedRepresentative nt/(p*φ))) at hu
      change _≤ENNReal.ofReal (Cr*min (I*cappedRepresentative nr*p^3*cappedRepresentative nt*φ^3) (R^2/(p*cappedRepresentative nr*cappedRepresentative nt*φ))) at hr
      have hnt := cappedRepresentative_pos nt
      have hnr := cappedRepresentative_pos nr
      have hu' : representativeSpatialCost s F zX w ![np,nt,nf,nr] a b≤
          ENNReal.ofReal (C₀*(aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)) := by
        rw [spatial_polynomial_normalisation hP hp (cappedRepresentative_pos nt) hφ (cappedRepresentative_pos nr)] at hu
        exact hu.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      have hr' : representativeSpatialCost s F zX w ![np,nt,nf,nr] a b≤
          ENNReal.ofReal (C₀*(cc/(cappedRepresentative nt*cappedRepresentative nr))) := by
        apply hr.trans
        apply ENNReal.ofReal_le_ofReal
        calc
          _≤Cr*(R^2/(p*cappedRepresentative nr*cappedRepresentative nt*φ)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hCr
          _≤C₀*(R^2/(p*cappedRepresentative nr*cappedRepresentative nt*φ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
          _=C₀*(cc/(cappedRepresentative nt*cappedRepresentative nr)) := by dsimp [cc]; ring
      rw [mul_min_of_nonneg _ _ hC₀,ENNReal.ofReal_min]
      exact le_min hu' hr'
    · rw [ite_eq_right hk]
      exact bot_le
  calc
    _≤∑'nt : ℕ,∑'nr : ℕ,ENNReal.ofReal C₀*
        (if bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
          ENNReal.ofReal (min (aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
            (cc/(cappedRepresentative nt*cappedRepresentative nr))) else 0) :=
      ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nt))
    _=ENNReal.ofReal C₀*(∑'nt : ℕ,∑'nr : ℕ,
        if bb*(cappedRepresentative nt)^(-α)≤(cappedRepresentative nr)^(1-α) then
          ENNReal.ofReal (min (aa*(cappedRepresentative nt)^(1-α)*(cappedRepresentative nr)^α)
            (cc/(cappedRepresentative nt*cappedRepresentative nr))) else 0) := by
      simp only [ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal C₀*ENNReal.ofReal (K*Real.sqrt (aa*cc/bb)) := by
      apply mul_le_mul' le_rfl
      convert spatial_transition_double_sum haa hbb hcc hα hα2 using 1
      congr 1
      dsimp only [K,γ]
      ring
    _= _ := by
      rw [←ENNReal.ofReal_mul hC₀]
      have he := spatial_crossing_datum_scale hP hI hp hφ hR.le
      change Real.sqrt (aa*cc/bb)=32768*Real.sqrt I*R*p*φ at he
      rw [he]
      congr 1
      dsimp only [R,p,φ]
      ring

def bulkSelection (P M A w I : ℝ) : Set (Fin 4→ℕ) :=
  {k | cappedRepresentative (k 1)≤cappedRepresentative (k 2)/1024 ∧
    representativeSelected P M A w I k}

lemma physicalCutoff_positive_source_floor {T r : ℝ} {v W n : Vec} {k : Fin 4→ℕ}
    (hn : ‖n‖=1)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v W)) :
    1/sourceRepresentative (k 0)≤cappedRepresentative (k 1) := by
  have hb := dyadicMultiFactor_positive_bands hk
  have hq := (dyadicBand_source_range (hb 0)).2
  have hθ := (dyadicBand_capped_range (hb 1)).2
  have hl := source_angle_coordinate_lower v n hn
  change Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) at hθ
  have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hθ0 := cappedRepresentative_pos (k 1)
  have hm := mul_le_mul hq hθ (Real.sqrt_nonneg _) (by positivity : 0≤ sourceRepresentative (k 0)/32)
  apply (div_le_iff₀ hp).mpr
  nlinarith

lemma bulkSelection_neighbor_aperture {P M A w I : ℝ} {j k : Fin 4→ℕ}
    (hj : j∈bulkSelection P M A w I)
    (hjk : ∀i,j i≤k i+2 ∧ k i≤j i+2) :
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/64 := by
  have hθ := cappedRepresentative_le_four (hjk 1).1
  have hφ := cappedRepresentative_le_four (hjk 2).2
  have hsmall := hj.1
  linarith

lemma bulkSelection_derivative_physical_cover {T P M A w I t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec}
    (hP : 1024*q v≤P) (H : CutoffState)
    (hd : fderiv ℝ (stateCutoff T (bulkSelection P M A w I)) (t-σ,n.1,v,V t) H≠0) :
    ∃k∈centralIndexSector P,
      (cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) ∨
        representativeSpatialTransition P M A w I k) ∧
      ((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ≤ max 1 T := by linarith [hσ.1,le_max_right (1:ℝ) T]
  obtain ⟨j,hj,k,hk,hjp,hkp,_⟩ := stateCutoff_partial_boundary
    (z:=(t-σ,n.1,v,V t)) (bulkSelection P M A w I) hr hrT (sphere_norm n) H hd
  have hc := dyadicMultiFactor_positive_index_comparison hjp hkp
  have hnear : ∀i,j i≤k i+2 ∧ k i≤j i+2 := fun i=>(hc i).symm
  have hangle := bulkSelection_neighbor_aperture hj hnear
  have hfloor := physicalCutoff_positive_source_floor (sphere_norm n) hkp
  have hsource := (sourceRepresentative_mem_range (dyadicMultiFactor_positive_bands hkp 0) hP).2
  have hφ := cappedRepresentative_pos (k 2)
  have hsector : k∈centralIndexSector P := ⟨hsource,by linarith,by linarith⟩
  refine ⟨k,hsector,?_,physicalCutoff_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hkp⟩
  by_cases hs : cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)
  · exact Or.inl hs
  · right
    refine ⟨?_,j,hj.2,hnear⟩
    intro hsel
    apply hk
    exact ⟨by linarith [lt_of_not_ge hs],hsel⟩

lemma bulkSelection_positive_smallSector {T P M A w I r : ℝ} {v W n : Vec} {k : Fin 4→ℕ}
    (hn : ‖n‖=1) (hP : 1024*q v≤P) (hsel : k∈bulkSelection P M A w I)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v W)) :
    k∈representativeSmallSector P := by
  refine ⟨(sourceRepresentative_mem_range (dyadicMultiFactor_positive_bands hk 0) hP).2,
    physicalCutoff_positive_source_floor hn hk,?_⟩
  have hθ := hsel.1
  have hφ := cappedRepresentative_pos (k 2)
  linarith

lemma partialCutoffTriangle_nonzero_data {s : Solution} {α : Phase→ℝ→Phase}
    {zX : Phase} {T : ℝ} {Q : Set (Fin 4→ℕ)}
    {H : ConeKernelState→CutoffState} {W : ℝ→Vec→L[ℝ]Vec} {J : Set ℝ}
    {p : TrianglePhase} (hp : partialCutoffTriangle s α zX T Q H W J p≠0) :
    p.1.1∈J ∧ p∈trianglePhaseDomain T ∧
      s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2)≠0 ∧
      fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX (triangleKernelState α zX p))
        (H (triangleKernelState α zX p))≠0 := by
  have ht : p.1.1∈J := by
    by_contra hc
    exact hp (partialCutoffTriangle_of_notMem hc)
  have hc : p∈trianglePhaseDomain T := by
    by_contra hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_notMem hh,map_zero]
  have hf : s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2)≠0 := by
    intro hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_mem hc,hh,
      zero_smul,smul_zero,map_zero]
  have hd : fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX (triangleKernelState α zX p))
      (H (triangleKernelState α zX p))≠0 := by
    intro hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_mem hc,
      normalisedPartialCutoff,hh,zero_smul,smul_zero,map_zero]
  exact ⟨ht,hc,hf,hd⟩

lemma PhaseFlowOn.partialCutoffTriangle_physical_nonzero {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : partialCutoffTriangle s F.flow zX T Q H W J p≠0) :
    p.1.1∈J ∧ p.1.1≤T ∧ p.1.2.1∈Ico 0 p.1.1 ∧
      q (prefixFlow F.flow T zX p.1.1).2∈Icc (w/8) (8*w) ∧ 1024*q p.2≤P ∧
      fderiv ℝ (stateCutoff T Q)
        (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(prefixFlow F.flow T zX p.1.1).2)
        (H (triangleKernelState F.flow zX p))≠0 := by
  obtain ⟨ht,hc,hf,hd⟩ := partialCutoffTriangle_nonzero_data hp
  have he : (prefixFlow F.flow T zX p.1.1).2=(F.flow zX p.1.1).2 := by
    simp only [prefixFlow,prefixClamp_eq (hJT ht)]
  refine ⟨ht,(hJT ht).2,⟨hc.2.1.le,hc.2.2⟩,?_,?_,?_⟩
  · rw [he]; exact hband _ ht
  · exact hP p.1.2.1 ⟨hc.2.1.le,hc.2.2.le.trans hc.1.2.le⟩
      ((triangleKernelState F.flow zX p).2.2) hf
  · rw [he]; exact hd

lemma PhaseFlowOn.bulkCutoffTriangle_support {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    (H : ConeKernelState→CutoffState) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I) H W J p≠0) :
    ∃k∈centralIndexSector P,
      (cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) ∨
        representativeSpatialTransition P M A w I k) ∧
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J := by
  obtain ⟨ht,htT,hσ,hb,hv,hd⟩ := F.partialCutoffTriangle_physical_nonzero zX
    (bulkSelection P M A w I) H W hJT hband hP hp
  exact bulkSelection_derivative_physical_cover (P:=P) (M:=M) (A:=A) (w:=w) (I:=I)
    (V:=fun t=>(prefixFlow F.flow T zX t).2) (n:=p.1.2.2) ht htT hσ hb hv _ hd

lemma bulkSelection_derivative_small_cover {T P M A w I t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec}
    (hP : 1024*q v≤P) (H : CutoffState)
    (hd : fderiv ℝ (stateCutoff T (bulkSelection P M A w I)) (t-σ,n.1,v,V t) H≠0) :
    ∃k∈representativeSmallSector P,
      (cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) ∨
        representativeSpatialTransition P M A w I k) ∧
      ((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ≤ max 1 T := by linarith [hσ.1,le_max_right (1:ℝ) T]
  obtain ⟨j,hj,k,hk,hjp,hkp,_⟩ := stateCutoff_partial_boundary
    (z:=(t-σ,n.1,v,V t)) (bulkSelection P M A w I) hr hrT (sphere_norm n) H hd
  have hc := dyadicMultiFactor_positive_index_comparison hjp hkp
  have hnear : ∀i,j i≤k i+2 ∧ k i≤j i+2 := fun i=>(hc i).symm
  have hangle := bulkSelection_neighbor_aperture hj hnear
  have hfloor := physicalCutoff_positive_source_floor (sphere_norm n) hkp
  have hsource := (sourceRepresentative_mem_range (dyadicMultiFactor_positive_bands hkp 0) hP).2
  have hφ := cappedRepresentative_pos (k 2)
  have hsector : k∈representativeSmallSector P := ⟨hsource,hfloor,by linarith⟩
  refine ⟨k,hsector,?_,physicalCutoff_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hkp⟩
  by_cases hs : cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)
  · exact Or.inl hs
  · right
    refine ⟨?_,j,hj.2,hnear⟩
    intro hsel
    apply hk
    exact ⟨by linarith [lt_of_not_ge hs],hsel⟩

lemma PhaseFlowOn.bulkCutoffTriangle_small_support {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    (H : ConeKernelState→CutoffState) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I) H W J p≠0) :
    ∃k∈representativeSmallSector P,
      (cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) ∨
        representativeSpatialTransition P M A w I k) ∧
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J := by
  obtain ⟨ht,htT,hσ,hb,hv,hd⟩ := F.partialCutoffTriangle_physical_nonzero zX
    (bulkSelection P M A w I) H W hJT hband hP hp
  exact bulkSelection_derivative_small_cover (P:=P) (M:=M) (A:=A) (w:=w) (I:=I)
    (V:=fun t=>(prefixFlow F.flow T zX t).2) (n:=p.1.2.2) ht htT hσ hb hv _ hd

def bulkSourceBoundary (P M A w I : ℝ) : Set (Fin 4→ℕ) :=
  {k | k∈representativeSmallSector P ∧
    (cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) ∨
      representativeSpatialTransition P M A w I k)}

lemma tsum_structuralCentralSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,({k | k∈centralIndexSector P ∧
      cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)}).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative n.2/16384≤cappedRepresentative nt ∧
          cappedRepresentative nt≤cappedRepresentative n.2/16 then f ![n.1,nt,n.2,nr] else 0) n := by
  have he : ({k | k∈centralIndexSector P ∧
      cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)}).indicator f=
      (centralIndexSector P).indicator (fun k=>if cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1) then f k else 0) := by
    funext k
    simp only [indicator_apply,mem_ofPred_eq]
    split_ifs <;> simp_all
  rw [he,tsum_centralIndexSector]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1≤cappedRepresentative n.2
  · have hn' : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1≤cappedRepresentative n.2} := hn
    rw [indicator_of_mem hn',indicator_of_mem hn']
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    split_ifs <;> simp_all
  · have hn' : n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1≤cappedRepresentative n.2} := hn
    rw [indicator_of_notMem hn',indicator_of_notMem hn']

lemma Admissible.bulk_source_good_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∑'k : Fin 4→ℕ,(bulkSourceBoundary P M A w I).indicator
        (fun k=>representativeGoodCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hstruct⟩ := hd.good_structural_uniform T₀
  obtain ⟨Cu,hCu,hunsel⟩ := hd.unselected_good_uniform T₀
  refine ⟨Cs+Cu,add_nonneg hCs hCu,?_⟩
  intro M A hM hA
  filter_upwards [hunsel M A (zero_lt_one.trans_le hM) hA] with P hu
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  let f := fun k=>representativeGoodCost s F zX w k a b
  let S := {k | k∈centralIndexSector P ∧ cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)}
  let U := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hPB : P*Real.sqrt I≤B := le_add_of_nonneg_right (by positivity)
  have hbnd : (∑'k,(bulkSourceBoundary P M A w I).indicator f k)≤
      (∑'k,S.indicator f k)+(∑'k,U.indicator f k) := by
    rw [←ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈bulkSourceBoundary P M A w I
    · rw [indicator_of_mem hk]
      rcases hk.2 with hstr|htr
      · have hks : k∈S := ⟨representativeSmallSector_subset_centralIndexSector P hk.1,hstr⟩
        rw [indicator_of_mem hks]
        exact le_add_right le_rfl
      · have hku : k∈U := ⟨hk.1,htr.1⟩
        rw [indicator_of_mem hku]
        exact le_add_left le_rfl
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hst : (∑'k,S.indicator f k)≤ENNReal.ofReal (Cs*B) := by
    rw [show S={k | k∈centralIndexSector P ∧ cappedRepresentative (k 2)/16384≤cappedRepresentative (k 1)} by rfl,
      tsum_structuralCentralSector]
    exact hstruct M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  have hun : (∑'k,U.indicator f k)≤ENNReal.ofReal (Cu*(P*Real.sqrt I)) := by
    simpa only [mul_assoc] using hu s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI
      (zero_lt_one.trans_le hw) hsource HZ
  apply hbnd.trans
  calc
    _≤ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cu*(P*Real.sqrt I)) := add_le_add hst hun
    _≤ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cu*B) := add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hPB hCu))
    _=ENNReal.ofReal ((Cs+Cu)*B) := by
      rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCu hB)]; congr 1; ring

lemma PhaseFlowOn.bulkSource_density {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) :
    (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneSourceCutoffTangent s F.flow zX) W J (z,v)‖)≤
      ENNReal.ofReal ((99840000*C)*(cappedRepresentative (k 2)/(sourceRepresentative (k 0)*(cappedRepresentative (k 1))^2)))*
        (ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T (fun t=>(prefixFlow F.flow T zX t).1) z)*
          physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2)+
      ENNReal.ofReal ((99840000*C)*(cappedRepresentative (k 2)/sourceRepresentative (k 0)))*
        (ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeMagnetic s T (fun t=>(prefixFlow F.flow T zX t).1) z)*
          physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
  have hp : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
  let u := cappedRepresentative (k 2)/(sourceRepresentative (k 0)*(cappedRepresentative (k 1))^2)
  let v := cappedRepresentative (k 2)/sourceRepresentative (k 0)
  let g := prefixConeGood s T (fun t=>(prefixFlow F.flow T zX t).1) z
  let m := prefixConeMagnetic s T (fun t=>(prefixFlow F.flow T zX t).1) z
  have hu : 0≤u := by dsimp [u]; positivity
  have hv : 0≤v := by dsimp [v]; positivity
  have hg : 0≤g := add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hm : 0 ≤ m := norm_nonneg _
  have hc : 0≤99840000*C := by positivity
  have hcoeff : 0≤(99840000*C)*(z.1-z.2.1)*(u*g+v*m) := by positivity
  have hb : (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX) W J (z,v)‖)≤
      ENNReal.ofReal ((99840000*C)*(z.1-z.2.1)*(u*g+v*m))*
        physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
    unfold physicalBinDensity
    rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
    intro vv hvv
    rw [←ENNReal.ofReal_mul hcoeff]
    exact ENNReal.ofReal_le_ofReal (F.bulkSource_pointwise hs zX Q hJT W hW hC0 hC k hsmall hz hvv)
  apply hb.trans_eq
  change ENNReal.ofReal ((99840000*C)*(z.1-z.2.1)*(u*g+v*m))*_ =
    ENNReal.ofReal ((99840000*C)*u)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal g*_)+
    ENNReal.ofReal ((99840000*C)*v)*(ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal m*_)
  rw [ENNReal.ofReal_mul (mul_nonneg hc hr),ENNReal.ofReal_add (mul_nonneg hu hg) (mul_nonneg hv hm),
    ENNReal.ofReal_mul hu,ENNReal.ofReal_mul hv,ENNReal.ofReal_mul hc,
    ENNReal.ofReal_mul hc,ENNReal.ofReal_mul hc]
  ring

lemma PhaseFlowOn.bulkSource_bin_integral {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈Icc a b,‖W t‖≤1)
    {C : ℝ} (hC0 : 0≤C) (hC : ∀k : ℕ,∀x : ℝ,|x*deriv (dyadicFactor k) x|≤C)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
        (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneSourceCutoffTangent s F.flow zX) W (Icc a b) (z,v)‖
      ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal (99840000*C)*(representativeGoodCost s F zX w k a b+
        representativeMagneticCost s F zX w k a b) := by
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hX : Measurable (fun t=>(prefixFlow F.flow T zX t).1) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).fst.measurable
  have hN := physicalBinDensity_aemeasurable hs hT hX hV (representativeClosedBin T w k)
    measurableSet_Icc (Icc_subset_Icc ha hb)
  have hG := hs.measurable_prefixConeGood hT hX
  have hr : Measurable (fun z : ConeCoordinate=>ENNReal.ofReal (z.1-z.2.1)) :=
    (measurable_fst.sub measurable_snd.fst).ennreal_ofReal
  have hcost := fun z hz=>F.bulkSource_density (w:=w) hs zX Q (Icc_subset_Icc ha hb) W hW hC0 hC k hsmall (z:=z) hz
  have hbnd := setLIntegral_mono' (μ:=volume.prod (volume.prod sphereMeasure))
    (measurableSet_physicalBinBase hV (representativeClosedBin T w k) measurableSet_Icc) hcost
  apply hbnd.trans_eq
  unfold physicalBinMeasure at hN
  have hGN : AEMeasurable (fun z : ConeCoordinate=>
      ENNReal.ofReal ((99840000*C)*(cappedRepresentative (k 2)/(sourceRepresentative (k 0)*(cappedRepresentative (k 1))^2)))*
        (ENNReal.ofReal (z.1-z.2.1)*ENNReal.ofReal (prefixConeGood s T (fun t=>(prefixFlow F.flow T zX t).1) z)*
          physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
            (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2))
      ((volume.prod (volume.prod sphereMeasure)).restrict
        (physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))) := by
    exact (((hr.mul hG.ennreal_ofReal).aemeasurable.mul hN).const_mul _)
  rw [lintegral_add_left' hGN,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold representativeGoodCost representativeMagneticCost
  dsimp only
  rw [ENNReal.ofReal_mul (by positivity : 0≤99840000*C),ENNReal.ofReal_mul (by positivity : 0≤99840000*C),mul_add]
  simp only [mul_assoc,physicalBinMeasure]

lemma Admissible.spatial_transition_regular_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 0<w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 ∧
          regularCentralIndex P M A I w ![n.1,nt,n.2,nr] ∧
          representativeSpatialTransition P M A w I ![n.1,nt,n.2,nr] then
          representativeSpatialCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cc,hCc,hcentral⟩ := hd.regular_spatial_transition_pair_sum T₀
  let E := 3468*datumEnergyNumber d
  let D := pairCountConstant+4*Real.sqrt pairCountConstant+2
  let K := 4+16384*Real.sqrt E*D
  have hE : 0≤E := mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg
  have hD : 0≤D := by dsimp [D]; exact add_nonneg (add_nonneg pairCountConstant_pos.le (by positivity)) (by norm_num)
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨Cc*K,mul_nonneg hCc hK,?_⟩
  intro M A hM hA
  filter_upwards [hcentral M A hM hA] with P hc
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource HZ
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let J := representativeJointEnergy s F zX a b I
  let R := representativeSharedRadius s F zX P M A w a b I
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hR (n : ℕ×ℕ) : 0<R n := zero_lt_one.trans_le (representativeSharedRadius_one_le ..)
  have hp (n : ℕ) : 0<sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpair (n : ℕ×ℕ) (hn : n∈Q) : sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1≤cappedRepresentative n.2 := hn
  obtain ⟨hJs,hJsum,hJeq⟩ := hs.representativeJointEnergy_sum hd F zX hI hJI
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>n∈Q)
  have hU (n) (hn : n∈U) : n∈Q := (Finset.mem_filter.mp hn).2
  have he : (∑n∈S,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 ∧
        regularCentralIndex P M A I w ![n.1,nt,n.2,nr] ∧
        representativeSpatialTransition P M A w I ![n.1,nt,n.2,nr] then
        representativeSpatialCost s F zX w ![n.1,nt,n.2,nr] a b else 0) n)=
      ∑n∈U,(∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt≤cappedRepresentative n.2/16 ∧
        regularCentralIndex P M A I w ![n.1,nt,n.2,nr] ∧
        representativeSpatialTransition P M A w I ![n.1,nt,n.2,nr] then
        representativeSpatialCost s F zX w ![n.1,nt,n.2,nr] a b else 0) := by
    simp [U,Finset.sum_filter,indicator_apply]
  rw [he]
  have hJn (n : ℕ×ℕ) : 0≤J n := representativeJointEnergy_nonneg ..
  have hbudget : ∑n∈U,J n≤E := (hJs.sum_le_tsum U (fun n _=>hJn n)).trans hJsum
  have hn := shared_radius_pair_sum hP hL hM.le hA.le hI.le hw hwP hE U J
    (fun n _=>hJn n) hbudget (fun n hn=>hpair n (hU n hn))
  change (∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)≤
    K*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) at hn
  calc
    _≤∑n∈U,ENNReal.ofReal (Cc*Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hc s T F hs hT hTT zX n.1 n.2 a b I w
        hzX ha hb hab hI hJI hw hsource HZ
    _=ENNReal.ofReal (Cc*(∑n∈U,Real.sqrt I*R n*sourceRepresentative n.1*cappedRepresentative n.2)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>by
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCc (Real.sqrt_nonneg I)) (hR n).le) (hp _).le) (cappedRepresentative_pos _).le)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left hn hCc
      simpa only [mul_assoc] using hh)


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma spatial_exception_radial_sum {P I p θ φ : ℝ} (hP : 0<P)
    (hI : 0≤I) (hp : 0<p) (hθ : 0<θ) (hφ : 0<φ) :
    (∑'nr : ℕ, if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal (I*cappedRepresentative nr*p^3*θ*φ^3) else 0)≤
      ENNReal.ofReal (2*I*p^3/P^2*θ*φ^3) := by
  classical
  have hC : 0≤I*p^3*θ*φ^3 := by positivity
  have he (nr : ℕ) : (if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal (I*cappedRepresentative nr*p^3*θ*φ^3) else 0)=
      ENNReal.ofReal (I*p^3*θ*φ^3)*ENNReal.ofReal
        (if cappedRepresentative nr≤1/P^2 then cappedRepresentative nr else 0) := by
    split_ifs <;> simp [←ENNReal.ofReal_mul hC]; congr 1; ring
  simp_rw [he]
  rw [ENNReal.tsum_mul_left]
  calc
    _≤ENNReal.ofReal (I*p^3*θ*φ^3)*ENNReal.ofReal (2*(1/P^2)) :=
      mul_le_mul' le_rfl (capped_linear_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma spatial_exception_angle_radial_sum {P I p φ : ℝ} (hP : 0<P)
    (hI : 0≤I) (hp : 0<p) (hφ : 0<φ) :
    (∑'nt : ℕ, if cappedRepresentative nt≤φ then ∑'nr : ℕ,
      if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal (I*cappedRepresentative nr*p^3*cappedRepresentative nt*φ^3) else 0 else 0)≤
      ENNReal.ofReal (4*I*p^3/P^2*φ^4) := by
  classical
  have hC : 0≤2*I*p^3/P^2*φ^3 := by positivity
  calc
    _≤∑'nt : ℕ, if cappedRepresentative nt≤φ then
        ENNReal.ofReal (2*I*p^3/P^2*cappedRepresentative nt*φ^3) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nt
      split_ifs
      · exact spatial_exception_radial_sum hP hI hp (cappedRepresentative_pos _) hφ
      · rfl
    _=ENNReal.ofReal (2*I*p^3/P^2*φ^3)*
        (∑'nt : ℕ, ENNReal.ofReal (if cappedRepresentative nt≤φ then cappedRepresentative nt else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nt
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]; congr 1; ring
    _≤ENNReal.ofReal (2*I*p^3/P^2*φ^3)*ENNReal.ofReal (2*φ) :=
      mul_le_mul' le_rfl (capped_linear_tail_sum hφ)
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

lemma spatial_exception_triple_sum {P I p w : ℝ} (hP : 0<P)
    (hI : 0≤I) (hp : 0<p) (hw : 0<w) :
    (∑'nf : ℕ, if cappedRepresentative nf≤512/min p w then
      ∑'nt : ℕ, if cappedRepresentative nt≤cappedRepresentative nf then ∑'nr : ℕ,
        if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal (I*cappedRepresentative nr*p^3*cappedRepresentative nt*(cappedRepresentative nf)^3)
        else 0 else 0 else 0)≤ENNReal.ofReal (8*I*p^3/P^2*(512/min p w)^4) := by
  classical
  have hm : 0 < min p w := lt_min hp hw
  have hC : 0≤4*I*p^3/P^2 := by positivity
  calc
    _≤∑'nf : ℕ,if cappedRepresentative nf≤512/min p w then
        ENNReal.ofReal (4*I*p^3/P^2*(cappedRepresentative nf)^4) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro nf
      split_ifs
      · exact spatial_exception_angle_radial_sum hP hI hp (cappedRepresentative_pos _)
      · rfl
    _=ENNReal.ofReal (4*I*p^3/P^2)*
        (∑'nf : ℕ,ENNReal.ofReal (if cappedRepresentative nf≤512/min p w then (cappedRepresentative nf)^4 else 0)) := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro nf
      split_ifs <;> simp [←ENNReal.ofReal_mul hC]
    _≤ENNReal.ofReal (4*I*p^3/P^2)*ENNReal.ofReal (2*(512/min p w)^4) :=
      mul_le_mul' le_rfl (capped_fourth_tail_sum (by positivity))
    _=_ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

noncomputable def representativeExceptionSpatialCost (s : Solution) {T : ℝ} (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) : ℝ≥0∞ := by
  classical
  exact if regularCentralIndex P M A I w k then 0 else representativeSpatialCost s F zX w k a b

lemma Admissible.representative_exception_spatial_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative nf/16 then
          representativeExceptionSpatialCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*(sourceRepresentative np)^3/P^2*(512/min (sourceRepresentative np) w)^4) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_spatial_near T₀
  refine ⟨8*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hpoint (nf nt nr : ℕ) :
      (if cappedRepresentative nt≤cappedRepresentative nf/16 then
        representativeExceptionSpatialCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal Cn*(if cappedRepresentative nf≤512/min p w then
        if cappedRepresentative nt≤cappedRepresentative nf then
          if cappedRepresentative nr≤1/P^2 then
            ENNReal.ofReal (I*cappedRepresentative nr*p^3*cappedRepresentative nt*(cappedRepresentative nf)^3)
          else 0 else 0 else 0) := by
    by_cases ht : cappedRepresentative nt≤cappedRepresentative nf/16
    · rw [ite_eq_left ht]
      by_cases hr : regularCentralIndex P M A I w ![np,nt,nf,nr]
      · simp only [representativeExceptionSpatialCost,ite_eq_left hr]
        exact bot_le
      · have hreg : ¬(512/min p w<cappedRepresentative nf ∨
            min I (stabilityLength P 16384 M A p w (cappedRepresentative nf))<cappedRepresentative nr) := by
          simpa [regularCentralIndex,p] using hr
        have hf : cappedRepresentative nf≤512/min p w := le_of_not_gt (not_or.mp hreg).1
        have hnr : cappedRepresentative nr≤1/P^2 :=
          ((le_of_not_gt (not_or.mp hreg).2).trans (min_le_right _ _)).trans
            (small_deficit_stabilityLength hP hM hp hw (cappedRepresentative_pos _) hf)
        have hnt : cappedRepresentative nt≤cappedRepresentative nf := by
          have hf0 := (cappedRepresentative_pos nf).le
          linarith
        rw [ite_eq_left hf,ite_eq_left hnt,ite_eq_left hnr,representativeExceptionSpatialCost,ite_eq_right hr]
        rw [←ENNReal.ofReal_mul hCn]
        simpa [p] using hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI
    · rw [ite_eq_right ht]
      exact bot_le
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        ENNReal.ofReal Cn*(if cappedRepresentative nf≤512/min p w then
          if cappedRepresentative nt≤cappedRepresentative nf then
            if cappedRepresentative nr≤1/P^2 then
              ENNReal.ofReal (I*cappedRepresentative nr*p^3*cappedRepresentative nt*(cappedRepresentative nf)^3)
            else 0 else 0 else 0) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))
    _=ENNReal.ofReal Cn*(∑'nf : ℕ,if cappedRepresentative nf≤512/min p w then
        ∑'nt : ℕ,if cappedRepresentative nt≤cappedRepresentative nf then
          ∑'nr : ℕ,if cappedRepresentative nr≤1/P^2 then
            ENNReal.ofReal (I*cappedRepresentative nr*p^3*cappedRepresentative nt*(cappedRepresentative nf)^3)
          else 0 else 0 else 0) := by
      simp only [ENNReal.tsum_mul_left]
      congr 1
      apply tsum_congr
      intro nf
      split_ifs with hf
      · apply tsum_congr
        intro nt
        split_ifs with ht <;> simp only [tsum_zero]
      · simp only [tsum_zero]
    _≤ENNReal.ofReal Cn*ENNReal.ofReal (8*I*p^3/P^2*(512/min p w)^4) :=
      mul_le_mul' le_rfl (spatial_exception_triple_sum hP hI.le hp hw)
    _=_ := by rw [←ENNReal.ofReal_mul hCn]; congr 1; dsimp only [p]; ring

lemma Admissible.spatial_exception_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 1≤w → w≤P →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1≤cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if cappedRepresentative nt≤cappedRepresentative n.2/16 then
          representativeExceptionSpatialCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*(I*P^2*Real.log (2+P)/w)) := by
  classical
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_exception_spatial_triple_sum T₀
  have hpc := pairCountConstant_pos
  refine ⟨2*512^4*Cn*pairCountConstant,by positivity,?_⟩
  intro M A P hM hP hL s T F hs hT hTT zX a b I w ha hb hI hJI hw hwP
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1≤cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if cappedRepresentative nt≤cappedRepresentative nf/16 then
      representativeExceptionSpatialCost s F zX P M A I w ![np,nt,nf,nr] a b else 0
  let D := 2*512^4*Cn*I*P^2/w
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hD : 0≤D := by dsimp [D]; positivity
  have hgb (np : ℕ) (hn : sourceRepresentative np≤P) : g np≤ENNReal.ofReal D := by
    apply (hnear M A P hM hP0 s T F hs hT hTT zX np a b I w ha hb hI hJI hw0).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_left
      (central_exception_coefficient hP (sourceRepresentative_one_le _) hn hw hwP)
      (mul_nonneg hCn hI.le)
    calc
      _=(Cn*I)*((sourceRepresentative np)^3/P^2*(512/min (sourceRepresentative np) w)^4) := by ring
      _≤(Cn*I)*(2*512^4*P^2/w) := hh
      _=D := by dsimp [D]; ring
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if cappedRepresentative nt≤cappedRepresentative n.2/16 then
        representativeExceptionSpatialCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  obtain ⟨N,hN,hidx⟩ := exists_small_pair_count hP hL
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have hsub : U⊆Finset.range N := by
    intro np hn
    have hpn : 1/sourceRepresentative np≤cappedRepresentative 0 := by
      rw [show cappedRepresentative 0=1 by rfl]
      exact (div_le_one (zero_lt_one.trans_le (sourceRepresentative_one_le _))).mpr (sourceRepresentative_one_le _)
    exact Finset.mem_range.mpr (hidx np 0 (hU np hn) hpn).1
  have hcard : (U.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
    have hh : (U.card:ℝ)≤N := by exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
    exact hh.trans hN
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal D := Finset.sum_le_sum (fun np hn=>hgb np (hU np hn))
    _=ENNReal.ofReal ((U.card:ℝ)*D) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _=>hD)]
      simp
    _≤ENNReal.ofReal ((pairCountConstant*Real.log (2+P))*D) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hD)
    _=_ := by congr 1; dsimp [D]; ring



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma Admissible.spatial_transition_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let Q := {k | k∈centralIndexSector P ∧ representativeSpatialTransition P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeSpatialCost s F zX w k a b) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hregular⟩ := hd.spatial_transition_regular_uniform T₀
  obtain ⟨Ce,hCe,hexcept⟩ := hd.spatial_exception_uniform T₀
  refine ⟨Cr+Ce,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hregular M A (zero_lt_one.trans_le hM) hA] with P hr
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsource HZ
  dsimp only
  let Q := {k | k∈centralIndexSector P ∧ representativeSpatialTransition P M A w I k}
  let fs := fun k=>representativeSpatialCost s F zX w k a b
  let fr := fun k=>if regularCentralIndex P M A I w k ∧ representativeSpatialTransition P M A w I k then fs k else 0
  let fe := fun k=>representativeExceptionSpatialCost s F zX P M A I w k a b
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let V := I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hVB : V≤B := by
    have hroot := Real.sqrt_nonneg A
    have ht : V≤(M+Real.sqrt A)*V := le_mul_of_one_le_left hV (by linarith)
    calc
      V≤(M+Real.sqrt A)*V := ht
      _≤P*Real.sqrt I+(M+Real.sqrt A)*V := le_add_of_nonneg_left (by positivity)
      _=B := by dsimp [B,V]; ring
  have hpoint (k : Fin 4→ℕ) : Q.indicator fs k≤
      (centralIndexSector P).indicator fr k+(centralIndexSector P).indicator fe k := by
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk,indicator_of_mem hk.1,indicator_of_mem hk.1]
      by_cases hreg : regularCentralIndex P M A I w k
      · have hh : regularCentralIndex P M A I w k ∧ representativeSpatialTransition P M A w I k := ⟨hreg,hk.2⟩
        change fs k ≤ (if regularCentralIndex P M A I w k ∧ representativeSpatialTransition P M A w I k then fs k else 0)+fe k
        rw [ite_eq_left hh]
        exact le_add_of_nonneg_right bot_le
      · have he : fe k=fs k := by simp [fe,fs,representativeExceptionSpatialCost,hreg]
        rw [he]
        exact le_add_of_nonneg_left bot_le
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hreg : (∑'k,(centralIndexSector P).indicator fr k)≤ENNReal.ofReal (Cr*B) := by
    rw [tsum_centralIndexSector]
    have hh := hr hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI
      (zero_lt_one.trans_le hw) hwP hsource HZ
    apply le_of_eq_of_le _ hh
    apply tsum_congr
    intro n
    by_cases hn : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1≤cappedRepresentative n.2}
    · rw [indicator_of_mem hn,indicator_of_mem hn]
      apply tsum_congr
      intro nt
      apply tsum_congr
      intro nr
      simp only [fr,fs,ite_and]
    · rw [indicator_of_notMem hn,indicator_of_notMem hn]
  have he : (∑'k,(centralIndexSector P).indicator fe k)≤ENNReal.ofReal (Ce*V) := by
    rw [tsum_centralIndexSector]
    exact hexcept M A P hM hP hL s T F hs hT hTT zX a b I w ha hb hI hJI hw hwP
  change (∑'k,Q.indicator fs k)≤ENNReal.ofReal ((Cr+Ce)*B)
  calc
    _≤∑'k,((centralIndexSector P).indicator fr k+(centralIndexSector P).indicator fe k) :=
      ENNReal.tsum_le_tsum hpoint
    _=(∑'k,(centralIndexSector P).indicator fr k)+(∑'k,(centralIndexSector P).indicator fe k) := ENNReal.tsum_add
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*V) := add_le_add hreg he
    _≤ENNReal.ofReal (Cr*B)+ENNReal.ofReal (Ce*B) :=
      add_le_add le_rfl (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hVB hCe))
    _=_ := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

lemma PhaseFlowOn.bulkRemainder_selected_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hw : 0<w)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1) :
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
      (remainderConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal 147*(∑'k : Fin 4→ℕ,(centralIndexSector P).indicator
        (fun k=>representativeCentralCost s F zX w k a b) k)+
      ENNReal.ofReal 15424*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>representativeReceiverCost s F zX w k a b (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)) k) := by
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  have hV : Measurable (fun time=>(prefixFlow F.flow T zX time).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hcover : ∀point,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T
      (bulkSelection P M A w I) (remainderConeKernel s F.flow zX) W (Icc a b) point‖≠0→
      ∃index∈Q,point∈physicalBinPhaseSet (fun time=>(prefixFlow F.flow T zX time).2)
        (representativeClosedBin T w index) (Icc a b) := by
    intro point hnonzero
    have htriangle : selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
        (remainderConeKernel s F.flow zX) W (Icc a b) point≠0 := by
      intro hzero
      exact hnonzero (by rw [hzero,norm_zero,ENNReal.ofReal_zero])
    have htime : point.1.1∈Icc a b := by
      by_contra houtside
      exact htriangle (by simp only [selectedConeTriangle,indicator_of_notMem houtside,zero_apply])
    have hdomain : point∈trianglePhaseDomain T := by
      by_contra houtside
      exact htriangle (by simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem houtside,map_zero])
    have hdensity : s.f ((triangleKernelState F.flow zX point).1.2,
        (triangleKernelState F.flow zX point).2.2)≠0 := by
      intro hzero
      apply htriangle
      simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hdomain,hzero,
        zero_smul,smul_zero,map_zero]
    have hcutoff : stateCutoff T (bulkSelection P M A w I)
        (coneCutoffState F.flow zX (triangleKernelState F.flow zX point))≠0 := by
      intro hzero
      apply htriangle
      simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hdomain,selectedConeKernel,
        hzero,zero_smul,smul_zero,map_zero]
    have hprefix : (prefixFlow F.flow T zX point.1.1).2=(F.flow zX point.1.1).2 := by
      simp only [prefixFlow,prefixClamp_eq (Icc_subset_Icc ha hb htime)]
    change stateCutoff T (bulkSelection P M A w I)
      (point.1.1-point.1.2.1,point.1.2.2.1,point.2,(F.flow zX point.1.1).2)≠0 at hcutoff
    rw [←hprefix] at hcutoff
    obtain ⟨index,hindex,hpositive⟩ := selectedDyadicCutoff_active hcutoff
    have hmomentum : 1024*q point.2≤P := hP point.1.2.1
      ⟨hdomain.2.1.le,hdomain.2.2.le.trans hdomain.1.2.le⟩
      ((triangleKernelState F.flow zX point).2.2) hdensity
    refine ⟨index,⟨bulkSelection_positive_smallSector (sphere_norm point.1.2.2)
      hmomentum hindex hpositive,hindex.2⟩,?_⟩
    exact physicalCutoff_positive_closedBin htime ⟨hdomain.2.1.le,hdomain.2.2.le⟩
      (by rw [hprefix]; exact hband _ htime) hpositive
  apply (physicalBinPhase_cover_lintegral hV measurableSet_Icc T w Q
    (F.selectedConeTriangle_measurable hs zX (bulkSelection P M A w I)
      ((F.normalised_remainder_continuousOn hs zX).mono inter_subset_left)
      hW measurableSet_Icc).norm.ennreal_ofReal hcover).trans
  rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈Q
  · rw [indicator_of_mem hk,indicator_of_mem hk,
      indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk.1)]
    exact F.bulkRemainder_bin_integral hs hT zX hw _ ha hb W hW1 k hk.1.2.2
  · rw [indicator_of_notMem hk]
    exact bot_le

lemma Admissible.bulk_remainder_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 1≤w → w≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
        (remainderConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cc,hCc,hcentral⟩ := hd.central_uniform T₀
  obtain ⟨Cr,hCr,hreceiver⟩ := hd.selected_receiver_uniform T₀
  let C := 147*Cc+15424*Cr
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hreceiver M A (zero_lt_one.trans_le hM) hA,
    eventually_ge_atTop (1:ℝ),eventually_ge_atTop (Real.exp 1)] with P hr hP he
  have hL : 1≤Real.log (2+P) := by
    calc
      1=Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _≤Real.log (2+P) := Real.log_le_log (Real.exp_pos 1) (by linarith)
  intro s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP hIP HZ hphysical hband W hW hW1
  have hc := hcentral M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only at hc
  rw [←tsum_centralIndexSector P (fun k=>representativeCentralCost s F zX w k a b)] at hc
  have hg := (F.continuous_prefixMomentumForce hs.energyPrefix hT zX).norm.measurable.ennreal_ofReal
  have hr' := hr s T F hs hT hTT zX a b I w
    (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) ha hb hw hwP hI hIP hg
    (fun _=>ENNReal.ofReal_ne_top)
  apply (F.bulkRemainder_selected_sum hs.energyPrefix hT zX (zero_lt_one.trans_le hw)
    ha hb hband hphysical hW hW1).trans
  apply (add_le_add (mul_le_mul' le_rfl hc) (mul_le_mul' le_rfl hr')).trans
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤147)]
  apply add_le_add
  · apply ENNReal.ofReal_le_ofReal
    have hB : 0≤P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w := by positivity
    dsimp [C]
    nlinarith [mul_nonneg (by positivity : 0≤15424*Cr) hB]
  · rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤15424)]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hn := Real.rpow_nonneg (zero_le_one.trans hw) (-1/2:ℝ)
    dsimp [C]
    nlinarith [mul_nonneg (by positivity : 0≤147*Cc) hn]



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma PhaseFlowOn.bulkRate_selected_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (hI : 0<I)
    {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hband : ∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) (hW1 : ∀t∈Icc a b,‖W t‖≤1) :
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
      (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal 52*(∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>representativeTimeWeightCost s F zX w I k a b) k) := by
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  have hK : ContinuousOn (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p) (coneKernelInterior T) :=
    (continuousOn_const : ContinuousOn (fun _ : ConeKernelState=>I⁻¹) (coneKernelInterior T)).smul
      ((F.normalisedRatePrimitive_continuousOn zX).mono inter_subset_left)
  have hV : Measurable (fun time=>(prefixFlow F.flow T zX time).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hcover : ∀point,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T
      (bulkSelection P M A w I) (fun state=>I⁻¹ • normalisedRatePrimitive F.flow zX state)
      W (Icc a b) point‖≠0→
      ∃index∈Q,point∈physicalBinPhaseSet (fun time=>(prefixFlow F.flow T zX time).2)
        (representativeClosedBin T w index) (Icc a b) := by
    intro point hnonzero
    have htriangle : selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
        (fun state=>I⁻¹ • normalisedRatePrimitive F.flow zX state) W (Icc a b) point≠0 := by
      intro hzero
      exact hnonzero (by rw [hzero,norm_zero,ENNReal.ofReal_zero])
    have htime : point.1.1∈Icc a b := by
      by_contra houtside
      exact htriangle (by simp only [selectedConeTriangle,indicator_of_notMem houtside,zero_apply])
    have hdomain : point∈trianglePhaseDomain T := by
      by_contra houtside
      exact htriangle (by simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem houtside,map_zero])
    have hdensity : s.f ((triangleKernelState F.flow zX point).1.2,
        (triangleKernelState F.flow zX point).2.2)≠0 := by
      intro hzero
      apply htriangle
      simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hdomain,hzero,
        zero_smul,smul_zero,map_zero]
    have hcutoff : stateCutoff T (bulkSelection P M A w I)
        (coneCutoffState F.flow zX (triangleKernelState F.flow zX point))≠0 := by
      intro hzero
      apply htriangle
      simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hdomain,selectedConeKernel,
        hzero,zero_smul,smul_zero,map_zero]
    have hprefix : (prefixFlow F.flow T zX point.1.1).2=(F.flow zX point.1.1).2 := by
      simp only [prefixFlow,prefixClamp_eq (Icc_subset_Icc ha hb htime)]
    change stateCutoff T (bulkSelection P M A w I)
      (point.1.1-point.1.2.1,point.1.2.2.1,point.2,(F.flow zX point.1.1).2)≠0 at hcutoff
    rw [←hprefix] at hcutoff
    obtain ⟨index,hindex,hpositive⟩ := selectedDyadicCutoff_active hcutoff
    have hmomentum : 1024*q point.2≤P := hP point.1.2.1
      ⟨hdomain.2.1.le,hdomain.2.2.le.trans hdomain.1.2.le⟩
      ((triangleKernelState F.flow zX point).2.2) hdensity
    refine ⟨index,⟨bulkSelection_positive_smallSector (sphere_norm point.1.2.2)
      hmomentum hindex hpositive,hindex.2⟩,?_⟩
    exact physicalCutoff_positive_closedBin htime ⟨hdomain.2.1.le,hdomain.2.2.le⟩
      (by rw [hprefix]; exact hband _ htime) hpositive
  apply (physicalBinPhase_cover_lintegral hV measurableSet_Icc T w Q
    (F.selectedConeTriangle_measurable hs zX (bulkSelection P M A w I)
      hK hW measurableSet_Icc).norm.ennreal_ofReal hcover).trans
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈Q
  · rw [indicator_of_mem hk,indicator_of_mem hk]
    exact F.bulkRate_bin_integral hs hT zX hI _ ha hb W hW1 k hk.1.2.2
  · rw [indicator_of_notMem hk,indicator_of_notMem hk,mul_zero]

lemma Admissible.bulk_rate_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → b-a≤I → 1≤w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
        (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Ct,hCt,htime⟩ := hd.selected_time_weight_uniform T₀
  refine ⟨52*Ct,by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP HZ hphysical hband W hW hW1
  apply (F.bulkRate_selected_sum hs.energyPrefix hT zX hI ha hb hband hphysical hW hW1).trans
  apply (mul_le_mul' le_rfl (htime M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP HZ)).trans
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤52)]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

end RVM

end

end OAI
