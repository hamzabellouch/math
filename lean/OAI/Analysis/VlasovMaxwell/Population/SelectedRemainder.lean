import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates
import OAI.Analysis.VlasovMaxwell.Population.MagneticEstimates
import OAI.Analysis.VlasovMaxwell.Population.BulkSpatialUniform
import OAI.Analysis.VlasovMaxwell.Population.BulkReceiverScalar

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma bulkSelection_derivative_selected_cover {T P M A w I t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec}
    (hP : 1024*q v≤P) (H : CutoffState)
    (hd : fderiv ℝ (stateCutoff T (bulkSelection P M A w I)) (t-σ,n.1,v,V t) H≠0) :
    ∃k∈representativeSmallSector P,representativeSelected P M A w I k ∧
      ((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ≤ max 1 T := by linarith [hσ.1,le_max_right (1:ℝ) T]
  obtain ⟨j,hj,_,_,hjp,_,_⟩ := stateCutoff_partial_boundary
    (z:=(t-σ,n.1,v,V t)) (bulkSelection P M A w I) hr hrT (sphere_norm n) H hd
  exact ⟨j,bulkSelection_positive_smallSector (sphere_norm n) hP hj hjp,hj.2,
    physicalCutoff_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hjp⟩

lemma PhaseFlowOn.bulkCutoffTriangle_selected_support {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    (H : ConeKernelState→CutoffState) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : partialCutoffTriangle s F.flow zX T (bulkSelection P M A w I) H W J p≠0) :
    ∃k∈representativeSmallSector P,representativeSelected P M A w I k ∧
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J := by
  obtain ⟨ht,htT,hσ,hb,hv,hd⟩ := F.partialCutoffTriangle_physical_nonzero zX
    (bulkSelection P M A w I) H W hJT hband hP hp
  exact bulkSelection_derivative_selected_cover (P:=P) (M:=M) (A:=A) (w:=w) (I:=I)
    (V:=fun t=>(prefixFlow F.flow T zX t).2) (n:=p.1.2.2) ht htT hσ hb hv _ hd

lemma selectedConeTriangle_nonzero_data {s : Solution} {α : Phase→ℝ→Phase}
    {zX : Phase} {T : ℝ} {Q : Set (Fin 4→ℕ)} {A : ConeKernelState→Vec}
    {W : ℝ→Vec→L[ℝ]Vec} {J : Set ℝ} {p : TrianglePhase}
    (hp : selectedConeTriangle s α zX T Q A W J p≠0) :
    p.1.1∈J ∧ p∈trianglePhaseDomain T ∧
      s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2)≠0 ∧
      stateCutoff T Q (coneCutoffState α zX (triangleKernelState α zX p))≠0 := by
  have ht : p.1.1∈J := by
    by_contra hh
    exact hp (by simp only [selectedConeTriangle,indicator_of_notMem hh,zero_apply])
  have hc : p∈trianglePhaseDomain T := by
    by_contra hh
    exact hp (by simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem hh,map_zero])
  refine ⟨ht,hc,?_,?_⟩
  · intro hh
    apply hp
    simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hc,hh,zero_smul,smul_zero,map_zero]
  · intro hh
    apply hp
    simp only [selectedConeTriangle,triangleConeKernel,indicator_of_mem hc,selectedConeKernel,hh,
      zero_smul,smul_zero,map_zero]

lemma bulkSelection_cutoff_physical_cover {T P M A w I t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec}
    (hP : 1024*q v≤P)
    (hc : stateCutoff T (bulkSelection P M A w I) (t-σ,n.1,v,V t)≠0) :
    ∃k∈representativeSmallSector P,representativeSelected P M A w I k ∧
      ((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  obtain ⟨k,hk,hpos⟩ := selectedDyadicCutoff_active hc
  exact ⟨k,bulkSelection_positive_smallSector (sphere_norm n) hP hk hpos,hk.2,
    physicalCutoff_positive_closedBin ht hσ hband hpos⟩

lemma PhaseFlowOn.selectedConeTriangle_physical_nonzero {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (K : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : selectedConeTriangle s F.flow zX T Q K W J p≠0) :
    p.1.1∈J ∧ p.1.2.1∈Icc 0 p.1.1 ∧
      q (prefixFlow F.flow T zX p.1.1).2∈Icc (w/8) (8*w) ∧ 1024*q p.2≤P ∧
      stateCutoff T Q (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(prefixFlow F.flow T zX p.1.1).2)≠0 := by
  obtain ⟨ht,hc,hf,hcut⟩ := selectedConeTriangle_nonzero_data hp
  have he : (prefixFlow F.flow T zX p.1.1).2=(F.flow zX p.1.1).2 := by
    simp only [prefixFlow,prefixClamp_eq (hJT ht)]
  refine ⟨ht,⟨hc.2.1.le,hc.2.2.le⟩,?_,?_,?_⟩
  · rw [he]; exact hband _ ht
  · exact hP p.1.2.1 ⟨hc.2.1.le,hc.2.2.le.trans hc.1.2.le⟩
      ((triangleKernelState F.flow zX p).2.2) hf
  · rw [he]; exact hcut

lemma PhaseFlowOn.bulkSelectedCone_support {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (K : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : selectedConeTriangle s F.flow zX T (bulkSelection P M A w I) K W J p≠0) :
    ∃k∈representativeSmallSector P,representativeSelected P M A w I k ∧
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J := by
  obtain ⟨ht,hσ,hb,hv,hc⟩ := F.selectedConeTriangle_physical_nonzero zX
    (bulkSelection P M A w I) K W hJT hband hP hp
  exact bulkSelection_cutoff_physical_cover (P:=P) (M:=M) (A:=A) (w:=w) (I:=I)
    (V:=fun t=>(prefixFlow F.flow T zX t).2) (n:=p.1.2.2) ht hσ hb hv hc

lemma selectedConeTriangle_contract_norm_le {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} {p : TrianglePhase} (ht : p.1.1∈J) (hp : p∈trianglePhaseDomain T)
    (hW : ‖W p.1.1‖≤1) :
    ‖selectedConeTriangle s α zX T Q A W J p‖≤
      ‖(s.f ((triangleKernelState α zX p).1.2,(triangleKernelState α zX p).2.2)*
        (1-dot p.1.2.2.1 (velocity (α zX p.1.1).2))) • A (triangleKernelState α zX p)‖ := by
  apply (selectedConeTriangle_norm_le Q A W J p).trans
  rw [indicator_of_mem ht]
  apply ((W p.1.1).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_right hW (norm_nonneg _)).trans
  rw [one_mul,triangleConeKernel,indicator_of_mem hp,smul_smul,mul_comm]

lemma PhaseFlowOn.bulkSelectedCone_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {K : ConeKernelState→Vec} (hK : ContinuousOn K (coneKernelInterior T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) :
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I) K W J p‖ ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}).indicator
        (fun k=>∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
          (velocity (prefixFlow F.flow T zX z.1).2),
            ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I) K W J (z,v)‖
            ∂volume ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  apply physicalBinPhase_cover_lintegral hV hJ T w Q
    (F.selectedConeTriangle_measurable hs zX (bulkSelection P M A w I) hK hW hJ).norm.ennreal_ofReal
  intro p hp
  have hpn : selectedConeTriangle s F.flow zX T (bulkSelection P M A w I) K W J p≠0 := by
    intro hh
    exact hp (by rw [hh,norm_zero,ENNReal.ofReal_zero])
  obtain ⟨k,hk,hr,hpk⟩ := F.bulkSelectedCone_support zX K W hJT hband hP hpn
  exact ⟨k,⟨hk,hr⟩,hpk⟩

lemma velocity_bin_normal_bound {v n : Vec} {θ : ℝ} (hn : ‖n‖=1)
    (hθ : 0≤θ) (hd : 1-dot n (velocity v)≤8*θ^2) : ‖velocity v-n‖≤4*θ := by
  apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le hn.le (by positivity)
  rw [dot_comm]
  nlinarith

lemma unprojected_remainder_bin_cost {r f θ φ w : ℝ} {n v W K : Vec}
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f) (hθ : 0<θ) (hφ : 0<φ) (hw : 0<w)
    (hsmall : θ≤φ/16) (hd : 1-dot n (velocity v)∈Icc (θ^2/2) (8*θ^2))
    (hD : 1-dot n (velocity W)∈Icc (φ^2/2) (8*φ^2)) (hq : w/8≤q W) :
    ‖(f*(1-dot n (velocity W))) •
      normalisedRemainder r (velocity W) (velocity v) n (fderiv ℝ velocity W K)‖≤
      147*f+15424*(θ/(w*φ^2))*‖K‖*r*f := by
  have hsmall' : θ≤φ := by linarith
  have hun := velocity_bin_normal_bound hn hθ.le hd.2
  have han := velocity_bin_normal_bound hn hφ.le hD.2
  have he := small_deficit_difference hn hθ.le hφ.le hsmall'
    (cone_denom_pos v n hn).le hd.2 hun han
  have hb := signedRemainder_small_norm W K (velocity v) n hr hf hn hθ.le hφ hsmall'
    hD.1 hD.2 hun he
  have hq' : ‖K‖/q W≤8*‖K‖/w := by
    calc
      _≤‖K‖/(w/8) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hq
      _=_ := by ring
  rw [normalisedRemainder_eq _ _ _ _ hr.ne',smul_comm (f*(1-dot n (velocity W))),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
  calc
    _≤r^2*(147*f/r^2+1928*f*θ*(‖K‖/q W)/(r*φ^2)) := mul_le_mul_of_nonneg_left hb (sq_nonneg r)
    _≤r^2*(147*f/r^2+1928*f*θ*(8*‖K‖/w)/(r*φ^2)) := by gcongr
    _=_ := by field_simp; ring

lemma unprojected_rate_bin_cost {r f θ φ I : ℝ} {n v W : Vec}
    (hn : ‖n‖=1) (hr : 0<r) (hf : 0≤f) (hθ : 0<θ) (hφ : 0<φ) (hφ1 : φ≤1) (hI : 0<I)
    (hsmall : θ≤φ/16) (hd : 1-dot n (velocity v)∈Icc (θ^2/2) (8*θ^2))
    (hD : 1-dot n (velocity W)∈Icc (φ^2/2) (8*φ^2)) :
    ‖(f*(1-dot n (velocity W))) •
      (I⁻¹ • (((1-dot n (velocity v))/(1-dot n (velocity W))) •
        normalisedPrimitive r (velocity W) (velocity v) n))‖≤52*(θ/(I*φ))*r*f := by
  have hsmall' : θ≤φ := by linarith
  have hun := velocity_bin_normal_bound hn hθ.le hd.2
  have han := velocity_bin_normal_bound hn hφ.le hD.2
  have he := small_deficit_difference hn hθ.le hφ.le hsmall'
    (cone_denom_pos v n hn).le hd.2 hun han
  have hb := small_primitive_norm hn hθ.le hφ hφ1 hD.1 hun he
  have hd0 := (cone_denom_pos v n hn).ne'
  have hD0 := (cone_denom_pos W n hn).ne'
  have heq : (f*(1-dot n (velocity W)))*I⁻¹*
      ((1-dot n (velocity v))/(1-dot n (velocity W)))*(r/(1-dot n (velocity v)))=f*r/I := by field_simp
  simp only [normalisedPrimitive,smul_smul]
  rw [show (f*(1-dot n (velocity W)))*(I⁻¹*((1-dot n (velocity v))/(1-dot n (velocity W))*(r/(1-dot n (velocity v)))))=f*r/I by
    convert heq using 1; ring]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤f*r/I)]
  calc
    _≤(f*r/I)*(52*θ/φ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _=_ := by ring

lemma PhaseFlowOn.bulkRemainder_pointwise {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (hw : 0<w)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) {v : Vec}
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2)) :
    ‖selectedConeTriangle s F.flow zX T Q (remainderConeKernel s F.flow zX) W J (z,v)‖≤
      147*s.f (z.2.1,((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))+
        15424*(cappedRepresentative (k 1)/(w*(cappedRepresentative (k 2))^2))*
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
    apply (selectedConeTriangle_contract_norm_le Q (remainderConeKernel s F.flow zX) W hz.1 hp (hW _ hz.1)).trans
    simpa only [triangleKernelState,remainderConeKernel,phaseAcceleration,lorentzField,lorentzPhase] using
      unprojected_remainder_bin_cost (sphere_norm z.2.2) (sub_pos.mpr hp.2.2)
        (by simpa only [heq] using hf) hθ hφ hw hsmall hv.2.1 hD hq
  · simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero]
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    positivity

lemma PhaseFlowOn.bulkRate_pointwise {s : Solution} {T w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (hI : 0<I)
    (Q : Set (Fin 4→ℕ)) {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16)
    {z : ConeCoordinate} (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J) {v : Vec}
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2)) :
    ‖selectedConeTriangle s F.flow zX T Q (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p) W J (z,v)‖≤
      52*(cappedRepresentative (k 1)/(I*cappedRepresentative (k 2)))*(z.1-z.2.1)*
        s.f (z.2.1,((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hφ := cappedRepresentative_pos (k 2)
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
    apply (selectedConeTriangle_contract_norm_le Q (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p) W hz.1 hp (hW _ hz.1)).trans
    simpa only [triangleKernelState,normalisedRatePrimitive] using
      unprojected_rate_bin_cost (sphere_norm z.2.2) (sub_pos.mpr hp.2.2)
        (by simpa only [heq] using hf) hθ hφ (cappedRepresentative_le_one _) hI hsmall hv.2.1 hD
  · simp only [selectedConeTriangle,triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero]
    have hr : 0≤z.1-z.2.1 := sub_nonneg.mpr hz.2.1.2
    positivity

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.bulk_selected_family_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤w → w≤P → I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T (bulkSelection P M A w I)
        ((Icc a b).indicator W) p)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cs,hCs,hsource⟩ := hd.bulk_source_uniform T₀
  obtain ⟨Cg,hCg,hgeometry⟩ := hd.bulk_geometry_uniform T₀
  obtain ⟨Cr,hCr,hreceiver⟩ := hd.bulk_receiver_uniform T₀
  obtain ⟨Cb,hCb,hremainder⟩ := hd.bulk_remainder_uniform T₀
  let C := Cs+Cg+Cr+Cb
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hsource M A hM hA,hgeometry M A hM hA,
    hreceiver M A (zero_lt_one.trans_le hM) hA,hremainder M A hM hA] with P hso hge hre hrm
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ W hW hW1
  let Q := bulkSelection P M A w I
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
  let V := (Icc a b).indicator W
  have hV : Measurable V := hW.indicator measurableSet_Icc
  have hB : 0≤B := by dsimp [B]; positivity
  have hsc := hso hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsrc hphysical hband HZ W hW hW1
  have hgc := hge hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP hsrc hphysical hband HZ W hW hW1
  have hrc := hre s T F hs hT hTT zX a b I w ha hb hw hwP hI hIP hphysical hband W hW hW1
  have hbc := hrm s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP hIP HZ hphysical hband W hW hW1
  have htr (H : ConeKernelState→CutoffState) (hH : ContinuousOn H (coneKernelInterior T)) :=
    F.partialCutoffLabelCost_triangle (J:=Icc a b) hs.energyPrefix hT zX Q hH hW measurableSet_Icc
  have hts := htr _ (F.coneSourceCutoffTangent_continuousOn hs.energyPrefix zX)
  have htg := htr _ (F.coneGeometryCutoffTangent_continuousOn hs.energyPrefix zX)
  have htrc := htr _ (F.coneReceiverCutoffTangent_continuousOn hs.energyPrefix zX)
  rw [coneSourceCutoffTangent_pullback] at hts
  rw [coneGeometryCutoffTangent_pullback] at htg
  rw [coneReceiverCutoffTangent_pullback] at htrc
  have hcut := F.cutoff_label_integral_split hs.energyPrefix zX Q hV
  dsimp only [V] at hcut
  rw [hts,htg,htrc] at hcut
  have hcut' := hcut.trans (add_le_add (add_le_add hsc hgc) hrc)
  have hrem : (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖V (labelReceiverTime F.flow zX T p)
        (labelSelectedCutoff F.flow zX T Q p • actualLabelRemainder s F.flow zX T p)‖)≤
      ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K := by
    rw [F.actualLabelRemainder_eq_normalised zX]
    change (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T (remainderConeKernel s F.flow zX) p)‖)≤_
    have ht := F.selectedConeTriangle_norm_transfer (J:=Icc a b) (A:=remainderConeKernel s F.flow zX)
      hs.energyPrefix hT zX Q
      ((F.normalised_remainder_continuousOn hs.energyPrefix zX).mono inter_subset_left) hW measurableSet_Icc
    exact ht.le.trans hbc
  have hmeas := (measurable_vec_clm_apply (hV.comp (F.labelReceiverTime_measurable zX))
    (F.actualLabelCutoffCost_measurable hs.energyPrefix zX Q)).norm.ennreal_ofReal
  change Measurable (fun x=>ENNReal.ofReal ‖V (labelReceiverTime F.flow zX T x)
    (actualLabelCutoffCost s F.flow zX T Q x)‖) at hmeas
  change (∫⁻p : ℝ×Phase,selectedMultiplierBulkDensity s F.flow zX T Q V p)≤_
  simp only [selectedMultiplierBulkDensity]
  rw [lintegral_add_left hmeas]
  apply (add_le_add hcut' hrem).trans
  have heq : (ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cg*B)+ENNReal.ofReal (Cr*w^(-1/2:ℝ))*K)+
      (ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K)=
      ENNReal.ofReal ((Cs+Cg+Cb)*B)+ENNReal.ofReal ((Cr+Cb)*w^(-1/2:ℝ))*K := by
    rw [add_mul,add_mul,add_mul,ENNReal.ofReal_add (add_nonneg (mul_nonneg hCs hB) (mul_nonneg hCg hB)) (mul_nonneg hCb hB),
      ENNReal.ofReal_add (mul_nonneg hCs hB) (mul_nonneg hCg hB),
      ENNReal.ofReal_add (by positivity : 0≤Cr*w^(-1/2:ℝ)) (by positivity : 0≤Cb*w^(-1/2:ℝ)),add_mul]
    ring
  change (ENNReal.ofReal (Cs*B)+ENNReal.ofReal (Cg*B)+ENNReal.ofReal (Cr*w^(-1/2:ℝ))*K)+
      (ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K)≤_
  rw [heq]
  apply add_le_add
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hB
  · apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.rpow_nonneg (zero_le_one.trans hw) _)

end RVM

end

end OAI
