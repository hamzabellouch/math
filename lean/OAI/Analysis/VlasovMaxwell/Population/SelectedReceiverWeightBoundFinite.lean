import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RepresentativeCosts

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.selected_receiver_weight_bound_finite_sources {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularMultiplierCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t|)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
  classical
  obtain ⟨C,hC,hnear⟩ := hd.label_projected_primitive_near_constant
  refine ⟨32*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w N Q hQ hJ hJT hw hband hv b hb hbJ
  let G := prefixAngularMultiplier s F.flow T w hw zX
  let W := ∫⁻t in J,ENNReal.ofReal |b t|
  have hG := (F.prefixAngular_regular hs hT hw zX).1
  have hGe : ∀t∈J,G t=angularMultiplierCLM w (F.flow zX t).2 :=
    fun t ht=>(prefixAngular_highband (s:=s) hw zX (hJT ht) (hv t ht)).1
  have h0abs : ∀t∉J,|b t|=0 := fun t ht=>by rw [hbJ t ht,abs_zero]
  have hbnorm (k : Fin 4→ℕ) : Measurable (fun p : ℝ×Phase=>
      ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) :=
    ((hb.comp (F.labelReceiverTime_measurable zX)).norm.ennreal_ofReal).mul
      ((F.measurable_labelConeKernel hs zX (F.projectedDyadicRateKernel_continuousOn zX k hG)).norm.ennreal_ofReal)
  have hbound (k : Fin 4→ℕ) (hk : k∈Q) :
      (∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖)≤
      W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T))*ENNReal.ofReal (directionWeightMajorant N k)) := by
    have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    have he : (∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖)=
      ∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k (fun t=>angularMultiplierCLM w (F.flow zX t).2)) p‖ := by
      apply lintegral_congr
      intro p
      exact weighted_labelProjected_congr s F.flow zX T k (fun t ht=>hGe t ht) h0abs p
    rw [he]
    have hn := hnear s T F hs hT h0 zX J w (sourceRepresentative (k 0))
      (cappedRepresentative (k 1)) (cappedRepresentative (k 2)) k hJ hJT hw hp.le (hc 1).le (hc 2)
      (hQ k hk).2.2.1 le_rfl le_rfl le_rfl (by
        change sourceRepresentative (k 0)/32 ≤ sourceRepresentative (k 0)
        linarith) hband hv (fun t=>|b t|) hb.norm h0abs
    refine hn.trans (mul_le_mul' (a:=W) (b:=W) le_rfl ?_)
    rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T))]
    exact ENNReal.ofReal_le_ofReal
      (selected_representative_weight_bound hC (hQ k hk).1 (hQ k hk).2.1 (hQ k hk).2.2.2 w)
  calc
    _ = ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖ := by
      apply lintegral_congr
      intro p
      by_cases ht : labelReceiverTime F.flow zX T p∈J
      · rw [hGe _ ht]
      · simp only [labelWeight,hbJ _ ht,zero_mul,zero_smul,map_zero]
    _ = ∫⁻p : ℝ×Phase,∑'k : Fin 4→ℕ,Q.indicator (fun k=>
        ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
          ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
      apply lintegral_congr
      intro p
      exact F.selected_receiver_rate_norm_sum s zX Q b G p
    _ = ∑'k : Fin 4→ℕ,∫⁻p : ℝ×Phase,Q.indicator (fun k=>
        ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
          ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
      apply lintegral_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using (hbnorm k).aemeasurable
      · simp only [indicator_of_notMem hk]
        exact aemeasurable_const
    _ ≤ ∑'k : Fin 4→ℕ,W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T))*
        ENNReal.ofReal (directionWeightMajorant N k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using hbound k hk
      · simp only [indicator_of_notMem hk,lintegral_zero]
        exact bot_le
    _ = W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T))*
        ∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k)) := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T))*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      mul_le_mul' (a:=W) (b:=W) le_rfl (mul_le_mul' (a:=ENNReal.ofReal (4*C*Real.sqrt (max 1 T)))
        (b:=ENNReal.ofReal (4*C*Real.sqrt (max 1 T))) le_rfl (tsum_directionWeightMajorant N))
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T))]
      congr 2
      ring

lemma source_angle_coordinate_lower (v n : Vec) (hn : ‖n‖=1) :
    1/2≤q v*Real.sqrt ((1-dot n (velocity v))/2) := by
  have hq := q_pos v
  have hv := norm_velocity_lt_one v
  have hdot := dot_le_norm n (velocity v)
  rw [hn,one_mul] at hdot
  have hs := velocity_self v
  rw [dot_self] at hs
  have hinv : (q v)^2*((q v)⁻¹)^2=1 := by field_simp
  have hd : ((q v)⁻¹)^2≤2*(1-dot n (velocity v)) := by
    nlinarith [sq_nonneg (1-‖velocity v‖)]
  have hdq := mul_le_mul_of_nonneg_left hd (sq_nonneg (q v))
  rw [hinv] at hdq
  have hroot := Real.sq_sqrt (div_nonneg (cone_denom_pos v n hn).le (by norm_num : (0:ℝ)≤2))
  have hp : 0≤q v*Real.sqrt ((1-dot n (velocity v))/2) := by positivity
  have hsq : 1≤4*(q v*Real.sqrt ((1-dot n (velocity v))/2))^2 := by
    nlinarith [sq_nonneg (q v)]
  nlinarith

lemma source_energy_index_lt {n N : ℕ} {v : Vec}
    (h : DyadicBand n (1/q v)) (hP : 1024*q v≤(2:ℝ)^N) : n<N := by
  by_contra hc
  have hn : N≤n := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hr := (dyadicBand_source_range h).1
  dsimp [sourceRepresentative] at hr
  nlinarith [q_pos v]

lemma source_angle_index_lt {n N : ℕ} {v nu : Vec} (hnu : ‖nu‖=1)
    (h : DyadicBand n (Real.sqrt ((1-dot nu (velocity v))/2)))
    (hP : 1024*q v≤(2:ℝ)^N) : n<N := by
  by_contra hc
  have hn : N≤n := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hm := mul_le_mul_of_nonneg_right (hP.trans hpow)
    (Real.sqrt_nonneg ((1-dot nu (velocity v))/2))
  have hl := source_angle_coordinate_lower v nu hnu
  nlinarith [h.2]

lemma physicalCutoff_positive_source_indices {T r : ℝ} {v w n : Vec} {k : Fin 4→ℕ} {N : ℕ}
    (hn : ‖n‖=1) (hP : 1024*q v≤(2:ℝ)^N)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v w)) :
    k 0<N ∧ k 1<N := by
  have hb := dyadicMultiFactor_positive_bands hk
  exact ⟨source_energy_index_lt (hb 0) hP,source_angle_index_lt hn (hb 1) hP⟩

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_restrict {ι : Type*} [Fintype ι] (Q R : Set (ι→ℕ))
    (x : ι→ℝ) (hR : ∀k,dyadicMultiFactor k x≠0→k∈R) :
    selectedDyadicCutoff Q x=selectedDyadicCutoff (Q∩R) x := by
  classical
  apply tsum_congr
  intro k
  by_cases hk : k∈R
  · by_cases hQ : k∈Q
    · simp only [indicator_of_mem hQ,indicator_of_mem (show k∈Q∩R from ⟨hQ,hk⟩)]
    · simp only [indicator_of_notMem hQ,indicator_of_notMem (show k∉Q∩R from fun h=>hQ h.1)]
  · have hz : dyadicMultiFactor k x=0 := by by_contra hc; exact hk (hR k hc)
    by_cases hQ : k∈Q
    · simp only [indicator_of_mem hQ,indicator_of_notMem (show k∉Q∩R from fun h=>hk h.2),hz]
    · simp only [indicator_of_notMem hQ,indicator_of_notMem (show k∉Q∩R from fun h=>hQ h.1)]

lemma PhaseFlowOn.labelWeight_rate_source_truncate {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase) (N : ℕ)
    (hP : ∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N)
    (Q : Set (Fin 4→ℕ)) (b : ℝ→ℝ) (p : ℝ×Phase) :
    labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p=
      labelWeight F.flow zX T (Q∩{k | k 0<N ∧ k 1<N}) b p • actualLabelRatePrimitive s F.flow zX T p := by
  classical
  by_cases hf : s.f (0,p.2)=0
  · rw [F.actualLabelRatePrimitive_eq s zX]
    by_cases hp : p∈labelBranchDomain F.flow zX T
    · simp only [labelConeKernel,indicator_of_mem hp,hf,zero_smul,smul_zero]
    · simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have he : selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX p.2 p.1)=
        selectedDyadicCutoff (Q∩{k | k 0<N ∧ k 1<N}) (actualCutoffCoordinates F.flow T zX p.2 p.1) := by
      apply selectedDyadicCutoff_restrict
      intro k hk
      exact physicalCutoff_positive_source_indices (F.branchDirection_norm zX p.2 hp.1 hp.2)
        (hP p.2 hf p.1 (Ioo_subset_Icc_self hp.1.1))
        (lt_of_le_of_ne (dyadicMultiFactor_nonneg _ _) (Ne.symm hk))
    have hj : p∈jointBranchDomain F.flow zX T := hp
    simp only [labelWeight,labelSelectedCutoff,indicator_of_mem hj,he]
  · rw [F.actualLabelRatePrimitive_eq s zX]
    simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]

lemma Admissible.selected_receiver_weight_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularMultiplierCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t|)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_receiver_weight_bound_finite_sources
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv b hbm hbJ
  have he : (fun p : ℝ×Phase=>labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)=
      fun p : ℝ×Phase=>labelWeight F.flow zX T (Q∩{k | k 0<N ∧ k 1<N}) b p • actualLabelRatePrimitive s F.flow zX T p :=
    funext (F.labelWeight_rate_source_truncate s zX N hP Q b)
  simp_rw [congr_fun he]
  exact hb s T F hs hT h0 zX J w N _ (fun k hk=>⟨hk.2.1,hk.2.2,hQ k hk.1⟩)
    hJ hJT hw hband hv b hbm hbJ

def physicalDyadicMovingDensity (s : Solution) (X V K : ℝ→Vec) (T w : ℝ)
    (k : Fin 4→ℕ) (z : ConeCoordinate) : ℝ≥0∞ :=
  ∫⁻v : Vec, ENNReal.ofReal (dyadicMultiFactor k
    (physicalCutoffCoordinates T (z.1-z.2.1) z.2.2.1 v (V z.1))*(z.1-z.2.1)*
      ‖s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)) •
        angularDerivativeCLM w (V z.1) (K z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖)

lemma physicalDyadicMovingDensity_le {s : Solution} {X V K : ℝ→Vec} {T w t σ : ℝ}
    {k : Fin 4→ℕ} {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hσt : σ<t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (n : Sphere) :
    physicalDyadicMovingDensity s X V K T w k (t,σ,n) ≤
      (physicalBinBase V (representativeClosedBin T w k) J).indicator
        (physicalMovingProjectorDensity s X V (representativeClosedBin T w k) w K) (t,σ,n) := by
  classical
  let B := representativeClosedBin T w k
  let χ : Vec→ℝ := fun v=>dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))
  let H : Vec→ℝ := fun v=>‖s.f (σ,(X t-(t-σ) • n.1,v)) •
    angularDerivativeCLM w (V t) (K t) (signedPrimitive (velocity (V t)) (velocity v) n.1)‖
  have hp : ∀v, ENNReal.ofReal (χ v*(t-σ)*H v) ≤
      (coneBinMomentumSet B n.1 (velocity (V t))).indicator
        (fun v=>ENNReal.ofReal ((t-σ)*H v)) v := by
    intro v
    by_cases hχ : 0<χ v
    · have hv := (physicalCutoff_positive_closedBin ht hσ hband hχ).2
      rw [indicator_of_mem hv]
      apply ENNReal.ofReal_le_ofReal
      have hm := dyadicMultiFactor_le_one k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))
      have hrH : 0≤(t-σ)*H v := mul_nonneg (sub_nonneg.mpr hσt.le) (norm_nonneg _)
      have hm' := mul_le_mul_of_nonneg_right hm hrH
      dsimp [χ] at *
      nlinarith
    · have hz : χ v=0 := le_antisymm (le_of_not_gt hχ) (dyadicMultiFactor_nonneg _ _)
      simp only [hz,zero_mul,ENNReal.ofReal_zero]
      exact bot_le
  by_cases hbase : (t,σ,n)∈physicalBinBase V B J
  · rw [indicator_of_mem hbase]
    calc
      _ ≤ ∫⁻v, (coneBinMomentumSet B n.1 (velocity (V t))).indicator
          (fun v=>ENNReal.ofReal ((t-σ)*H v)) v := lintegral_mono hp
      _ = ∫⁻v in coneBinMomentumSet B n.1 (velocity (V t)), ENNReal.ofReal ((t-σ)*H v) :=
        lintegral_indicator (measurableSet_coneBinMomentumSet _ _ _) _
      _ = _ := by
        simp only [H,physicalPrimitive_radius_norm (sub_pos.mpr hσt)]
        simp_rw [ENNReal.ofReal_mul (sq_nonneg (t-σ))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [indicator_of_notMem hbase]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro v
    have hχ : χ v=0 := by
      apply le_antisymm _ (dyadicMultiFactor_nonneg _ _)
      exact le_of_not_gt (fun h=>hbase (physicalCutoff_positive_closedBin ht hσ hband h).1)
    change ENNReal.ofReal (χ v*(t-σ)*H v)=0
    simp only [hχ,zero_mul,ENNReal.ofReal_zero]

lemma physicalDyadicMovingDensity_near_pointwise {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {X V K : ℝ→Vec} {J : Set ℝ} (hJT : J⊆Icc 0 T)
    {w C p θ φ t σ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (_hC : 0≤C) (_hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (ht : t∈J) (hσ : σ∈Icc 0 t) (hσt : σ<t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (hv : w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V (representativeClosedBin T w k) J,
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
        ENNReal.ofReal (128*C*p^3*θ^2)) (n : Sphere) :
    physicalDyadicMovingDensity s X V K T w k (t,σ,n)≤
      (physicalBinBase V (representativeClosedBin T w k) J).indicator
        (fun z=>ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (5111808*C*(p*θ)^3*
          (representativeClosedBin T w k).rmax/(w*φ))) (t,σ,n) := by
  classical
  let B := representativeClosedBin T w k
  have h := physicalDyadicMovingDensity_le ht hσ hσt hband n (s:=s) (X:=X) (K:=K) (k:=k) (T:=T)
  by_cases hz : (t,σ,n)∈physicalBinBase V B J
  · rw [indicator_of_mem hz] at h ⊢
    have hk := physicalMovingProjectorDensity_bound (s:=s) (X:=X) (z:=(t,σ,n)) (K:=K)
      hw hv (sub_pos.mpr hσt) hθ hφ hφ1 hsmall hd (hDlo.trans hz.2.2.2.2.1)
      (hz.2.2.2.2.2.trans hDhi)
      (fun v=>hs.nonnegative σ ⟨hσ.1,hσ.2.trans (hJT ht).2⟩ _)
    have hn : 0≤B.rmax := (representativeClosedBin_radius_pos T w k).le.trans
      (hz.2.2.1.1.trans hz.2.2.1.2)
    have hden := hdensity (t,σ,n) hz
    have hrad : ENNReal.ofReal (t-σ)≤ENNReal.ofReal B.rmax :=
      ENNReal.ofReal_le_ofReal hz.2.2.1.2
    calc
      _ ≤ ENNReal.ofReal (39936*θ/(w*φ)*‖K t‖)*ENNReal.ofReal (t-σ)*
          physicalBinDensity s X V B t σ n := h.trans hk
      _ ≤ ENNReal.ofReal (39936*θ/(w*φ)*‖K t‖)*ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2) :=
        mul_le_mul' (mul_le_mul' le_rfl hrad) hden
      _ = _ := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ)*‖K t‖),
          ←ENNReal.ofReal_mul (mul_nonneg (by positivity) hn),
          ←ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        dsimp [B]
        ring
  · exact (h.trans (by rw [indicator_of_notMem hz,indicator_of_notMem hz]))

lemma physicalDyadicMoving_triangle_near {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {X V K : ℝ→Vec} (hV : Measurable V) (hK : Measurable K)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w)) (hv : ∀t∈J,w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V (representativeClosedBin T w k) J,
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
        ENNReal.ofReal (128*C*p^3*θ^2))
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) (hgJ : ∀t∉J,g t=0) :
    (∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
      g t*physicalDyadicMovingDensity s X V K T w k (t,σ,n) ∂sphereMeasure)≤
    (∫⁻t in J,g t*ENNReal.ofReal ‖K t‖)*ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*
      (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
        (representativeClosedBin T w k).rmin)) := by
  classical
  let B := representativeClosedBin T w k
  let c := 5111808*C*(p*θ)^3*B.rmax/(w*φ)
  have hc : 0≤c := by
    have hr : 0≤B.rmax := by
      dsimp [B,representativeClosedBin]
      have hh : 0<cappedRepresentative (k 3) := by dsimp [cappedRepresentative]; positivity
      positivity
    dsimp [c]
    positivity
  have hgK : Measurable (fun t=>g t*ENNReal.ofReal ‖K t‖) := hg.mul hK.norm.ennreal_ofReal
  have hm : Measurable (fun t=>(g t*ENNReal.ofReal ‖K t‖)*ENNReal.ofReal c) := hgK.mul measurable_const
  calc
    _ ≤ ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        (physicalBinBase V B J).indicator (fun z : ConeCoordinate=>(g z.1*ENNReal.ofReal ‖K z.1‖)*ENNReal.ofReal c) (t,σ,n)
          ∂sphereMeasure := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t _
      apply setLIntegral_mono' measurableSet_Ioo
      intro σ hσ
      apply lintegral_mono
      intro n
      by_cases ht : t∈J
      · have hpw := mul_le_mul' (a:=g t) (b:=g t) le_rfl
          (physicalDyadicMovingDensity_near_pointwise hs hJT hw hC hp hθ hφ hφ1 hsmall
            hDlo hDhi hd ht (Ioo_subset_Icc_self hσ) hσ.2 (hband t ht) (hv t ht) hdensity n (K:=K))
        by_cases hz : (t,σ,n)∈physicalBinBase V B J
        · dsimp [B] at hz
          simpa only [B,c,indicator_of_mem hz,mul_assoc] using hpw
        · dsimp [B] at hz
          simpa only [B,c,indicator_of_notMem hz,mul_zero] using hpw
      · simp only [hgJ t ht,zero_mul]
        exact bot_le
    _ ≤ ∫⁻z : ConeCoordinate,(g z.1*ENNReal.ofReal ‖K z.1‖)*ENNReal.ofReal c ∂physicalBinMeasure V B J :=
      physicalBin_triangle_weight_le hV B hJ T hm
    _ = (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal ‖K z.1‖ ∂physicalBinMeasure V B J)*ENNReal.ofReal c :=
      lintegral_mul_const _ (hgK.comp measurable_fst)
    _ ≤ ((∫⁻t in J,g t*ENNReal.ofReal ‖K t‖)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2))*ENNReal.ofReal c :=
      mul_le_mul' (physicalBinMeasure_receiver_weight hV B hJ hφ.le hDhi hgK) le_rfl
    _ = _ := by
      have hr : B.rmin≤B.rmax := by
        dsimp [B,representativeClosedBin]
        have hh : 0<cappedRepresentative (k 3) := by dsimp [cappedRepresentative]; positivity
        have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
        nlinarith [mul_pos hT hh]
      rw [mul_assoc,mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤384*φ^2),
        ←ENNReal.ofReal_mul (sub_nonneg.mpr hr)]
      congr 2
      dsimp [c,B]
      field_simp
      ring

lemma projectedDyadicRateKernel_polar_moving_density (α : Phase→ℝ→Phase) (zX : Phase)
    (s : Solution) (T w : ℝ) (k : Fin 4→ℕ) (K : ℝ→Vec) {G : ℝ→Vec→L[ℝ]Vec} {t σ : ℝ}
    (hσt : σ<t) (hG : G t=angularDerivativeCLM w (α zX t).2 (K t)) (n : Sphere) :
    ENNReal.ofReal (1-dot n.1 (velocity (α zX t).2))*
      (∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((α zX t).1-(t-σ) • n.1,v)) •
        projectedDyadicRateKernel α zX T k G ((t,σ),(n.1,((α zX t).1-(t-σ) • n.1,v)))‖)=
      physicalDyadicMovingDensity s (fun t=>(α zX t).1) (fun t=>(α zX t).2) K T w k (t,σ,n) := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro v
  rw [←ENNReal.ofReal_mul (cone_denom_pos _ _ (sphere_norm n)).le,
    projectedDyadicRateKernel_flux_norm α zX T k G hσt,hG]
  rfl

lemma PhaseFlowOn.label_moving_primitive_near {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hv : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
        (representativeClosedBin T w k) J,
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
          ENNReal.ofReal (128*C*p^3*θ^2))
    {b : ℝ→ℝ} (hb : Measurable b) (hbJ : ∀t∉J,b t=0) :
    (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
      ENNReal.ofReal ‖labelConeKernel s F.flow zX T
        (projectedDyadicRateKernel F.flow zX T k
          (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) z‖)≤
    (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
      ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*
        (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
          (representativeClosedBin T w k).rmin)) := by
  let X : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).1
  let V : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let G := prefixAngularRate s F.flow T w hw zX
  have hV : Measurable V :=
    (((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd).measurable
  have hK : Measurable K := (F.continuous_prefixMomentumForce hs hT zX).measurable
  have hKe : ∀t∈Icc 0 T,K t=(lorentzField s.E s.B (t,F.flow zX t)).2 := by
    intro t ht
    simp only [K,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  have hG : ∀t∈J,G t=angularDerivativeCLM w (F.flow zX t).2 (K t) := by
    intro t ht
    rw [hKe t (hJT ht)]
    exact (prefixAngular_highband (s:=s) hw zX (hJT ht) (hv t ht)).2
  have he : ∀t∈Icc 0 T,X t=(F.flow zX t).1 ∧ V t=(F.flow zX t).2 := by
    intro t ht
    simp only [X,V,prefixFlow,prefixClamp_eq ht,and_self]
  calc
    _ = ∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) z‖ := by
      apply lintegral_congr
      intro z
      apply weighted_labelProjected_congr s F.flow zX T k _ hbJ z
      intro t ht
      rw [hG t ht,hKe t (hJT ht)]
    _ = ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (b t)*physicalDyadicMovingDensity s X V K T w k (t,σ,n) ∂sphereMeasure := by
      rw [F.labelConeKernel_triangle_weighted_norm hs hT zX
        (F.projectedDyadicRateKernel_continuousOn zX k (F.prefixAngular_regular hs hT hw zX).2.1) hb]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      apply lintegral_congr
      intro n
      by_cases htJ : t∈J
      · rw [mul_assoc,projectedDyadicRateKernel_polar_moving_density F.flow zX s T w k K hσ.2 (hG t htJ) n]
        unfold physicalDyadicMovingDensity
        rw [(he t (Ioo_subset_Icc_self ht)).1,(he t (Ioo_subset_Icc_self ht)).2]
      · simp only [hbJ t htJ,ENNReal.ofReal_zero,zero_mul]
    _ ≤ (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*
          (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
            (representativeClosedBin T w k).rmin)) :=
      physicalDyadicMoving_triangle_near hs hV hK hJ hJT hw hC hp hθ hφ hφ1 hsmall
        hDlo hDhi hd (fun t ht=>by rw [(he t (hJT ht)).2]; exact hband t ht)
        (fun t ht=>by rw [(he t (hJT ht)).2]; exact hv t ht) hdensity hb.ennreal_ofReal
        (fun t ht=>by rw [hbJ t ht,ENNReal.ofReal_zero])
    _ = _ := by
      congr 1
      apply setLIntegral_congr_fun hJ
      intro t ht
      dsimp only
      rw [hKe t (hJT ht)]

lemma Admissible.label_moving_primitive_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w p θ φ : ℝ) (k : Fin 4→ℕ),
      MeasurableSet J → J⊆Icc 0 T → 0<w → 0≤p → 0≤θ → 0<φ → φ≤1 → θ≤φ →
      φ^2/2≤(representativeClosedBin T w k).Dmin →
      (representativeClosedBin T w k).Dmax≤8*φ^2 →
      (representativeClosedBin T w k).dmax≤8*θ^2 →
      (representativeClosedBin T w k).qmax≤p →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k
          (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) z‖)≤
      (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*(p*θ)^3*φ/w*
          (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
            (representativeClosedBin T w k).rmin)) := by
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨1962934272*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w p θ φ k hJ hJT hw hp hθ hφ hφ1 hsmall hDlo hDhi hd hq hband hv b hbm hbJ
  apply F.label_moving_primitive_near hs hT zX hJ hJT hw hC hp hθ hφ hφ1 hsmall hDlo hDhi hd hband hv _ hbm hbJ
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)

lemma selected_representative_moving_bound {T C w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    (hC : 0≤C) (hw : 0≤w) (h0 : k 0<N) (h1 : k 1<N)
    (hsel : sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) :
    C*(sourceRepresentative (k 0)*cappedRepresentative (k 1))^3*
      cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
      ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin)≤
      (4*C*Real.sqrt (max 1 T)/w)*directionWeightMajorant N k := by
  have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  have hb := selected_moving_coefficient hC hp.le (hc 1).le (hc 2).le hw
    (mul_nonneg hT.le (hc 3).le) hsel
    (R:=(representativeClosedBin T w k).rmax) (r:=(representativeClosedBin T w k).rmin)
    (by exact mul_nonneg (mul_nonneg (by norm_num) hT.le) (hc 3).le)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
    (by dsimp [representativeClosedBin]; ring_nf; exact le_rfl)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
  calc
    _ ≤ 4*C*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2)/w := hb
    _ = _ := by
      rw [Real.sqrt_mul hT.le]
      simp only [directionWeightMajorant,ite_eq_left h0,ite_eq_left h1,one_mul,cappedRepresentative]
      norm_num
      ring

lemma Admissible.selected_moving_bound_finite_sources {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularDerivativeCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (lorentzField s.E s.B (labelReceiverTime F.flow zX T p,F.flow zX (labelReceiverTime F.flow zX T p))).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t| * ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨C,hC,hnear⟩ := hd.label_moving_primitive_near_constant
  refine ⟨32*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w N Q hQ hJ hJT hw hband hv b hb hbJ
  let G := prefixAngularRate s F.flow T w hw zX
  let W := ∫⁻t in J,ENNReal.ofReal |b t| * ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖
  have hG := (F.prefixAngular_regular hs hT hw zX).2.1
  have hGe : ∀t∈J,G t=angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2 :=
    fun t ht=>(prefixAngular_highband (s:=s) hw zX (hJT ht) (hv t ht)).2
  have h0abs : ∀t∉J,|b t|=0 := fun t ht=>by rw [hbJ t ht,abs_zero]
  have hbnorm (k : Fin 4→ℕ) : Measurable (fun p : ℝ×Phase=>
      ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) :=
    ((hb.comp (F.labelReceiverTime_measurable zX)).norm.ennreal_ofReal).mul
      ((F.measurable_labelConeKernel hs zX (F.projectedDyadicRateKernel_continuousOn zX k hG)).norm.ennreal_ofReal)
  have hbound (k : Fin 4→ℕ) (hk : k∈Q) :
      (∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖)≤
      W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (directionWeightMajorant N k)) := by
    have hc (i : Fin 4) : 0<cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hp : 0<sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    have he : (∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖)=
      ∫⁻p : ℝ×Phase,ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) p‖ := by
      apply lintegral_congr
      intro p
      exact weighted_labelProjected_congr s F.flow zX T k (fun t ht=>hGe t ht) h0abs p
    rw [he]
    have hn := hnear s T F hs hT h0 zX J w (sourceRepresentative (k 0))
      (cappedRepresentative (k 1)) (cappedRepresentative (k 2)) k hJ hJT hw hp.le (hc 1).le (hc 2)
      (by dsimp [cappedRepresentative]; exact pow_le_one₀ (by norm_num) (by norm_num))
      (hQ k hk).2.2.1 le_rfl le_rfl le_rfl (by
        change sourceRepresentative (k 0)/32 ≤ sourceRepresentative (k 0)
        linarith) hband hv (fun t=>|b t|) hb.norm h0abs
    refine hn.trans (mul_le_mul' (a:=W) (b:=W) le_rfl ?_)
    rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
    exact ENNReal.ofReal_le_ofReal
      (selected_representative_moving_bound hC hw.le (hQ k hk).1 (hQ k hk).2.1 (hQ k hk).2.2.2)
  calc
    _ = ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖ := by
      apply lintegral_congr
      intro p
      by_cases ht : labelReceiverTime F.flow zX T p∈J
      · rw [hGe _ ht]
      · simp only [labelWeight,hbJ _ ht,zero_mul,zero_smul,map_zero]
    _ = ∫⁻p : ℝ×Phase,∑'k : Fin 4→ℕ,Q.indicator (fun k=>
        ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
          ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
      apply lintegral_congr
      intro p
      exact F.selected_receiver_rate_norm_sum s zX Q b G p
    _ = ∑'k : Fin 4→ℕ,∫⁻p : ℝ×Phase,Q.indicator (fun k=>
        ENNReal.ofReal |b (labelReceiverTime F.flow zX T p)| *
          ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) p‖) k := by
      apply lintegral_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using (hbnorm k).aemeasurable
      · simp only [indicator_of_notMem hk]
        exact aemeasurable_const
    _ ≤ ∑'k : Fin 4→ℕ,W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*
        ENNReal.ofReal (directionWeightMajorant N k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using hbound k hk
      · simp only [indicator_of_notMem hk,lintegral_zero]
        exact bot_le
    _ = W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*
        ∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k)) := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ W*(ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      mul_le_mul' (a:=W) (b:=W) le_rfl (mul_le_mul' (a:=ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w))
        (b:=ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)) le_rfl (tsum_directionWeightMajorant N))
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
      congr 2
      ring

lemma Admissible.selected_moving_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularDerivativeCLM w (F.flow zX (labelReceiverTime F.flow zX T p)).2
        (lorentzField s.E s.B (labelReceiverTime F.flow zX T p,F.flow zX (labelReceiverTime F.flow zX T p))).2
        (labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)‖)≤
      (∫⁻t in J,ENNReal.ofReal |b t| * ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_moving_bound_finite_sources
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv b hbm hbJ
  have he : (fun p : ℝ×Phase=>labelWeight F.flow zX T Q b p • actualLabelRatePrimitive s F.flow zX T p)=
      fun p : ℝ×Phase=>labelWeight F.flow zX T (Q∩{k | k 0<N ∧ k 1<N}) b p • actualLabelRatePrimitive s F.flow zX T p :=
    funext (F.labelWeight_rate_source_truncate s zX N hP Q b)
  simp_rw [congr_fun he]
  exact hb s T F hs hT h0 zX J w N _ (fun k hk=>⟨hk.2.1,hk.2.2,hQ k hk.1⟩)
    hJ hJT hw hband hv b hbm hbJ

lemma directionWeight_deriv_outside {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∉Icc a b) : deriv (directionWeight a b ℓ) t=0 :=
  deriv_of_notMem_tsupport (fun h=>ht (directionWeight_tsupport hℓ hab h))

lemma directionWeight_lvariation {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    {J : Set ℝ} (hJ : Icc a b⊆J) :
    (∫⁻t in J,ENNReal.ofReal |deriv (directionWeight a b ℓ) t|)=2 := by
  have hs : Function.support (fun t=>ENNReal.ofReal |deriv (directionWeight a b ℓ) t|)⊆Icc a b := by
    intro t ht
    by_contra hn
    exact ht (by dsimp only; rw [directionWeight_deriv_outside hℓ hab hn,abs_zero,ENNReal.ofReal_zero])
  rw [setLIntegral_eq_of_support_subset (hs.trans hJ),←setLIntegral_eq_of_support_subset hs]
  have hi : IntervalIntegrable (fun t=>|deriv (directionWeight a b ℓ) t|) volume a b :=
    ((directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b)).absolutelyContinuousOnInterval.intervalIntegrable_deriv.norm
  rw [←ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (show a≤b by linarith)).mp hi)
    (ae_of_all _ (fun t=>abs_nonneg _)),integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show a≤b by linarith),directionWeight_total_variation hℓ hab]
  norm_num

lemma directionWeight_ne_zero_interior {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : directionWeight a b ℓ t≠0) : t∈Ioo a b := by
  have hc : t∈Icc a b := directionWeight_tsupport hℓ hab (subset_closure ht)
  refine ⟨lt_of_le_of_ne hc.1 ?_,lt_of_le_of_ne hc.2 ?_⟩
  · intro he
    subst t
    exact ht (directionWeight_endpoints hℓ hab).1
  · intro he
    subst t
    exact ht (directionWeight_endpoints hℓ hab).2

lemma directionWeight_sum_le_one {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) (t : ℝ) :
    ∑i∈S,directionWeight (a i) (b i) (ℓ i) t≤1 := by
  classical
  by_cases hz : ∀i∈S,directionWeight (a i) (b i) (ℓ i) t=0
  · simp only [Finset.sum_eq_zero hz,zero_le_one]
  · push Not at hz
    obtain ⟨i,hi,hit⟩ := hz
    rw [Finset.sum_eq_single i]
    · exact (directionWeight_bounds (hℓ i hi) (hlen i hi)).2
    · intro j hj hji
      by_contra hn
      exact Set.disjoint_left.mp (hdis hi hj (Ne.symm hji))
        (directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hit)
        (directionWeight_ne_zero_interior (hℓ j hj) (hlen j hj) hn)
    · exact fun hn=>(hn hi).elim

lemma directionWeight_sum_ofReal_le_one {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) (t : ℝ) :
    ∑i∈S,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t|≤1 := by
  have hn : ∀i∈S,0≤directionWeight (a i) (b i) (ℓ i) t :=
    fun i hi=>(directionWeight_bounds (hℓ i hi) (hlen i hi)).1
  simp_rw [Finset.sum_congr rfl (fun i hi=>congrArg ENNReal.ofReal (abs_of_nonneg (hn i hi)))]
  rw [←ENNReal.ofReal_sum_of_nonneg hn]
  exact (ENNReal.ofReal_le_ofReal (directionWeight_sum_le_one S a b ℓ hℓ hlen hdis t)).trans_eq (by norm_num)

lemma directionWeight_sum_kernel {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {J : Set ℝ} {g : ℝ→ℝ≥0∞} (hg : AEMeasurable g (volume.restrict J)) :
    (∑i∈S,∫⁻t in J,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| * g t)≤∫⁻t in J,g t := by
  have hm (i : ι) : AEMeasurable (fun t=>ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| * g t) (volume.restrict J) := by
    apply AEMeasurable.mul
    · have hc : Continuous (fun t=>ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t|) :=
        ENNReal.continuous_ofReal.comp ((directionWeight_lipschitz (a i) (b i) (ℓ i)).continuous.abs)
      exact hc.measurable.aemeasurable
    · exact hg
  rw [←lintegral_finsetSum' S (fun i _=>hm i)]
  apply lintegral_mono
  intro t
  dsimp only
  rw [←Finset.sum_mul]
  exact (mul_le_mul' (directionWeight_sum_ofReal_le_one S a b ℓ hℓ hlen hdis t) le_rfl).trans_eq (one_mul _)

def selectedAngularMovingCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T w : ℝ) (Q : Set (Fin 4→ℕ)) (b : ℝ→ℝ) : ℝ≥0∞ :=
  ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularDerivativeCLM w (α zX (labelReceiverTime α zX T p)).2
    (lorentzField s.E s.B (labelReceiverTime α zX T p,α zX (labelReceiverTime α zX T p))).2
    (labelWeight α zX T Q b p • actualLabelRatePrimitive s α zX T p)‖

def selectedAngularWeightCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T w : ℝ) (Q : Set (Fin 4→ℕ)) (b : ℝ→ℝ) : ℝ≥0∞ :=
  ∫⁻p : ℝ×Phase,ENNReal.ofReal ‖angularMultiplierCLM w (α zX (labelReceiverTime α zX T p)).2
    (labelWeight α zX T Q (deriv b) p • actualLabelRatePrimitive s α zX T p)‖

lemma PhaseFlowOn.aemeasurable_receiver_force {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (fun t=>ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖) (volume.restrict J) := by
  have hc : Continuous (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) :=
    ENNReal.continuous_ofReal.comp ((F.continuous_prefixMomentumForce hs hT zX).norm)
  apply hc.measurable.aemeasurable.congr
  filter_upwards [ae_restrict_mem hJ] with t ht
  simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (hJT ht)]

lemma Admissible.direction_family_moving_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      (∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
      (∫⁻t in J,ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_moving_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell hdis
  have hi (i : ι) (hi : i∈S) := hb s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv
    (directionWeight (a i) (b i) (ℓ i)) (directionWeight_lipschitz _ _ _).continuous.measurable
    (fun t ht=>image_eq_zero_of_notMem_tsupport (f:=directionWeight _ _ _)
      (fun hn=>ht (hcell i hi (directionWeight_tsupport (hℓ i hi) (hlen i hi) hn))))
  calc
    _ ≤ ∑i∈S,(∫⁻t in J,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| *
        ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := Finset.sum_le_sum hi
    _ = (∑i∈S,∫⁻t in J,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t| *
        ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul' (directionWeight_sum_kernel S a b ℓ hℓ hlen hdis
      (F.aemeasurable_receiver_force hs hT zX hJ hJT)) le_rfl

lemma Admissible.direction_family_weight_bound {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀z,s.f (0,z)≠0→∀σ∈Icc 0 T,1024*q (F.flow z σ).2≤(2:ℝ)^N) →
      (∀k∈Q,cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀(ι : Type) (S : Finset ι) (a b ℓ : ι→ℝ),
      (∀i∈S,0<ℓ i) → (∀i∈S,2*ℓ i≤b i-a i) → (∀i∈S,Icc (a i) (b i)⊆J) →
      (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i)))≤
        (S.card:ℝ≥0∞)*ENNReal.ofReal (2*C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
  obtain ⟨C,hC,hb⟩ := hd.selected_receiver_weight_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv ι S a b ℓ hℓ hlen hcell
  have hi (i : ι) (hi : i∈S) : selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))≤
      ENNReal.ofReal (2*C*Real.sqrt (max 1 T)*(N:ℝ)^2) := by
    have hk := hb s T F hs hT h0 zX J w N Q hP hQ hJ hJT hw hband hv
      (deriv (directionWeight (a i) (b i) (ℓ i))) (measurable_deriv _)
      (fun t ht=>directionWeight_deriv_outside (hℓ i hi) (hlen i hi) (fun hn=>ht (hcell i hi hn)))
    rw [directionWeight_lvariation (hℓ i hi) (hlen i hi) (hcell i hi)] at hk
    apply hk.trans_eq
    rw [show (2:ℝ≥0∞)=ENNReal.ofReal (2:ℝ) by norm_num,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hi

end RVM

end

end OAI
