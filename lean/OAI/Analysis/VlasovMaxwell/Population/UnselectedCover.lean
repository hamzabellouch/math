import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates
import OAI.Analysis.VlasovMaxwell.Population.SelectedRemainder
import OAI.Analysis.VlasovMaxwell.Population.MagneticEstimates
import OAI.Analysis.VlasovMaxwell.Population.TransportRemainder
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedTransportNear
import OAI.Analysis.VlasovMaxwell.Population.DirectExpandedAssemble

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.direct_source_representative_cost {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (k : Fin 4→ℕ) {a b : ℝ} (ha : 0≤a) (hb : b≤T) :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal 10240*(representativeGoodCost s F zX w k a b+
        representativeMagneticCost s F zX w k a b) := by
  have hc := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hp : 0<sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := cappedRepresentative_pos (k 1)
  have hf := cappedRepresentative_pos (k 2)
  have hh := physicalDirectSource_integral_bound hs hT hc.fst.measurable hc.snd.measurable
    (representativeClosedBin T w k) measurableSet_Icc (Icc_subset_Icc ha hb)
    (show 0<sourceRepresentative (k 0)/128 by positivity) ht hf
    (representativeClosedBin_radius_pos T w k) le_rfl le_rfl le_rfl
  apply hh.trans_eq
  unfold representativeGoodCost representativeMagneticCost
  dsimp only
  rw [mul_add,←mul_assoc,←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240),
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240)]
  congr 1
  · congr 1
    congr 1
    ring
  · rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro z
    have he : 10240*(cappedRepresentative (k 2)/sourceRepresentative (k 0))=
        (80/(sourceRepresentative (k 0)/128))*cappedRepresentative (k 2) := by ring
    rw [he,ENNReal.ofReal_mul (by positivity : 0≤80/(sourceRepresentative (k 0)/128))]
    dsimp only [Function.comp_apply,id_eq]
    ac_rfl

lemma PhaseFlowOn.selectedSourceTriangle_direct_le {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    (p : TrianglePhase) :
    ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX) W J p‖≤
      directTriangleDensity s (fun t=>(prefixFlow F.flow T zX t).1) T J
        (directSourceTriangleKernel s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) T) p := by
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J p)).trans
  by_cases ht : p.1.1∈J
  · rw [indicator_of_mem ht]
    by_cases hp : p∈trianglePhaseDomain T
    · have htime := hJT ht
      have hσ : p.1.2.1∈Icc 0 T := ⟨hp.2.1.le,hp.2.2.le.trans htime.2⟩
      have hn := ((W p.1.1).le_opNorm (triangleConeKernel s F.flow zX T
        (sourceOnlyConeKernel s F.flow zX) p)).trans
          (mul_le_mul_of_nonneg_right (hW _ ht) (norm_nonneg _))
      rw [one_mul] at hn
      apply (ENNReal.ofReal_le_ofReal hn).trans_eq
      rw [triangleConeKernel_source hp]
      simp only [directTriangleDensity,indicator_of_mem (show p∈directTriangleDomain T J from ⟨hp,ht⟩),
        prefixParticle,prefixFlow,prefixClamp_eq htime,prefixClamp_eq hσ,directSourceTriangleKernel,
        prefixField,sourceAcceleration,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (p.1.1-p.1.2.1)),ENNReal.ofReal_mul (sq_nonneg _)]
    · simp only [triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
      exact bot_le
  · simp only [indicator_of_notMem ht,zero_apply,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

abbrev UnselectedCoverIndex (N : ℕ) := (Fin 4→ℕ) ⊕ (DirectOuterIndex N×ℕ)

def unselectedCoverBin (T w : ℝ) {N : ℕ} : UnselectedCoverIndex N→ClosedConeBin :=
  Sum.elim (representativeClosedBin T w) (fun i=>directOuterBin T w i.1 i.2)

def unselectedCoverSector (P M A w I : ℝ) (N : ℕ) : Set (UnselectedCoverIndex N) :=
  {i | match i with
    | .inl k => k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k
    | .inr i => sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}

lemma physical_remaining_active_finite_cover {T P w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {N : ℕ} {k : Fin 4→ℕ} (hP : 0≤P) (hwP : w≤P)
    (hN : 8192*P≤(2:ℝ)^N) (ht : t∈J) (hσ : σ∈Icc 0 t)
    (hb : q (V t)∈Icc (w/8) (8*w)) (n : Sphere) (v : Vec)
    (hv : 1024*q v≤P) (hsource : sourceRepresentative (k 0)≤P)
    (hpos : 0<dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t)))
    (hrem : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)) :
    ∃i : DirectOuterIndex N×ℕ,
      (sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val) ∧
      ((t,σ,n),v)∈physicalBinPhaseSet V (directOuterBin T w i.1 i.2) J := by
  obtain ⟨j,hj⟩ := exists_relative_dyadic_positive v (V t)
  have hrel : 0<relativePhysicalFactor T (t-σ) n.1 v (V t) k j := mul_pos hpos hj
  have hvN : 1024*q v≤(2:ℝ)^N := by linarith only [hv,hP,hN]
  have hidx := relativePhysicalFactor_positive_indices (sphere_norm n) hvN hrel
  have hW : 1024*q (V t)≤(2:ℝ)^N := by linarith only [hb.2,hwP,hN]
  have hnf : k 2<N := source_angle_index_lt (sphere_norm n)
    (show DyadicBand (k 2) (Real.sqrt ((1-dot n.1 (velocity (V t)))/2)) from
      dyadicMultiFactor_positive_bands hpos 2) hW
  let i : DirectOuterIndex N := ![⟨k 0,hidx.1⟩,⟨k 1,hidx.2.1⟩,⟨k 2,hnf⟩,⟨j,hidx.2.2⟩]
  have he : ![(i 0).val,(i 1).val,(i 2).val,k 3]=k := by
    funext l
    fin_cases l <;> rfl
  refine ⟨(i,k 3),⟨?_,hrem⟩,?_⟩
  · change sourceRepresentative (k 0)≤128*P
    linarith only [hsource,hP]
  · have hm := relativePhysicalFactor_positive_closedBin ht hσ hb hrel
    simpa only [physicalBinPhaseSet,mem_ofPred_eq,directOuterBin,he,show (i 3).val=j from rfl] using hm

lemma physical_unselected_active_cover {T P M A w I t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {N : ℕ} (hP : 0≤P) (hwP : w≤P) (hN : 8192*P≤(2:ℝ)^N)
    (ht : t∈J) (hσ : σ∈Icc 0 t) (hb : q (V t)∈Icc (w/8) (8*w))
    (n : Sphere) (v : Vec) (hv : 1024*q v≤P)
    (hc : selectedDyadicCutoff (bulkSelection P M A w I)ᶜ
      (physicalCutoffCoordinates T (t-σ) n.1 v (V t))≠0) :
    ∃i∈unselectedCoverSector P M A w I N,
      ((t,σ,n),v)∈physicalBinPhaseSet V (unselectedCoverBin T w i) J := by
  obtain ⟨k,hk,hpos⟩ := selectedDyadicCutoff_active hc
  have hsource : sourceRepresentative (k 0)≤P :=
    (sourceRepresentative_mem_range (dyadicMultiFactor_positive_bands hpos 0) hv).2
  have hfloor := physicalCutoff_positive_source_floor (sphere_norm n) hpos
  by_cases hrem : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)
  · obtain ⟨i,hi,hmem⟩ := physical_remaining_active_finite_cover
      (T:=T) (P:=P) (w:=w) (V:=V)
      (J:=J) (N:=N) (k:=k) hP hwP hN ht hσ hb n v hv hsource hpos hrem
    exact ⟨.inr i,hi,hmem⟩
  · have hφ := cappedRepresentative_pos (k 2)
    have hn := lt_of_not_ge hrem
    have hs : k∈representativeSmallSector P := ⟨hsource,hfloor,by linarith⟩
    have hnot : ¬representativeSelected P M A w I k := by
      intro hsel
      exact hk ⟨by linarith,hsel⟩
    refine ⟨.inl k,⟨hs,hnot⟩,?_⟩
    exact physicalCutoff_positive_closedBin ht hσ hb hpos

lemma PhaseFlowOn.bulkUnselectedCone_support {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (K : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hphysical : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    {p : TrianglePhase} (hp : selectedConeTriangle s F.flow zX T
        (bulkSelection P M A w I)ᶜ K W J p≠0) :
    ∃i∈unselectedCoverSector P M A w I N,
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (unselectedCoverBin T w i) J := by
  obtain ⟨ht,hσ,hb,hv,hc⟩ := F.selectedConeTriangle_physical_nonzero zX
    (bulkSelection P M A w I)ᶜ K W hJT hband hphysical hp
  exact physical_unselected_active_cover (T:=T) (P:=P) (M:=M) (A:=A) (w:=w) (I:=I)
    (V:=fun t=>(prefixFlow F.flow T zX t).2) (J:=J) (N:=N)
    hP hwP hN ht hσ hb p.1.2.2 p.2 hv hc

lemma Admissible.unselected_small_source_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let R := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectSourceDensity s X V (representativeClosedBin T w k) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cg,hCg,hgood⟩ := hd.unselected_good_uniform T₀
  obtain ⟨Cm,hCm,hmag⟩ := hd.magnetic_small_uniform T₀
  refine ⟨10240*(Cg+Cm),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hgood M A (zero_lt_one.trans_le hM) hA] with P hg
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  dsimp only
  let R := {k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
  let G := fun k=>representativeGoodCost s F zX w k a b
  let H := fun k=>representativeMagneticCost s F zX w k a b
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  have hPB : P*Real.sqrt I≤B := le_add_of_nonneg_right (by positivity)
  have hsum : (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal 10240*((∑'k,R.indicator G k)+(∑'k,R.indicator H k)) := by
    rw [←ENNReal.tsum_add,←ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈R
    · simp only [indicator_of_mem hk]
      exact F.direct_source_representative_cost hs.energyPrefix hT zX k ha hb
    · simp only [indicator_of_notMem hk,zero_add,mul_zero,le_refl]
  have hg' : (∑'k,R.indicator G k)≤ENNReal.ofReal (Cg*B) := by
    apply (hg s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI
      (zero_lt_one.trans_le hw) hsource HZ).trans
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hPB hCg
  have hm : (∑'k,R.indicator H k)≤ENNReal.ofReal (Cm*B) := by
    calc
      _≤∑'k,(centralIndexSector P).indicator H k := by
        apply ENNReal.tsum_le_tsum
        intro k
        by_cases hk : k∈R
        · rw [indicator_of_mem hk,indicator_of_mem (representativeSmallSector_subset_centralIndexSector P hk.1)]
        · rw [indicator_of_notMem hk]; exact bot_le
      _≤_ := by
        rw [tsum_centralIndexSector]
        exact hmag M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  apply hsum.trans
  apply (mul_le_mul' le_rfl (add_le_add hg' hm)).trans_eq
  rw [←ENNReal.ofReal_add (mul_nonneg hCg hB) (mul_nonneg hCm hB),
    ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10240)]
  congr 1
  ring

lemma unselectedCover_tsum {N : ℕ} (T P M A w I : ℝ) (f : ClosedConeBin→ℝ≥0∞) :
    (∑'i : UnselectedCoverIndex N,(unselectedCoverSector P M A w I N).indicator
      (fun i=>f (unselectedCoverBin T w i)) i)=
    (∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}).indicator
      (fun k=>f (representativeClosedBin T w k)) k)+
    (∑'i : DirectOuterIndex N×ℕ,({i : DirectOuterIndex N×ℕ |
      sourceRepresentative (i.1 0).val≤128*P ∧
      cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
      (fun i=>f (directOuterBin T w i.1 i.2)) i) := by
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  rfl

lemma PhaseFlowOn.selectedSourceTriangle_v_integral_le {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {W : ℝ→Vec→L[ℝ]Vec} {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (hcontract : ∀t∈J,‖W t‖≤1) (B : ClosedConeBin) (z : ConeCoordinate)
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX) W J (z,v)‖)≤
      physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z := by
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hh : (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX) W J (z,v)‖)≤
      ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        directTriangleDensity s X T J (directSourceTriangleKernel s X V T) (z,v) := by
    exact lintegral_mono (fun v=>F.selectedSourceTriangle_direct_le zX Q hJT W hcontract (z,v))
  exact hh.trans (directSourceTriangle_bin_bound hJT B hz)

lemma PhaseFlowOn.selectedSourceTriangle_bin_integral_le {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec} {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) (hcontract : ∀t∈J,‖W t‖≤1) (B : ClosedConeBin) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet B z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX) W J (z,v)‖ ∂volume
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B J)≤
      ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B J := by
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
  exact F.selectedSourceTriangle_v_integral_le zX Q hJT hcontract B z hz

lemma PhaseFlowOn.unselectedSourceTriangle_physical_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hcontract : ∀t∈J,‖W t‖≤1) (hP : 0≤P) (hwP : w≤P)
    (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hphysical : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)ᶜ
      (sourceOnlyConeKernel s F.flow zX) W J p‖ ∂trianglePhaseMeasure)≤
    ∑'i : UnselectedCoverIndex N,(unselectedCoverSector P M A w I N).indicator
      (fun i=>∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (unselectedCoverBin T w i) z
        ∂physicalBinMeasure V (unselectedCoverBin T w i) J) i := by
  dsimp only
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hA : ContinuousOn (sourceOnlyConeKernel s F.flow zX) (coneKernelInterior T) :=
    (F.sourceOnlyConeKernel_continuousOn hs zX).mono inter_subset_left
  have hg := (F.selectedConeTriangle_measurable hs zX (bulkSelection P M A w I)ᶜ hA hW hJ).norm.ennreal_ofReal
  have hcover := physicalBinFamily_cover_lintegral hV hJ (unselectedCoverBin T w)
    (unselectedCoverSector P M A w I N) hg
  refine (hcover (by
      intro p hp
      apply F.bulkUnselectedCone_support zX _ W hJT hband hP hwP N hN hphysical
      intro he
      exact hp (by rw [he,norm_zero,ENNReal.ofReal_zero]))).trans ?_
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : i∈unselectedCoverSector P M A w I N
  · simp only [indicator_of_mem hi]
    exact F.selectedSourceTriangle_bin_integral_le hs hT zX _ hJ hJT hcontract _
  · simp only [indicator_of_notMem hi,le_refl]

lemma PhaseFlowOn.selectedTransportTriangle_direct_le {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (W : ℝ→Vec→L[ℝ]Vec) (hW : ∀t∈J,‖W t‖≤1)
    (p : TrianglePhase) :
    ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (transportOnlyConeKernel F.flow zX) W J p‖≤
      directTriangleDensity s (fun t=>(prefixFlow F.flow T zX t).1) T J
        (directTransportTriangleKernel (fun t=>(prefixFlow F.flow T zX t).2)) p := by
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J p)).trans
  by_cases ht : p.1.1∈J
  · rw [indicator_of_mem ht]
    by_cases hp : p∈trianglePhaseDomain T
    · have htime := hJT ht
      have hσ : p.1.2.1∈Icc 0 T := ⟨hp.2.1.le,hp.2.2.le.trans htime.2⟩
      have hn := ((W p.1.1).le_opNorm (triangleConeKernel s F.flow zX T
        (transportOnlyConeKernel F.flow zX) p)).trans
          (mul_le_mul_of_nonneg_right (hW _ ht) (norm_nonneg _))
      rw [one_mul] at hn
      apply (ENNReal.ofReal_le_ofReal hn).trans_eq
      rw [triangleConeKernel_transport hp]
      simp only [directTriangleDensity,indicator_of_mem (show p∈directTriangleDomain T J from ⟨hp,ht⟩),
        prefixParticle,prefixFlow,prefixClamp_eq htime,prefixClamp_eq hσ,directTransportTriangleKernel,
        norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (p.1.1-p.1.2.1)),ENNReal.ofReal_mul (sq_nonneg _)]
    · simp only [triangleConeKernel,indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
      exact bot_le
  · simp only [indicator_of_notMem ht,zero_apply,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.selectedTransportTriangle_v_integral_le {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {W : ℝ→Vec→L[ℝ]Vec} {J : Set ℝ} (hJT : J⊆Icc 0 T)
    (hcontract : ∀t∈J,‖W t‖≤1) (B : ClosedConeBin) (z : ConeCoordinate)
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (transportOnlyConeKernel F.flow zX) W J (z,v)‖)≤
      physicalDirectTransportDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z := by
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hh : (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (transportOnlyConeKernel F.flow zX) W J (z,v)‖)≤
      ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        directTriangleDensity s X T J (directTransportTriangleKernel V) (z,v) := by
    exact lintegral_mono (fun v=>F.selectedTransportTriangle_direct_le zX Q hJT W hcontract (z,v))
  exact hh.trans (directTransportTriangle_bin_bound hJT B hz)

lemma PhaseFlowOn.selectedTransportTriangle_bin_integral_le {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {W : ℝ→Vec→L[ℝ]Vec} {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) (hcontract : ∀t∈J,‖W t‖≤1) (B : ClosedConeBin) :
    (∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet B z.2.2.1
      (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (transportOnlyConeKernel F.flow zX) W J (z,v)‖ ∂volume
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B J)≤
      ∫⁻z : ConeCoordinate,physicalDirectTransportDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) B J := by
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
  exact F.selectedTransportTriangle_v_integral_le zX Q hJT hcontract B z hz

lemma PhaseFlowOn.unselectedTransportTriangle_physical_sum {s : Solution} {T P M A w I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J)
    (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hcontract : ∀t∈J,‖W t‖≤1) (hP : 0≤P) (hwP : w≤P)
    (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hphysical : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) :
    let X := fun t=>(prefixFlow F.flow T zX t).1
    let V := fun t=>(prefixFlow F.flow T zX t).2
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)ᶜ
      (transportOnlyConeKernel F.flow zX) W J p‖ ∂trianglePhaseMeasure)≤
    ∑'i : UnselectedCoverIndex N,(unselectedCoverSector P M A w I N).indicator
      (fun i=>∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V (unselectedCoverBin T w i) z
        ∂physicalBinMeasure V (unselectedCoverBin T w i) J) i := by
  dsimp only
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  have hA : ContinuousOn (transportOnlyConeKernel F.flow zX) (coneKernelInterior T) :=
    (F.transportOnlyConeKernel_continuousOn zX).mono inter_subset_left
  have hg := (F.selectedConeTriangle_measurable hs zX (bulkSelection P M A w I)ᶜ hA hW hJ).norm.ennreal_ofReal
  have hcover := physicalBinFamily_cover_lintegral hV hJ (unselectedCoverBin T w)
    (unselectedCoverSector P M A w I N) hg
  refine (hcover (by
      intro p hp
      apply F.bulkUnselectedCone_support zX _ W hJT hband hP hwP N hN hphysical
      intro he
      exact hp (by rw [he,norm_zero,ENNReal.ofReal_zero]))).trans ?_
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : i∈unselectedCoverSector P M A w I N
  · simp only [indicator_of_mem hi]
    exact F.selectedTransportTriangle_bin_integral_le hs hT zX _ hJ hJT hcontract _
  · simp only [indicator_of_notMem hi,le_refl]

lemma Admissible.unselected_transport_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w → w≤P →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (W : ℝ→Vec→L[ℝ]Vec),Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)ᶜ
        (transportOnlyConeKernel F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := hd.small_transport_uniform T₀
  obtain ⟨Cr,hCr,hremaining⟩ := hd.direct_remaining_transport_uniform_expanded
  obtain ⟨K,hK,hcount⟩ := exists_direct_dyadic_count
  refine ⟨Cs+Cr*max 1 T₀,by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP hphysical hband HZ W hW hcontract
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let cost := fun B : ClosedConeBin=>∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z
      ∂physicalBinMeasure V B (Icc a b)
  have hB : 0≤B := by dsimp [B]; positivity
  have hf0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    rw [show (fun z=>s.f (0,z))=d.f₀ from funext hs.initial_f]
  have hh := F.unselectedTransportTriangle_physical_sum (M:=M) (A:=A) (I:=I) hs.energyPrefix hT zX hW measurableSet_Icc
    (Icc_subset_Icc ha hb) hband hcontract (zero_le_one.trans hP) hwP N hN hphysical
  change _≤∑'i : UnselectedCoverIndex N,(unselectedCoverSector P M A w I N).indicator
    (fun i=>cost (unselectedCoverBin T w i)) i at hh
  rw [unselectedCover_tsum] at hh
  have hsm : (∑'k : Fin 4→ℕ,({k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}).indicator
      (fun k=>cost (representativeClosedBin T w k)) k)≤ENNReal.ofReal (Cs*B) := by
    apply le_trans (b:=∑'k : Fin 4→ℕ,(representativeSmallSector P).indicator
      (fun k=>cost (representativeClosedBin T w k)) k)
    · apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈{k | k∈representativeSmallSector P ∧ ¬representativeSelected P M A w I k}
      · simp only [indicator_of_mem hk,indicator_of_mem hk.1,le_refl]
      · rw [indicator_of_notMem hk]; exact bot_le
    · exact hsmall M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  have hrem := hremaining P (zero_le_one.trans hP) s T F hs.energyPrefix hT hs.initial_f zX
    (tsupport d.f₀) a b I w hd.2.1 hf0 ha hb hJI hI hI1
  have hright : (∑'i : DirectOuterIndex N×ℕ,({i : DirectOuterIndex N×ℕ |
      sourceRepresentative (i.1 0).val≤128*P ∧
      cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
      (fun i=>cost (directOuterBin T w i.1 i.2)) i)≤ENNReal.ofReal ((Cr*max 1 T₀)*B) := by
    apply (directOuter_remaining_le_tsum P
      (fun np nf nt j nr=>cost (relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j))).trans
    apply hrem.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (mul_le_mul_of_nonneg_left (max_le_max le_rfl hTT) hCr)
      (le_add_of_nonneg_right (by positivity)) (by positivity) (by positivity)
  apply hh.trans ((add_le_add hsm hright).trans_eq ?_)
  rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (by positivity)]
  congr 1
  ring

lemma Admissible.unselected_source_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (W : ℝ→Vec→L[ℝ]Vec),Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)ᶜ
        (sourceOnlyConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := hd.unselected_small_source_uniform T₀
  obtain ⟨Cr,hCr,hremaining⟩ := hd.direct_remaining_source_unrestricted_uniform
  obtain ⟨K,hK,hcount⟩ := exists_direct_dyadic_count
  refine ⟨Cs+Cr*(1+K^4),by positivity,?_⟩
  intro M A hM hA
  filter_upwards [hsmall M A hM (zero_lt_one.trans_le hA)] with P hsmallP
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsource hphysical hband HZ W hW hcontract
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let cost := fun B : ClosedConeBin=>∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
      ∂physicalBinMeasure V B (Icc a b)
  have hB : 0≤B := by dsimp [B]; positivity
  have hf0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    rw [show (fun z=>s.f (0,z))=d.f₀ from funext hs.initial_f]
  have hh := F.unselectedSourceTriangle_physical_sum (M:=M) (A:=A) (I:=I) hs.energyPrefix hT zX hW measurableSet_Icc
    (Icc_subset_Icc ha hb) hband hcontract (zero_le_one.trans hP) hwP N hN hphysical
  change _≤∑'i : UnselectedCoverIndex N,(unselectedCoverSector P M A w I N).indicator
    (fun i=>cost (unselectedCoverBin T w i)) i at hh
  rw [unselectedCover_tsum] at hh
  have hsm := hsmallP hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hsource HZ
  have hrem := hremaining s T F hs hT zX (tsupport d.f₀) a b I w M A P K N hd.2.1 hf0
    ha hb hab hI hI1 hJI hM hA hP hL (zero_lt_one.trans_le hw) hwP hIP hK hNc (HZ zX hzX) HZ
  have hright : (∑'i : DirectOuterIndex N×ℕ,({i : DirectOuterIndex N×ℕ |
      sourceRepresentative (i.1 0).val≤128*P ∧
      cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
      (fun i=>cost (directOuterBin T w i.1 i.2)) i)≤ENNReal.ofReal (Cr*(1+K^4)*B) := by
    change (∑'i : DirectOuterIndex N×ℕ,({i : DirectOuterIndex N×ℕ |
      sourceRepresentative (i.1 0).val≤128*P ∧
      cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
      (fun i=>cost (relativeRepresentativeClosedBin T w
        ![(i.1 0).val,(i.1 1).val,(i.1 2).val,i.2] (i.1 3).val)) i)≤_
    rw [directOuter_remaining_sum P (fun np nf nt j nr=>cost (relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j))]
    exact hrem
  apply hh.trans ((add_le_add hsm hright).trans_eq ?_)
  rw [←ENNReal.ofReal_add (mul_nonneg hCs hB) (by positivity)]
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.unselected_label_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A : ℝ,1≤M → 1≤A → ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      I≤(w/P)^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (ψ : ℝ→ℝ),Measurable ψ → (∀t,|ψ t|≤1) → (∀t∉Icc a b,ψ t=0) →
      ENNReal.ofReal ‖∫p : ℝ×Phase,unselectedLabelSignedForce s F.flow zX T
        (bulkSelection P M A w I) ψ p‖ ≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Ct,hCt,htransport⟩ := hd.unselected_transport_uniform T₀
  obtain ⟨Cs,hCs,hsource⟩ := hd.unselected_source_uniform T₀
  refine ⟨Ct+Cs,add_nonneg hCt hCs,?_⟩
  intro M A hM hA
  filter_upwards [hsource M A hM hA] with P hso
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ hψ1 hout
  let Q := bulkSelection P M A w I
  let W : ℝ→Vec→L[ℝ]Vec := fun t=>ψ t • ContinuousLinearMap.id ℝ Vec
  have hW : Measurable W := hψ.smul measurable_const
  have hW1 (t : ℝ) (_ht : t∈Icc a b) : ‖W t‖≤1 := by
    dsimp [W]
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (abs_nonneg _)).trans (by simpa using hψ1 t)
  have ht := htransport M A P hM (zero_le_one.trans hA) hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI
    (zero_lt_one.trans_le hw) hwP hphysical hband HZ W hW hW1
  have hs' := hso hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ W hW hW1
  have he (p : ℝ×Phase) : unselectedLabelSignedForce s F.flow zX T Q ψ p=
      (Icc a b).indicator W (labelReceiverTime F.flow zX T p)
        ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p) := by
    by_cases hp : labelReceiverTime F.flow zX T p∈Icc a b
    · rw [indicator_of_mem hp]
      simp only [unselectedLabelSignedForce,W,smul_apply,ContinuousLinearMap.id_apply]
      exact smul_comm _ _ _
    · rw [indicator_of_notMem hp]
      simp [unselectedLabelSignedForce,hout _ hp]
  have hsplit := F.unselected_force_label_integral_split hs.energyPrefix zX Q (J:=Icc a b) hW measurableSet_Icc
  rw [F.selectedConeTriangle_norm_transfer hs.energyPrefix hT zX Qᶜ
      ((F.transportOnlyConeKernel_continuousOn zX).mono inter_subset_left) hW measurableSet_Icc,
    F.selectedConeTriangle_norm_transfer hs.energyPrefix hT zX Qᶜ
      ((F.sourceOnlyConeKernel_continuousOn hs.energyPrefix zX).mono inter_subset_left) hW measurableSet_Icc] at hsplit
  have hn : ENNReal.ofReal ‖∫p,unselectedLabelSignedForce s F.flow zX T Q ψ p‖≤
      ∫⁻p,ENNReal.ofReal ‖unselectedLabelSignedForce s F.flow zX T Q ψ p‖ := by
    simpa only [ofReal_norm] using (enorm_integral_le_lintegral_enorm
      (f:=unselectedLabelSignedForce s F.flow zX T Q ψ))
  apply hn.trans
  simp_rw [he]
  apply (hsplit.trans (add_le_add ht hs')).trans_eq
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end RVM

end

end OAI
