import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.UnselectedCover
import OAI.Analysis.VlasovMaxwell.Retarded.DirectSmallAbsolute

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

def directMixedSector (P : ℝ) (N : ℕ) : Set (UnselectedCoverIndex N) :=
  {i | match i with
    | .inl k => k∈representativeSmallSector P
    | .inr i => sourceRepresentative (i.1 0).val≤128*P ∧
        cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}

lemma directMixed_tsum {N : ℕ} (T P w : ℝ) (f : ClosedConeBin→ℝ≥0∞) :
    (∑'i : UnselectedCoverIndex N,(directMixedSector P N).indicator
      (fun i=>f (unselectedCoverBin T w i)) i)=
    (∑'k : Fin 4→ℕ,(representativeSmallSector P).indicator (fun k=>f (representativeClosedBin T w k)) k)+
    (∑'i : DirectOuterIndex N×ℕ,({i : DirectOuterIndex N×ℕ |
      sourceRepresentative (i.1 0).val≤128*P ∧
      cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
      (fun i=>f (directOuterBin T w i.1 i.2)) i) := by
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  rfl

lemma physical_direct_mixed_cover {T P w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {N : ℕ} (hP : 0≤P) (hwP : w≤P) (hN : 8192*P≤(2:ℝ)^N)
    (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t) (hb : q (V t)∈Icc (w/8) (8*w))
    (n : Sphere) (v : Vec) (hv : 1024*q v≤P) :
    ∃i∈directMixedSector P N,
      ((t,σ,n),v)∈physicalBinPhaseSet V (unselectedCoverBin T w i) J := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ≤ max 1 T := by linarith [le_max_right (1:ℝ) T,hσ.1]
  obtain ⟨k,hpos⟩ := exists_dyadicMultiFactor_positive
    (physicalCutoffCoordinates_pos (v:=v) (w:=V t) (sphere_norm n) hr)
    (physicalCutoffCoordinates_le_one (v:=v) (w:=V t) (sphere_norm n) hrT)
  have hsource : sourceRepresentative (k 0)≤P :=
    (sourceRepresentative_mem_range (dyadicMultiFactor_positive_bands hpos 0) hv).2
  have hfloor := physicalCutoff_positive_source_floor (sphere_norm n) hpos
  by_cases hrem : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)
  · obtain ⟨i,hi,hmem⟩ := physical_remaining_active_finite_cover
      (T:=T) (P:=P) (w:=w) (V:=V) (J:=J) (N:=N) (k:=k)
      hP hwP hN ht ⟨hσ.1,hσ.2.le⟩ hb n v hv hsource hpos hrem
    exact ⟨.inr i,hi,hmem⟩
  · have hφ := cappedRepresentative_pos (k 2)
    have hn := lt_of_not_ge hrem
    have hs : k∈representativeSmallSector P := ⟨hsource,hfloor,by linarith⟩
    exact ⟨.inl k,hs,physicalCutoff_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hb hpos⟩

lemma directTriangleDensity_mixed_cover {s : Solution} {T P w : ℝ}
    (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hphysical : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    (X V : ℝ→Vec) {J : Set ℝ} (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w))
    (K : TrianglePhase→Vec) (p : TrianglePhase)
    (hp : directTriangleDensity s X T J K p≠0) :
    ∃i∈directMixedSector P N,p∈physicalBinPhaseSet V (unselectedCoverBin T w i) J := by
  have hh := directTriangleDensity_nonzero hp
  have hσ : p.1.2.1∈Icc 0 T := ⟨hh.1.1.2.1.le,hh.1.1.2.2.le.trans hh.1.1.1.2.le⟩
  have hq := hphysical p.1.2.1 hσ _ hh.2
  exact physical_direct_mixed_cover hP hwP hN hh.1.2 hh.1.1.1.2.le
    ⟨hh.1.1.2.1.le,hh.1.1.2.2⟩ (hband _ hh.1.2) p.1.2.2 p.2 hq

lemma directTriangle_mixed_family_estimate {s : Solution} {T P w : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hphysical : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P)
    (X V : ℝ→Vec) (hX : Measurable X) (hV : Measurable V)
    (J : Set ℝ) (hJ : MeasurableSet J) (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w))
    (K : TrianglePhase→Vec) (hK : Measurable K) (f : ClosedConeBin → ConeCoordinate → ℝ≥0∞)
    (hbin : ∀B z,z∈physicalBinBase V B J→
      (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        directTriangleDensity s X T J K (z,v))≤f B z) :
    (∫⁻p,directTriangleDensity s X T J K p ∂trianglePhaseMeasure)≤
      ∑'i : UnselectedCoverIndex N,(directMixedSector P N).indicator
        (fun i=>∫⁻z,f (unselectedCoverBin T w i) z ∂physicalBinMeasure V (unselectedCoverBin T w i) J) i := by
  have hc := physicalBinFamily_cover_lintegral hV hJ (unselectedCoverBin T w) (directMixedSector P N)
    (measurable_directTriangleDensity hs hT hX hJ hK)
    (directTriangleDensity_mixed_cover hP hwP N hN hphysical X V hband K)
  apply hc.trans
  apply ENNReal.tsum_le_tsum
  intro i
  apply indicator_le_indicator
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  exact hbin _ z hz

lemma Admissible.direct_source_absolute_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 1≤A →
      1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I → 1≤w → w≤P →
      I≤(w/P)^2 →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∫⁻p,directTriangleDensity s (fun t=>(prefixFlow F.flow T zX t).1) T (Icc a b)
        (directSourceTriangleKernel s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) T) p ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (C*Real.sqrt w*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := hd.small_source_absolute_uniform T₀
  obtain ⟨Cr,hCr,hremaining⟩ := hd.direct_remaining_source_unrestricted_uniform
  obtain ⟨K,hK,hcount⟩ := exists_direct_dyadic_count
  refine ⟨Cs+Cr*(1+K^4),by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hphysical hband HZ
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let cost := fun B : ClosedConeBin=>∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z
      ∂physicalBinMeasure V B (Icc a b)
  have hB : 0≤B := by dsimp [B]; positivity
  have hf0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    rw [show (fun z=>s.f (0,z))=d.f₀ from funext hs.initial_f]
  have hcont := (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcont.fst.measurable
  have hV : Measurable V := hcont.snd.measurable
  have hband' : ∀t∈Icc a b,q (V t)∈Icc (w/8) (8*w) := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (Icc_subset_Icc ha hb ht)] using hband t ht
  have hh := directTriangle_mixed_family_estimate hs.energyPrefix hT (zero_le_one.trans hP) hwP N hN
    hphysical X V hX hV (Icc a b) measurableSet_Icc hband'
    (directSourceTriangleKernel s X V T) (measurable_directSourceTriangleKernel hs.energyPrefix hT hX hV)
    (physicalDirectSourceDensity s X V) (fun B _ hz=>directSourceTriangle_bin_bound (Icc_subset_Icc ha hb) B hz)
  change _≤∑'i : UnselectedCoverIndex N,(directMixedSector P N).indicator
    (fun i=>cost (unselectedCoverBin T w i)) i at hh
  rw [directMixed_tsum] at hh
  have hsm := hsmall M A P hM (zero_le_one.trans hA) hP hL s T F hs hT hTT zX a b I w
    hzX ha hb hab hI hI1 hJI hw hwP hIP HZ
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
  have hright' : (∑'i : DirectOuterIndex N×ℕ,({i : DirectOuterIndex N×ℕ |
      sourceRepresentative (i.1 0).val≤128*P ∧
      cappedRepresentative (i.1 2).val≤16384*cappedRepresentative (i.1 1).val}).indicator
      (fun i=>cost (directOuterBin T w i.1 i.2)) i)≤ENNReal.ofReal (Cr*(1+K^4)*Real.sqrt w*B) := by
    apply hright.trans
    apply ENNReal.ofReal_le_ofReal
    have hsw : 1≤Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsw (by positivity : 0≤Cr*(1+K^4))) hB
    simpa only [mul_one] using hh
  apply hh.trans ((add_le_add hsm hright').trans_eq ?_)
  rw [←ENNReal.ofReal_add (by positivity : 0≤Cs*Real.sqrt w*B) (by positivity : 0≤Cr*(1+K^4)*Real.sqrt w*B)]
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_transport_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w → w≤P →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∫⁻p,directTriangleDensity s (fun t=>(prefixFlow F.flow T zX t).1) T (Icc a b)
        (directTransportTriangleKernel (fun t=>(prefixFlow F.flow T zX t).2)) p ∂trianglePhaseMeasure)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cs,hCs,hsmall⟩ := hd.small_transport_uniform T₀
  obtain ⟨Cr,hCr,hremaining⟩ := hd.direct_remaining_transport_uniform_expanded
  obtain ⟨K,hK,hcount⟩ := exists_direct_dyadic_count
  refine ⟨Cs+Cr*max 1 T₀,by positivity,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP hphysical hband HZ
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let cost := fun B : ClosedConeBin=>∫⁻z : ConeCoordinate,physicalDirectTransportDensity s X V B z
      ∂physicalBinMeasure V B (Icc a b)
  have hB : 0≤B := by dsimp [B]; positivity
  have hf0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    rw [show (fun z=>s.f (0,z))=d.f₀ from funext hs.initial_f]
  have hcont := (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  have hX : Measurable X := hcont.fst.measurable
  have hV : Measurable V := hcont.snd.measurable
  have hband' : ∀t∈Icc a b,q (V t)∈Icc (w/8) (8*w) := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (Icc_subset_Icc ha hb ht)] using hband t ht
  have hh := directTriangle_mixed_family_estimate hs.energyPrefix hT (zero_le_one.trans hP) hwP N hN
    hphysical X V hX hV (Icc a b) measurableSet_Icc hband'
    (directTransportTriangleKernel V) (measurable_directTransportTriangleKernel hV)
    (physicalDirectTransportDensity s X V) (fun B _ hz=>directTransportTriangle_bin_bound (Icc_subset_Icc ha hb) B hz)
  change _≤∑'i : UnselectedCoverIndex N,(directMixedSector P N).indicator
    (fun i=>cost (unselectedCoverBin T w i)) i at hh
  rw [directMixed_tsum] at hh
  have hsm := hsmall M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
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

end RVM

end

end OAI
