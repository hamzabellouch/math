import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.GeometryCutoffStableLogSum

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.physicalProjectedRemainder_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V K : ℝ→Vec)
    {z : ConeCoordinate} {w : ℝ} (hr : z.2.1∈Icc 0 T) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z=0 := by
  unfold physicalProjectedRemainderDensity
  suffices h : (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖angularMultiplierCLM w (V z.1)
        ((s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (1-dot z.2.2.1 (velocity (V z.1)))) •
          signedRemainder (z.1-z.2.1) (velocity (V z.1)) (velocity v) z.2.2.1
            (fderiv ℝ velocity (V z.1) (K z.1)))‖)=0 by rw [h,mul_zero]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_coneBinMomentumSet _ _ _)] with v hv
  have hf : s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))=0 := by
    by_contra hc
    have hq := F.eulerian_supported_momentum hs hP hr _ v hc
    have hidx := representativeClosedBin_source_indices (sphere_norm z.2.2) hv
      ((mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤1024)).trans hN)
    have hp : sourceRepresentative (k 0)≤128*P := by
      have hh : sourceRepresentative (k 0)/128≤q v := hv.1.1
      linarith only [hh,hq]
    exact hk ⟨hidx.1,hidx.2,hp⟩
  simp only [hf,zero_mul,zero_smul,map_zero,norm_zero,ENNReal.ofReal_zero,Pi.zero_apply]

lemma PhaseFlowOn.physicalProjectedRemainder_integral_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V K : ℝ→Vec) (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (w : ℝ) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  exact F.physicalProjectedRemainder_source_truncate hs hP N hN X V K
    ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ k hk

lemma Admissible.projected_remainder_stable_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let K := prefixMomentumForce s F.flow T zX
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
        32≤cappedRepresentative (k 2)*w ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  classical
  obtain ⟨Cs,hCs,hcentral⟩ := hd₀.central_density_stable_log_sum
  obtain ⟨Cr,hCr,hremainder⟩ := hd₀.projected_remainder_selected_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  let C := Cs+Cr*Cn^2
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hsource hband HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let W := ∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖
  let E := ∫x : Vec,totalEnergy s (0,x)
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
    32≤cappedRepresentative (k 2)*w ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
  let stable : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1)≤cappedRepresentative (k 2)/16 ∧
    32≤cappedRepresentative (k 2)*w}
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P}
  let Q := source∩sector
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator rfun=Q.indicator rfun := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,indicator_of_mem (show k∈Q from ⟨hsrc,hk⟩)]
      · rw [indicator_of_mem hk,indicator_of_notMem (show k∉Q from fun h=>hsrc h.1)]
        exact F.physicalProjectedRemainder_integral_source_truncate hs hsource N hN X V K
          hα.snd.measurable measurableSet_Icc hJ w k hsrc
    · rw [indicator_of_notMem hk,indicator_of_notMem (show k∉Q from fun h=>hk h.2)]
  have hQ : ∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1)≤cappedRepresentative (k 2) ∧
      sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1 := by
    intro k hk
    refine ⟨hk.1.1,hk.1.2.1,?_,hk.2.2.2⟩
    have hh := hk.2.1
    have hφ := cappedRepresentative_pos (k 2)
    linarith only [hh,hφ]
  have hcsub : (∑'k : Fin 4→ℕ,Q.indicator cfun k)≤∑'k : Fin 4→ℕ,stable.indicator cfun k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk,indicator_of_mem (show k∈stable from ⟨hk.2.1,hk.2.2.1⟩)]
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hc : (∑'k : Fin 4→ℕ,Q.indicator cfun k)≤
      ENNReal.ofReal (C*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
    apply (hcsub.trans (hcentral s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab
      hM hA hP hL hw hwP hsource HX HZ)).trans
    apply ENNReal.ofReal_le_ofReal
    have hCsC : Cs≤C := by dsimp [C]; linarith only [mul_nonneg hCr (sq_nonneg Cn)]
    gcongr
  have hN2 : Cr*Real.sqrt (max 1 T)*(N:ℝ)^2/w≤C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w := by
    apply div_le_div_of_nonneg_right _ hw.le
    calc
      _ ≤ Cr*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _) (by positivity)
      _ = (Cr*Cn^2)*Real.sqrt (max 1 T)*(Real.log (2+P))^2 := by ring
      _ ≤ _ := by
        have hh : Cr*Cn^2≤C := by dsimp [C]; linarith only [hCs]
        gcongr
  change (∑'k : Fin 4→ℕ,sector.indicator rfun k)≤_
  rw [heq]
  exact (hremainder s T F hs hT h0 zX (Icc a b) w N Q hQ measurableSet_Icc hJ hw hband).trans
    (add_le_add hc (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hN2)))

end RVM

end

end OAI
