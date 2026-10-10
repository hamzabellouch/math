import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.DirectionCutoffs
import OAI.Analysis.VlasovMaxwell.Retarded.SelectedConeTransfer

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def remainderConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  normalisedRemainder (p.1.1-p.1.2) (velocity (α zX p.1.1).2)
    (velocity p.2.2.2) p.2.1 (phaseAcceleration s.E s.B α zX p.1.1)

lemma selectedConeTriangle_norm_le {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ)
    (p : TrianglePhase) :
    ‖selectedConeTriangle s α zX T Q A W J p‖≤
      ‖J.indicator W p.1.1 (triangleConeKernel s α zX T A p)‖ := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · have hr : 0<p.1.1-p.1.2.1 := sub_pos.mpr hp.2.2
    have hrT : p.1.1-p.1.2.1≤ max 1 T := by
      linarith only [hp.1.2,hp.2.1,le_max_right (1:ℝ) T]
    have hu := selectedDyadicCutoff_mem_unit
      (physicalCutoffCoordinates_pos (T:=T) (v:=p.2) (w:=(α zX p.1.1).2) (sphere_norm p.1.2.2) hr)
      (physicalCutoffCoordinates_le_one (T:=T) (sphere_norm p.1.2.2) hrT) Q
    have he : selectedConeTriangle s α zX T Q A W J p=
        stateCutoff T Q (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(α zX p.1.1).2) •
          J.indicator W p.1.1 (triangleConeKernel s α zX T A p) := by
      simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_mem hp,
        selectedConeKernel,coneCutoffState,triangleKernelState,map_smul]
      module
    rw [he,norm_smul,Real.norm_eq_abs]
    change |selectedDyadicCutoff Q _| * _ ≤ _
    rw [abs_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)).trans_eq (one_mul _)
  · simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_notMem hp,map_zero]
    exact le_rfl

lemma PhaseFlowOn.selectedRemainderTriangle_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (remainderConeKernel s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalProjectedRemainderDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B w (prefixMomentumForce s F.flow T zX) z := by
  classical
  unfold physicalProjectedRemainderDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J (z,v))).trans
  rw [Set.indicator_of_mem hz.1]
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have ht := hJT hz.1
    have he : (prefixAngularMultiplier s F.flow T w hw zX) z.1
        (triangleConeKernel s F.flow zX T (remainderConeKernel s F.flow zX) (z,v))=
        (z.1-z.2.1)^2 • angularMultiplierCLM w (prefixFlow F.flow T zX z.1).2
          ((s.f (z.2.1,((prefixFlow F.flow T zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
              (1-dot z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2))) •
            signedRemainder (z.1-z.2.1) (velocity (prefixFlow F.flow T zX z.1).2) (velocity v) z.2.2.1
              (fderiv ℝ velocity (prefixFlow F.flow T zX z.1).2 (prefixMomentumForce s F.flow T zX z.1))) := by
      simp only [triangleConeKernel,Set.indicator_of_mem hp,remainderConeKernel,triangleKernelState,
        normalisedRemainder_eq _ _ _ _ (sub_pos.mpr hp.2.2).ne',
        (prefixAngular_highband hw zX ht (hband _ hz.1)).1,
        phaseAcceleration,prefixFlow,prefixMomentumForce,prefixClamp_eq ht,lorentzField,lorentzPhase,map_smul]
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_mul (sq_nonneg _)]
  · simp only [triangleConeKernel,Set.indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.selectedRemainder_label_physical_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Q p • actualLabelRemainder s F.flow zX T p)‖)≤
      ∑'k : Fin 4→ℕ,Q.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) w
          (prefixMomentumForce s F.flow T zX) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  classical
  have hA : ContinuousOn (remainderConeKernel s F.flow zX) (coneKernelInterior T) :=
    (F.normalised_remainder_continuousOn hs zX).mono inter_subset_left
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  rw [F.actualLabelRemainder_eq_normalised zX]
  change (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
    (labelReceiverTime F.flow zX T p)
    (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T (remainderConeKernel s F.flow zX) p)‖)≤_
  rw [F.selectedConeTriangle_norm_transfer hs hT zX Q hA hW hJ]
  apply (F.selectedConeTriangle_physical_sum hs hT zX Q hA hW hJ hJT hq).trans
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈Q
  · rw [Set.indicator_of_mem hk,Set.indicator_of_mem hk]
    apply lintegral_mono_ae
    have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) hJ)] with z hz
    exact F.selectedRemainderTriangle_density_le hw zX Q hJT hband _ hz
  · rw [Set.indicator_of_notMem hk,Set.indicator_of_notMem hk]

lemma Admissible.direction_remainder_label_log_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤ C ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → b-a≤(w/P)^2 →
      0< M → 0≤ A → 0< P → 1≤ Real.log (2+P) → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (labelSelectedCutoff F.flow zX T (directionSelection T) p • actualLabelRemainder s F.flow zX T p)‖)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.projected_remainder_small_sector_log_sum
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hw hS hS0 ha hb hJI hM hA hP hL hwP hPw hsource hq hW HX HZ
  dsimp only
  apply (F.selectedRemainder_label_physical_sum hs hT hw zX (directionSelection T)
    measurableSet_Icc (Icc_subset_Icc ha hb) hq hW).trans
  let sector : Set (Fin 4→ℕ) := {k | cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
  have hsub : directionSelection T⊆sector := by
    intro k hk
    refine ⟨?_,hk.2⟩
    have hφ := cappedRepresentative_pos (k 2)
    linarith only [hk.1,hφ]
  apply (tsum_set_indicator_mono hsub _).trans
  exact hbound s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hJI hM hA hP hL hw hwP hPw hsource hW HX HZ

end RVM

end

end OAI
