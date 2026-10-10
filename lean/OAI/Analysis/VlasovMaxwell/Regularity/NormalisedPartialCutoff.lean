import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SelectionWeight
import OAI.Analysis.VlasovMaxwell.Retarded.SourceForceConeKernel
import OAI.Analysis.VlasovMaxwell.Retarded.ConeKernelInterior

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

lemma PhaseFlowOn.labelConeKernel_triangle_norm_localBorel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hm : Measurable ((coneKernelInterior T).indicator A)) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  classical
  rw [←F.labelConeKernel_interior_indicator zX A,
    F.labelConeKernel_triangle_norm_borel hs hT zX hm]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro σ hσ
  apply lintegral_congr
  intro n
  congr 1
  apply lintegral_congr
  intro v
  have hp : ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))∈coneKernelInterior T :=
    ⟨⟨⟨Ioo_subset_Icc_self ht,⟨hσ.1.le,(hσ.2.trans ht.2).le⟩⟩,
      ⟨n.2,mem_univ _⟩⟩,hσ.2⟩
  rw [indicator_of_mem hp]

def normalisedPartialCutoff (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState) (p : ConeKernelState) : Vec :=
  fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX p) (H p) •
    normalisedPrimitive (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

lemma PhaseFlowOn.normalisedPartialCutoff_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {H : ConeKernelState→CutoffState} (hH : ContinuousOn H (coneKernelInterior T)) :
    ContinuousOn (normalisedPartialCutoff F.flow zX T Q H) (coneKernelInterior T) := by
  have hz := F.coneCutoffState_continuousOn zX
  have hder : ContinuousOn (fun p=>fderiv ℝ (stateCutoff T Q) (coneCutoffState F.flow zX p))
      (coneKernelInterior T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (z:=coneCutoffState F.flow zX p)
      (sub_pos.mpr hp.2) (by simpa only [coneCutoffState,mem_sphere,dist_zero_right] using hp.1.2.1)).continuousAt_fderiv
        (by simp)).comp_continuousWithinAt (hz p hp)
  exact (hder.clm_apply hH).smul ((F.normalised_primitive_continuousOn zX).mono inter_subset_left)

lemma PhaseFlowOn.partialCutoffLabelCost_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (H : ConeKernelState→CutoffState) :
    partialCutoffLabelCost s F.flow zX T Q (H ∘ labelKernelState F.flow zX T)=
      labelConeKernel s F.flow zX T (normalisedPartialCutoff F.flow zX T Q H) := by
  classical
  funext p
  rw [partialCutoffLabelCost,F.actualLabelPrimitive_eq_normalised zX]
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hj : p∈jointBranchDomain F.flow zX T := hp
    rw [indicator_of_mem hj]
    simp only [labelConeKernel,indicator_of_mem hp]
    simp only [normalisedPartialCutoff,coneCutoffState,labelKernelState,
      branchCutoffState,Function.comp_apply]
    module
  · have hj : p∉jointBranchDomain F.flow zX T := hp
    simp only [indicator_of_notMem hj,labelConeKernel,indicator_of_notMem hp,zero_smul]

lemma localBorel_clm_apply {T : ℝ} {A : ConeKernelState→Vec}
    (hA : Measurable ((coneKernelInterior T).indicator A))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) :
    Measurable ((coneKernelInterior T).indicator (fun p=>W p.1.1 (A p))) := by
  classical
  have he : (coneKernelInterior T).indicator (fun p=>W p.1.1 (A p))=
      fun p=>W p.1.1 ((coneKernelInterior T).indicator A p) := by
    funext p
    by_cases hp : p∈coneKernelInterior T
    · rw [indicator_of_mem hp,indicator_of_mem hp]
    · rw [indicator_of_notMem hp,indicator_of_notMem hp,map_zero]
  rw [he]
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp ((hW.comp measurable_fst.fst).prodMk hA)

lemma PhaseFlowOn.partialCutoffLabelCost_multiplier_polar {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q (H ∘ labelKernelState F.flow zX T) p)‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖W t (s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          normalisedPartialCutoff F.flow zX T Q H
            ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v))))‖ ∂volume ∂sphereMeasure := by
  classical
  have hh := F.normalisedPartialCutoff_continuousOn zX Q hH
  have hm : Measurable ((coneKernelInterior T).indicator
      (normalisedPartialCutoff F.flow zX T Q H)) :=
    hh.measurable_piecewise continuousOn_const (measurableSet_coneKernelInterior T)
  have he := F.labelConeKernel_triangle_norm_localBorel hs hT zX (localBorel_clm_apply hm hW)
  simpa only [labelConeKernel_receiver_multiplier,F.partialCutoffLabelCost_eq_normalised zX Q H,map_smul] using he

lemma product_le_min_scale {P p w : ℝ} (hp : 0≤p) (hw : 0≤w)
    (hpP : p≤P) (hwP : w≤P) : w*p≤P*min p w := by
  rcases le_total p w with h|h
  · rw [min_eq_left h]
    exact mul_le_mul_of_nonneg_right hwP hp
  · rw [min_eq_right h]
    calc w*p≤w*P := mul_le_mul_of_nonneg_left hpP hw
         _ = P*w := by ring

lemma sqrt_div_stabilityLength {P C M A p w φ I : ℝ}
    (hP : 0≤P) (hC : 0≤C) (hM : 0≤M) (hp : 0≤p) (hw : 0≤w)
    (hφ : 0≤φ) (hI : 0≤I) :
    Real.sqrt (I/stabilityLength P C M A p w φ)=
      Real.sqrt I*stabilityRate P C M A p w φ := by
  rw [div_stabilityLength,Real.sqrt_mul hI,Real.sqrt_sq]
  unfold stabilityRate
  positivity

lemma direction_baseline_R_bound {P C M A p w φ : ℝ}
    (hP : 0<P) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      w*(1+C*(M+Real.sqrt (A*Real.log (2+P)))) := by
  have hL : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
  have hm : 0 < min p w := lt_min hp hw
  have hwp := product_le_min_scale hp.le hw.le hpP hwP
  have hmain : w^2*p/(P*min p w)≤w := by
    apply (div_le_iff₀ (mul_pos hP hm)).mpr
    nlinarith
  have hfirst : w*p*φ/P≤w := by
    apply (div_le_iff₀ hP).mpr
    have hh : p*φ≤P := (mul_le_of_le_one_right hp.le hφ1).trans hpP
    nlinarith
  have hroot : φ*Real.sqrt (A*Real.log (2+P)/φ)=
      Real.sqrt (A*Real.log (2+P)*φ) := by
    calc
      _ = Real.sqrt (φ^2)*Real.sqrt (A*Real.log (2+P)/φ) := by rw [Real.sqrt_sq hφ.le]
      _ = Real.sqrt (A*Real.log (2+P)*φ) := by
        rw [←Real.sqrt_mul (sq_nonneg φ)]
        congr 1
        field_simp
  have hsqrt : Real.sqrt (A*Real.log (2+P)*φ)≤Real.sqrt (A*Real.log (2+P)) :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right (mul_nonneg hA hL) hφ1)
  rw [Real.sqrt_sq (div_nonneg hw.le hP.le),
    sqrt_div_stabilityLength hP.le hC hM hp.le hw.le hφ.le (sq_nonneg _),
    Real.sqrt_sq (div_nonneg hw.le hP.le)]
  have he : (w/P)*(1+(w/P)*stabilityRate P C M A p w φ)*p*φ=
      w*p*φ/P+C*(w^2*p/(P*min p w))*(M+φ*Real.sqrt (A*Real.log (2+P)/φ)) := by
    unfold stabilityRate
    field_simp
  rw [he,hroot]
  calc
    _ ≤ w+C*w*(M+Real.sqrt (A*Real.log (2+P))) := by gcongr
    _ = _ := by ring

lemma direction_baseline_R_log_bound {P C M A p w φ : ℝ}
    (hP : 0<P) (hL : 1≤Real.log (2+P)) (hC : 0≤C) (hM : 0≤M) (hA : 0≤A)
    (hp : 0<p) (hw : 0<w) (hφ : 0<φ) (hφ1 : φ≤1)
    (hpP : p≤P) (hwP : w≤P) :
    Real.sqrt ((w/P)^2)*(1+Real.sqrt (((w/P)^2)/stabilityLength P C M A p w φ))*p*φ≤
      (1+C*(M+Real.sqrt A))*w*Real.sqrt (Real.log (2+P)) := by
  apply (direction_baseline_R_bound hP hC hM hA hp hw hφ hφ1 hpP hwP).trans
  rw [Real.sqrt_mul hA]
  have hroot : 1≤Real.sqrt (Real.log (2+P)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have h0 : 0≤1+C*M := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hroot (mul_nonneg hw.le h0)]

end RVM

end

end OAI
