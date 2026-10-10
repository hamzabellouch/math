import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SpatialEstimates
import OAI.Analysis.VlasovMaxwell.Population.SelectedRemainder

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma labelConeKernel_const_smul (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T c : ℝ) (A : ConeKernelState→Vec) (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun x=>c • A x) p=c • labelConeKernel s α zX T A p := by
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,indicator_of_mem hp]
    simp only [smul_smul]
    congr 1
    ring
  · simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]

lemma PhaseFlowOn.selected_weight_cost_bound {s : Solution} {T I D a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) (hI : 0<I) (hD : 0≤D)
    {ψ : ℝ→ℝ} (hψd : ∀t∈Icc a b,|deriv ψ t|≤D/I)
    (hψout : ∀t∉Icc a b,deriv ψ t=0) :
    (∫⁻p : ℝ×Phase,selectedMultiplierWeightDensity s F.flow zX T Q ψ
      (fun _=>ContinuousLinearMap.id ℝ Vec) p)≤
      ENNReal.ofReal D*(∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q
        (fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p)
        (fun _=>ContinuousLinearMap.id ℝ Vec) (Icc a b) p‖ ∂trianglePhaseMeasure) := by
  have ht := F.selectedConeTriangle_norm_transfer (J:=Icc a b)
    (A:=fun p=>I⁻¹ • normalisedRatePrimitive F.flow zX p)
    hs hT zX Q ((continuousOn_const : ContinuousOn (fun _ : ConeKernelState=>I⁻¹) (coneKernelInterior T)).smul
      ((F.normalisedRatePrimitive_continuousOn zX).mono inter_subset_left))
    (W:=fun _=>ContinuousLinearMap.id ℝ Vec) measurable_const measurableSet_Icc
  rw [←ht,←lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro p
  let τ := labelReceiverTime F.flow zX T p
  by_cases hp : τ∈Icc a b
  · simp only [selectedMultiplierWeightDensity,ContinuousLinearMap.id_apply,
      labelWeight,←smul_smul, norm_smul,Real.norm_eq_abs]
    rw [indicator_of_mem hp,ContinuousLinearMap.id_apply,labelConeKernel_const_smul,
      ←F.actualLabelRatePrimitive_eq s zX,smul_comm (labelSelectedCutoff F.flow zX T Q p),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hI),
      ENNReal.ofReal_mul (inv_nonneg.mpr hI.le)]
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    apply (mul_le_mul' (ENNReal.ofReal_le_ofReal (hψd τ hp)) le_rfl).trans_eq
    rw [div_eq_mul_inv,ENNReal.ofReal_mul hD,mul_assoc,norm_smul,Real.norm_eq_abs]
  · have hz := hψout τ hp
    change deriv ψ (labelReceiverTime F.flow zX T p)=0 at hz
    simp only [selectedMultiplierWeightDensity,labelWeight,hz,zero_mul,zero_smul,
      ContinuousLinearMap.id_apply,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma selected_bulk_weight_le (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) {a b : ℝ} {ψ : ℝ→ℝ}
    (hψ : ∀t,|ψ t|≤1) (hout : ∀t∉Icc a b,ψ t=0) (p : ℝ×Phase) :
    ENNReal.ofReal |ψ (labelReceiverTime α zX T p)| *
      selectedMultiplierBulkDensity s α zX T Q (fun _=>ContinuousLinearMap.id ℝ Vec) p ≤
    selectedMultiplierBulkDensity s α zX T Q
      ((Icc a b).indicator (fun _=>ContinuousLinearMap.id ℝ Vec)) p := by
  by_cases hp : labelReceiverTime α zX T p∈Icc a b
  · simp only [selectedMultiplierBulkDensity,indicator_of_mem hp,ContinuousLinearMap.id_apply]
    have hb : ENNReal.ofReal |ψ (labelReceiverTime α zX T p)|≤1 := by
      simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal (hψ (labelReceiverTime α zX T p)))
    exact (mul_le_mul' hb le_rfl).trans_eq (one_mul _)
  · rw [hout _ hp,abs_zero,ENNReal.ofReal_zero,zero_mul]
    exact bot_le

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.bulk_signed_cost_uniform {d : Datum} (hd : Admissible d) (T₀ D : ℝ) (hD : 0≤D) :
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
    ∀ ψ : ℝ→ℝ, Measurable ψ → (∀t,|ψ t|≤1) →
      (∀t∉Icc a b,ψ t=0) → (∀t∈Icc a b,|deriv ψ t|≤D/I) →
      (∀t∉Icc a b,deriv ψ t=0) →
      ENNReal.ofReal ‖∫p : ℝ×Phase,selectedMultiplierCosts s F.flow zX T
        (bulkSelection P M A w I) ψ (fun _=>ContinuousLinearMap.id ℝ Vec) (fun _=>0) p‖ ≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cb,hCb,hbulk⟩ := hd.bulk_selected_family_uniform T₀
  obtain ⟨Cr,hCr,hrate⟩ := hd.bulk_rate_uniform T₀
  let C := D*Cr+Cb
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hbulk M A hM hA] with P hbu
  intro hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ ψ hψ hψ1 hout hψd hdout
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  let K := ∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
  let Q := bulkSelection P M A w I
  let Id : ℝ→Vec→L[ℝ]Vec := fun _=>ContinuousLinearMap.id ℝ Vec
  have hId : ∀t∈Icc a b,‖Id t‖≤1 := fun _ _=>ContinuousLinearMap.norm_id_le
  have hB : 0≤B := by dsimp [B]; positivity
  have hbc := hbu hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hI1 hJI hw hwP hIP hsrc hphysical hband HZ Id measurable_const hId
  have hrc := hrate M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hab hI hJI hw hwP HZ hphysical hband Id measurable_const hId
  have hwc := (F.selected_weight_cost_bound hs.energyPrefix hT zX Q hI hD hψd hdout).trans
    (mul_le_mul' le_rfl hrc)
  have hbl := (lintegral_mono (selected_bulk_weight_le s F.flow zX T Q hψ1 hout)).trans hbc
  have hc := F.selectedMultiplierCosts_integral_bound hs.energyPrefix zX Q hψ
    (W:=Id) (W':=fun _=>0) measurable_const
  have hz : (∫⁻p : ℝ×Phase,selectedMultiplierMovingDensity s F.flow zX T Q ψ (fun _=>0) p)=0 := by
    simp only [selectedMultiplierMovingDensity,zero_apply,norm_zero,ENNReal.ofReal_zero,lintegral_zero]
  rw [hz,add_zero] at hc
  apply (hc.trans (add_le_add hwc hbl)).trans
  change ENNReal.ofReal D*ENNReal.ofReal (Cr*B)+(ENNReal.ofReal (Cb*B)+ENNReal.ofReal (Cb*w^(-1/2:ℝ))*K)≤_
  rw [←ENNReal.ofReal_mul hD,←add_assoc,←ENNReal.ofReal_add (by positivity) (by positivity)]
  have he : D*(Cr*B)+Cb*B=C*B := by dsimp [C]; ring
  rw [he]
  exact add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (by dsimp [C]; nlinarith [mul_nonneg hD hCr]) (Real.rpow_nonneg (zero_le_one.trans hw) _))) le_rfl)

end RVM

end

end OAI
