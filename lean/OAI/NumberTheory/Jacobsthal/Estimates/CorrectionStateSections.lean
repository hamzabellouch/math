import OAI.NumberTheory.Jacobsthal.Analysis.CorrectionWeightedIntegral

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.InvariantInverseWeights
open NumberTheoryLean.TransitionKernels
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.OrdinaryKernelInvariance
open Erdos970Dependency.InvariantFiniteness Erdos970Dependency.InvariantDensities
open Erdos970Dependency.RawStateCost

theorem even_inverse_product (G : State → ℝ) (t : ℝ) :
    Erdos970Dependency.InvariantDensities.evenDensity t*
      (G (.inl (evenLift t))/stateWeight (.inl (evenLift t)))=
    (Ici (2:ℝ)).indicator (fun t => G (.inl (evenLift t))) t := by
  by_cases ht : 2 ≤ t
  · have hl : (evenLift t).1=t := max_eq_right (by linarith)
    have hw : stateWeight (.inl (evenLift t))=NumberTheoryLean.DerivativeWeights.phiEven t := by
      change NumberTheoryLean.DerivativeWeights.phiEven (evenLift t).1=_
      rw [hl]
    rw [Erdos970Dependency.InvariantDensities.evenDensity,
      indicator_of_mem (show t ∈ Ici (2:ℝ) from ht),
      indicator_of_mem (show t ∈ Ici (2:ℝ) from ht),hw]
    field_simp [(NumberTheoryLean.DerivativeWeights.phiEven_pos (by linarith : 1 < t)).ne']
  · rw [Erdos970Dependency.InvariantDensities.evenDensity,
      indicator_of_notMem (show t ∉ Ici (2:ℝ) from ht),
      indicator_of_notMem (show t ∉ Ici (2:ℝ) from ht),zero_mul]

theorem odd_inverse_product (G : State → ℝ) (t : ℝ) :
    Erdos970Dependency.InvariantDensities.oddDensity t*
      (G (.inr (oddLift t))/stateWeight (.inr (oddLift t)))=
    (Ici (1:ℝ)).indicator (fun t => oddFactor t*G (.inr (oddLift t))) t := by
  by_cases ht : 1 ≤ t
  · have hl : (oddLift t).1=t := max_eq_right (by linarith)
    have hw : stateWeight (.inr (oddLift t))=NumberTheoryLean.DerivativeWeights.phiOdd t := by
      change NumberTheoryLean.DerivativeWeights.phiOdd (oddLift t).1=_
      rw [hl]
    rw [Erdos970Dependency.InvariantDensities.oddDensity,
      indicator_of_mem (show t ∈ Ici (1:ℝ) from ht),
      indicator_of_mem (show t ∈ Ici (1:ℝ) from ht),hw]
    field_simp [(NumberTheoryLean.DerivativeWeights.phiOdd_pos t).ne']
  · rw [Erdos970Dependency.InvariantDensities.oddDensity,
      indicator_of_notMem (show t ∉ Ici (1:ℝ) from ht),
      indicator_of_notMem (show t ∉ Ici (1:ℝ) from ht),zero_mul]

theorem state_inverse_integral {G : State → ℝ} (hG : Measurable G)
    (hi : Integrable (fun s => G s/stateWeight s) stateMeasure) :
    (∫ s : State,G s/stateWeight s ∂stateMeasure)=
      (∫ t in Ici 2,G (.inl (evenLift t)))+
      ∫ t in Ici 1,oddFactor t*G (.inr (oddLift t)) := by
  have hq : Measurable (fun s => G s/stateWeight s) := hG.div stateWeight_measurable
  rw [stateMeasure] at hi ⊢
  rw [integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
    integral_map measurable_inl.aemeasurable hq.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable hq.aestronglyMeasurable]
  have he := integral_map (μ := evenMeasure) evenLift_measurable.aemeasurable
    (hq.comp measurable_inl).aestronglyMeasurable
  have ho := integral_map (μ := oddMeasure) oddLift_measurable.aemeasurable
    (hq.comp measurable_inr).aestronglyMeasurable
  simp only [Function.comp_def] at he ho
  rw [evenStateMeasure,he,oddStateMeasure,ho,integral_evenMeasure,integral_oddMeasure]
  simp_rw [even_inverse_product,odd_inverse_product]
  rw [integral_indicator measurableSet_Ici,integral_indicator measurableSet_Ici]

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open NumberTheoryLean.InvariantInverseWeights
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.OrdinaryKernelInvariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound

noncomputable def cutoffAmplitude (L A B : ℝ) (s : State) : ℝ :=
  if stateRatio s < L then Sum.elim (fun _ => A) (fun _ => B) s else 0

theorem cutoffAmplitude_measurable (L A B : ℝ) : Measurable (cutoffAmplitude L A B) :=
  Measurable.ite (measurableSet_lt stateRatio_measurable measurable_const)
    (measurable_const.sumElim measurable_const) measurable_const

theorem cutoffAmplitude_integral (L A B : ℝ)
    (hi : Integrable (fun s => cutoffAmplitude L A B s/stateWeight s) stateMeasure) :
    (∫ s : State,cutoffAmplitude L A B s/stateWeight s ∂stateMeasure)=
      A*(∫ _t : ℝ in Ico 2 L,1)+B*(∫ t : ℝ in Ico 1 L,oddFactor t) := by
  rw [state_inverse_integral (cutoffAmplitude_measurable L A B) hi]
  have he : (Ici (2:ℝ)).indicator (fun t => cutoffAmplitude L A B (.inl (evenLift t)))=
      (Ico (2:ℝ) L).indicator (fun _ => A) := by
    funext t
    by_cases ht : 2 ≤ t
    · have hl : stateRatio (.inl (evenLift t))=t := max_eq_right (by linarith)
      by_cases hL : t < L
      · simp [indicator_of_mem (show t ∈ Ici (2:ℝ) from ht),
          indicator_of_mem (show t ∈ Ico (2:ℝ) L from ⟨ht,hL⟩),cutoffAmplitude,hl,hL]
      · simp [indicator_of_mem (show t ∈ Ici (2:ℝ) from ht),
          cutoffAmplitude,hl,hL]
    · simp [indicator_of_notMem (show t ∉ Ici (2:ℝ) from ht),
        indicator_of_notMem (show t ∉ Ico (2:ℝ) L from fun h => ht h.1)]
  have ho : (Ici (1:ℝ)).indicator (fun t => oddFactor t*cutoffAmplitude L A B (.inr (oddLift t)))=
      (Ico (1:ℝ) L).indicator (fun t => B*oddFactor t) := by
    funext t
    by_cases ht : 1 ≤ t
    · have hl : stateRatio (.inr (oddLift t))=t := max_eq_right (by linarith)
      by_cases hL : t < L
      · simp [indicator_of_mem (show t ∈ Ici (1:ℝ) from ht),
          indicator_of_mem (show t ∈ Ico (1:ℝ) L from ⟨ht,hL⟩),cutoffAmplitude,hl,hL,mul_comm]
      · simp [indicator_of_mem (show t ∈ Ici (1:ℝ) from ht),
          cutoffAmplitude,hl,hL]
    · simp [indicator_of_notMem (show t ∉ Ici (1:ℝ) from ht),
        indicator_of_notMem (show t ∉ Ico (1:ℝ) L from fun h => ht h.1)]
  rw [← integral_indicator measurableSet_Ici,← integral_indicator measurableSet_Ici,
    he,ho,integral_indicator measurableSet_Ico,integral_indicator measurableSet_Ico,integral_const_mul]
  simp [mul_comm]

theorem fullWeighted_cutoff (u : ℝ) (s : State) :
    fullWeighted (u,s)=cutoffAmplitude (Real.exp u/2)
      ((Real.exp u)^2/costMass*extendedSignedAnomaly .even (Real.exp u))
      ((Real.exp u)^2/costMass*extendedSignedAnomaly .odd (Real.exp u)) s/stateWeight s := by
  unfold fullWeighted density rawTest fullAnomalyTest cutoffAmplitude
  cases s <;> simp only [stateSide,Sum.elim_inl,Sum.elim_inr]
  all_goals split_ifs <;> ring

theorem fullWeighted_section (u : ℝ) :
    (∫ s : State,fullWeighted (u,s) ∂stateMeasure)=
      (Real.exp u)^2/costMass*(extendedSignedAnomaly .even (Real.exp u)*(∫ _t : ℝ in Ico 2 (Real.exp u/2),1)+
        extendedSignedAnomaly .odd (Real.exp u)*(∫ t : ℝ in Ico 1 (Real.exp u/2),oddFactor t)) := by
  have hi := fullWeighted_section_integrable u
  simp_rw [fullWeighted_cutoff] at hi ⊢
  rw [cutoffAmplitude_integral _ _ _ hi]
  ring

theorem even_cutoff_length (L : ℝ) : (∫ _t : ℝ in Ico 2 L,1)=if 2 < L then L-2 else 0 := by
  by_cases h : 2 < L
  · rw [ite_eq_left h,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le h.le]
    simp
  · rw [ite_eq_right h,Ico_eq_empty_of_le (le_of_not_gt h)]
    simp

theorem odd_cutoff_length (L : ℝ) :
    (∫ t : ℝ in Ico 1 L,oddFactor t)=if 1 < L then L+1/L-2 else 0 := by
  by_cases h : 1 < L
  · rw [ite_eq_left h,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le h.le,integral_oddFactor h.le]
  · rw [ite_eq_right h,Ico_eq_empty_of_le (le_of_not_gt h)]
    simp

noncomputable def radialNumerator (r : ℝ) : ℝ :=
  (if 4 < r then r*(r/2-2)*continuousAnomaly .even r else 0)-
    (if 2 < r then (r^2/2-2*r+2)*continuousAnomaly .odd r else 0)

theorem fullWeighted_section_radial (u : ℝ) :
    (∫ s : State,fullWeighted (u,s) ∂stateMeasure)=Real.exp u/costMass*radialNumerator (Real.exp u) := by
  rw [fullWeighted_section,even_cutoff_length,odd_cutoff_length]
  have hr : 0 < Real.exp u := Real.exp_pos _
  have h4 : (2:ℝ) < Real.exp u/2 ↔ 4 < Real.exp u := by constructor <;> intro h <;> linarith
  have h2 : (1:ℝ) < Real.exp u/2 ↔ 2 < Real.exp u := by constructor <;> intro h <;> linarith
  simp only [h4,h2,radialNumerator]
  by_cases hh2 : 2 < Real.exp u
  · have he : extendedSignedAnomaly .even (Real.exp u)=continuousAnomaly .even (Real.exp u) := by
      simp [extendedSignedAnomaly,max_eq_right hh2.le,sideSign]
    have ho : extendedSignedAnomaly .odd (Real.exp u)=-continuousAnomaly .odd (Real.exp u) := by
      simp [extendedSignedAnomaly,max_eq_right hh2.le,sideSign]
    rw [he,ho,ite_eq_left hh2]
    split_ifs <;> field_simp <;> ring
  · have hh4 : ¬4 < Real.exp u := by linarith
    simp only [ite_eq_right hh2,ite_eq_right hh4,mul_zero,add_zero,sub_zero]

end ErdosCorrectionLimit

end

end Erdos970

end OAI
