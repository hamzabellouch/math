import Mathlib
import OAI.Probability.LogConcave.Complexity.SingleCellBasisBudget
import OAI.Probability.LogConcave.Sampling.CenteringVelocityJoint

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

structure StationaryPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (V : E → E) where
  path : E → ℝ → E
  continuous : ∀y,Continuous (path y)
  initial : ∀y,path y 0=y
  derivative : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (path y) (V (path y t)) (Icc (0:ℝ) 1) t
  measurable : Measurable (fun p : ℝ × E => path p.2 p.1)
  law : ∀t∈Icc (0:ℝ) 1,μ.map (fun y => path y t)=μ

namespace StationaryPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  {μ : Measure E} {V : E → E} (X : StationaryPath μ V)

lemma measurable_slice (t : ℝ) : Measurable (fun y => X.path y t) :=
  X.measurable.comp (measurable_const.prodMk measurable_id)

lemma measurePreserving {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    MeasurePreserving (fun y => X.path y t) μ μ := ⟨X.measurable_slice t,X.law t ht⟩

lemma memLp_slice {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (hi : MemLp (id : E → E) 2 μ) :
    MemLp (fun y => X.path y t) 2 μ := hi.comp_measurePreserving (X.measurePreserving ht)

lemma integral_eq [CompleteSpace E] (hV : Continuous V) (y : E) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) : (∫u in 0..t,V (X.path y u))=X.path y t-y := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (X.continuous y).continuousOn
    (fun u hu => (X.derivative y u ⟨hu.1.le,hu.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2)))
    ((hV.comp (X.continuous y)).intervalIntegrable 0 t)
  simpa only [X.initial] using he
end StationaryPath

lemma centeringTrueVelocity_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hT0 : 0 ≤ T) (hT1 : T<1) (s : ℝ) :
    Continuous (skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)) := by
  let E := productPointEquiv d d
  have hK := (centeringKernel_smooth hF x hr hlam hl hT0 hT1).continuous
  have hM : Continuous (fun z => conditionalFieldMean F x r T z-primitiveExpectedField F x r) :=
    (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).continuous.sub continuous_const
  have hc : Continuous (skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
      (fun z => conditionalFieldMean F x r T z-primitiveExpectedField F x r) s) := by
    exact ((((ContinuousLinearMap.adjoint.continuous.comp hK).comp continuous_fst).clm_apply
      continuous_snd).const_smul (-s⁻¹)).prodMk ((hM.comp continuous_fst).const_smul s⁻¹)
  convert! E.symm.continuous.comp (hc.comp E.continuous) using 1
  funext y
  change _=E.symm (skewCenteringField (centeringKernel hF x hr hl hT0 hT1)
    (fun z => conditionalFieldMean F x r T z-primitiveExpectedField F x r) s (E y))
  dsimp only [E]
  rw [←actual_centering_joint_field hF x hr hlam hl hT0 hT1 s y]
  exact (E.symm_apply_apply _).symm

theorem exists_centering_stationaryPath {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T s : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0<s) :
    Nonempty (StationaryPath (gibbs (centeringPotential F x r T))
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s))) := by
  obtain ⟨Ξ,hc,hd,hm,hlaw⟩ := exists_actual_joint_centering_flow hF x hr hlam hl hT0 hT1 hs
  exact ⟨⟨Ξ,fun y => (hc y).1,fun y => (hc y).2,hd,hm,hlaw⟩⟩

def centeringWeight (n : ℕ) (i j : Fin (n+1)) : ℝ :=
  weight (probabilityNodes n) j 0 (probabilityNodes n i)

def centeringRowBudget (n : ℕ) : ℝ≥0 :=
  ⟨(n+1)*singleCellBasisBudget n,by positivity [(singleCellBasisBudget_spec n).1]⟩

lemma centeringWeight_bound (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    ∑j,|centeringWeight n i j| ≤ centeringRowBudget n := by
  change ∑j,|centeringWeight n i j| ≤ ((n:ℝ)+1)*singleCellBasisBudget n
  have hi := probabilityNodes_mem hn i
  have hb := weights_abs_bound (probabilityNodes n) hi.1 hi.2 (singleCellBasisBudget_spec n).2
  simpa only [centeringWeight,centeringRowBudget,NNReal.coe_mk,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using
    hb.trans (mul_le_of_le_one_right (by positivity [(singleCellBasisBudget_spec n).1]) hi.2)

lemma centeringFullWeight_bound (n : ℕ) :
    ∑j,|weight (probabilityNodes n) j 0 1| ≤ centeringRowBudget n := by
  change ∑j,|weight (probabilityNodes n) j 0 1| ≤ ((n:ℝ)+1)*singleCellBasisBudget n
  simpa only [centeringRowBudget,NNReal.coe_mk,Fintype.card_fin,Nat.cast_add,Nat.cast_one,mul_one] using
    weights_abs_bound (probabilityNodes n) (by norm_num : (0:ℝ) ≤ 1) le_rfl (singleCellBasisBudget_spec n).2
end LogConcaveSampling

end

end

end OAI
