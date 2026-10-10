import OAI.Geometry.RCD.Transport.LengthComponentCompression
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! # Bounded-length compression survives weak limits

Open length windows are compatible with Portmanteau. Their countable union
then gives absolute continuity without a global density bound.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem measure_le_of_open_sets {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (ν μ : Measure X) [μ.OuterRegular] (h : ∀ U, IsOpen U → ν U≤μ U) : ν≤μ := by
  intro B
  rw [B.measure_eq_iInf_isOpen μ]
  refine le_iInf (fun U => le_iInf (fun hBU => le_iInf (fun hU => ?_)))
  exact (measure_mono hBU).trans (h U hU)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [SeparableSpace X] in
theorem weak_length_window_compression
    (μ : Measure X) [μ.OuterRegular]
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π)) (t : Time) (D : ℝ)
    {C : ℝ≥0∞} (hC : C≠∞)
    (hb : ∀ j, (((πs j : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<D}).map
      (fun γ => γ t))≤C • μ) :
    (((π : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<D}).map
      (fun γ => γ t))≤C • μ := by
  let : (C • μ).OuterRegular := Measure.OuterRegular.smul μ hC
  apply measure_le_of_open_sets
  intro U hU
  let A := (fun γ : C(Time,X) => γ t) ⁻¹' U ∩ {γ | dist (γ 0) (γ 1)<D}
  have hA : IsOpen A := (hU.preimage (continuous_eval_const t)).inter
    (isOpen_lt ((continuous_eval_const 0).dist (continuous_eval_const 1)) continuous_const)
  have he (ρ : Measure C(Time,X)) :
      ((ρ.restrict {γ | dist (γ 0) (γ 1)<D}).map (fun γ => γ t)) U=ρ A := by
    rw [Measure.map_apply (measurable_path_eval t) hU.measurableSet,
      Measure.restrict_apply ((measurable_path_eval t) hU.measurableSet)]
  calc
    _ = (π : Measure C(Time,X)) A := he _
    _ ≤ liminf (fun j => (πs j : Measure C(Time,X)) A) atTop :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hA
    _ ≤ liminf (fun _ : ℕ => (C • μ) U) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall (fun j => (he _).symm.trans_le (hb j U)))
    _ = _ := by simp

omit [SeparableSpace X] in
theorem absolutelyContinuous_of_length_windows
    (μ : Measure X) (π : Measure C(Time,X)) (t : Time)
    (hb : ∀ j : ℕ, ((π.restrict {γ | dist (γ 0) (γ 1)<(j:ℝ)+1}).map
      (fun γ => γ t)) ≪ μ) : π.map (fun γ => γ t) ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro U hU hμU
  let A := (fun γ : C(Time,X) => γ t) ⁻¹' U
  have he : A=⋃ j : ℕ, A ∩ {γ | dist (γ 0) (γ 1)<(j:ℝ)+1} := by
    ext γ
    simp only [mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    constructor
    · intro hγ
      obtain ⟨j,hj⟩ := exists_nat_gt (dist (γ 0) (γ 1))
      exact ⟨j,hγ,by linarith⟩
    · rintro ⟨j,hγ,_⟩
      exact hγ
  rw [Measure.map_apply (measurable_path_eval t) hU]
  change π A=0
  rw [he]
  apply measure_iUnion_null
  intro j
  have hh := hb j hμU
  rwa [Measure.map_apply (measurable_path_eval t) hU,
    Measure.restrict_apply ((measurable_path_eval t) hU)] at hh

omit [SeparableSpace X] in
theorem weak_length_windows_absolutelyContinuous
    (μ : Measure X) [μ.OuterRegular]
    (πs : ℕ → ProbabilityMeasure C(Time,X)) (π : ProbabilityMeasure C(Time,X))
    (hlim : Tendsto πs atTop (𝓝 π)) (t : Time)
    (C : ℕ → ℝ≥0∞) (hC : ∀ j, C j≠∞)
    (hb : ∀ j k : ℕ, (((πs k : Measure C(Time,X)).restrict {γ | dist (γ 0) (γ 1)<(j:ℝ)+1}).map
      (fun γ => γ t))≤C j • μ) : (π : Measure C(Time,X)).map (fun γ => γ t) ≪ μ := by
  apply absolutelyContinuous_of_length_windows μ _ t
  intro j
  exact Measure.absolutelyContinuous_of_le_smul
    (weak_length_window_compression μ πs π hlim t ((j:ℝ)+1) (hC j) (hb j))

end RegularPointCoordinates

end

end OAI
