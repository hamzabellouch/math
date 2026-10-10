import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace OAI

/-! # Compact limits of couplings with vanishing dual slack -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y)

omit [MetricSpace X] [BorelSpace X] [BorelSpace Y] in
theorem coupling_snd_support (π : Measure (X × Y)) (hπ : π.map Prod.snd=ν)
    [SecondCountableTopology Y] : ∀ᵐ z ∂π, z.2 ∈ ν.support := by
  apply ae_of_ae_map measurable_snd.aemeasurable
  rw [hπ]
  exact ν.support_mem_ae

theorem compact_coupling_zero_slack [CompactSpace X] [CompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ℕ → ProbabilityMeasure (X × Y))
    (hl : ∀ k, (P k : Measure (X × Y)).map Prod.fst=μ)
    (hr : ∀ k, (P k : Measure (X × Y)).map Prod.snd=ν)
    (s : C(X × Y,ℝ)) (hs : ∀ x y, y ∈ ν.support → s (x,y) ≤ 0)
    (hlim : Tendsto (fun k => ∫ z, s z ∂(P k : Measure (X × Y))) atTop (𝓝 0)) :
    ∃ (Q : ProbabilityMeasure (X × Y)) (ι : ℕ → ℕ), StrictMono ι ∧
      Tendsto (fun k => P (ι k)) atTop (𝓝 Q) ∧
      (Q : Measure (X × Y)).map Prod.fst=μ ∧
      (Q : Measure (X × Y)).map Prod.snd=ν ∧
      ∀ᵐ z ∂(Q : Measure (X × Y)), s z=0 := by
  obtain ⟨Q,_,ι,hι,hQ⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (P k))
  have hleft : (Q : Measure (X × Y)).map Prod.fst=μ := by
    have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k => P (ι k)) Q hQ continuous_fst
    have he (k : ℕ) : (P (ι k)).map Prod.fst = μ.toProbabilityMeasure :=
      Subtype.ext (hl (ι k))
    simp only [he] at hh
    have heq : μ.toProbabilityMeasure = Q.map Prod.fst :=
      tendsto_nhds_unique tendsto_const_nhds hh
    exact (congrArg (fun r : ProbabilityMeasure X => (r : Measure X)) heq).symm
  have hright : (Q : Measure (X × Y)).map Prod.snd=ν := by
    have hh := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k => P (ι k)) Q hQ continuous_snd
    have he (k : ℕ) : (P (ι k)).map Prod.snd = ν.toProbabilityMeasure :=
      Subtype.ext (hr (ι k))
    simp only [he] at hh
    have heq : ν.toProbabilityMeasure = Q.map Prod.snd :=
      tendsto_nhds_unique tendsto_const_nhds hh
    exact (congrArg (fun r : ProbabilityMeasure Y => (r : Measure Y)) heq).symm
  have hint : (∫ z, s z ∂(Q : Measure (X × Y)))=0 :=
    tendsto_nhds_unique ((ProbabilityMeasure.continuous_integral_continuousMap s).tendsto Q |>.comp hQ)
      (hlim.comp hι.tendsto_atTop)
  have hnonpos : ∀ᵐ z ∂(Q : Measure (X × Y)), s z ≤ 0 := by
    filter_upwards [coupling_snd_support (ν := ν) (π := (Q : Measure (X × Y))) hright] with z hz
    exact hs z.1 z.2 hz
  have hi : Integrable (fun z => -s z) (Q : Measure (X × Y)) :=
    s.continuous.neg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (fun z => -s z) =ᵐ[(Q : Measure (X × Y))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (by filter_upwards [hnonpos] with z hz; simpa using hz) hi).mp
      (by rw [integral_neg,hint,neg_zero])
  refine ⟨Q,ι,hι,hQ,hleft,hright,?_⟩
  filter_upwards [he] with z hz
  simpa using hz

end RegularPointCoordinates

end

end OAI
