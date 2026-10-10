import Mathlib
import OAI.Probability.SKValue.Processes.UnitMomentMartingale

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

lemma UnitMomentMartingale.terminal_condExp
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) : μ[U | ℱ s] =ᵐ[μ] f s := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le _)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hUi
    (fun S _ _ ↦ (h.integrable hs).integrableOn) _ (h.measurable s hs).aestronglyMeasurable
  intro S hS _
  have hlim : Tendsto (fun n ↦ ∫ ω in S, f (terminalTime n) ω ∂μ) atTop (𝓝 (∫ ω in S, U ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ))
      (fun n ↦ ((h.measurable _ (terminalTime_mem n)).mono (ℱ.le _)).aestronglyMeasurable.restrict)
      (integrable_const 1)
      (fun n ↦ Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le
        (h.bounded _ (terminalTime_mem n) ω)))
      (ae_restrict_of_ae (hU.mono (fun _ hω ↦ hω.2)))
  have he : ∀ᶠ n in atTop, (∫ ω in S, f (terminalTime n) ω ∂μ) = ∫ ω in S, f s ω ∂μ := by
    have hsn : ∀ᶠ n in atTop, s ≤ terminalTime n :=
      ((tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1.eventually (Ioi_mem_nhds hs.2)).mono
        (fun _ hn ↦ hn.le)
    filter_upwards [hsn] with n hn
    calc
      _ = ∫ ω in S, μ[f (terminalTime n) | ℱ s] ω ∂μ :=
        (setIntegral_condExp (ℱ.le s) (h.integrable (terminalTime_mem n)) hS).symm
      _ = _ := integral_congr_ae (ae_restrict_of_ae (h.condExp s hs _ (terminalTime_mem n) hn))
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)) hlim

lemma UnitMomentMartingale.terminal_stopped_martingale
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω))) :
    Martingale (fun t : ℝ≥0 ↦ fun ω ↦ if (t : ℝ)<1 then f t ω else U ω)
      (⟨fun t : ℝ≥0 ↦ ℱ t,fun _ _ hij ↦ ℱ.mono hij,fun t ↦ ℱ.le t⟩ :
        Filtration ℝ≥0 m) μ := by
  have hUi : Integrable U μ := Integrable.of_bound (hUm.mono (ℱ.le _)).aestronglyMeasurable 1
    (hU.mono (fun ω hω ↦ (Real.norm_eq_abs _).trans_le hω.1))
  constructor
  · intro t
    by_cases ht : (t : ℝ)<1
    · simpa only [ht,ite_true,ite_false] using h.measurable t ⟨t.coe_nonneg,ht⟩
    · simpa only [ht,ite_true,ite_false] using hUm.mono (ℱ.mono (not_lt.mp ht))
  · intro s t hst
    by_cases hs : (s : ℝ)<1
    · by_cases ht : (t : ℝ)<1
      · simpa only [hs,ht,ite_true,ite_false] using
          h.condExp s ⟨s.coe_nonneg,hs⟩ t ⟨t.coe_nonneg,ht⟩ hst
      · simpa only [hs,ht,ite_true,ite_false] using h.terminal_condExp hUm hU ⟨s.coe_nonneg,hs⟩
    · have ht : ¬(t : ℝ)<1 := not_lt.mpr ((not_lt.mp hs).trans hst)
      have he := condExp_of_stronglyMeasurable (ℱ.le s)
        (hUm.mono (ℱ.mono (not_lt.mp hs))) hUi
      simpa only [hs,ht,ite_true,ite_false] using Filter.EventuallyEq.of_eq he

lemma UnitMomentMartingale.exists_terminal
    (h : UnitMomentMartingale (μ := μ) ℱ f)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Ico (0 : ℝ) 1)) :
    ∃ U : Ω → ℝ, StronglyMeasurable[ℱ 1] U ∧
      Martingale (fun t : ℝ≥0 ↦ fun ω ↦ if (t : ℝ)<1 then f t ω else U ω)
        (⟨fun t : ℝ≥0 ↦ ℱ t,fun _ _ hij ↦ ℱ.mono hij,fun t ↦ ℱ.le t⟩ :
          Filtration ℝ≥0 m) μ ∧
      (∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧ (U ω)^2=1 ∧
        Tendsto (fun t ↦ f t ω) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) ∧
      Tendsto (fun t ↦ ∫ ω, (f t ω-U ω)^2 ∂μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  obtain ⟨U,hUm,hU⟩ := h.exists_continuous_terminal hc
  have hseq : ∀ᵐ ω ∂μ, |U ω|≤1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω)) :=
    hU.mono (fun ω hω ↦ ⟨hω.1,hω.2.comp terminalTime_tendsto⟩)
  refine ⟨U,hUm,h.terminal_stopped_martingale hUm hseq,?_,h.terminal_mean_square hUm hU⟩
  filter_upwards [hU,h.terminal_square hUm hseq] with ω hω hsq
  exact ⟨hω.1,hsq,hω.2⟩

end SKValue

end

end OAI
