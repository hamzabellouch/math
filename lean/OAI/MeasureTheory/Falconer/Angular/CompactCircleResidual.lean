import OAI.MeasureTheory.Falconer.Angular.CircleStationaryPartition
import OAI.MeasureTheory.Falconer.Angular.StationaryChartAmplitude

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

 theorem contDiff_interval_zero_extension {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (ha : f =ᶠ[𝓝 a] (fun _ => 0)) (hb : f =ᶠ[𝓝 b] (fun _ => 0)) :
    ContDiff ℝ ∞ ((Ioo a b).indicator f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo a b
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact indicator_of_mem hy f
  · have he : (Ioo a b).indicator f =ᶠ[𝓝 x] (fun _ => 0) := by
      by_cases hc : x ∈ Icc a b
      · have hab : x = a ∨ x = b := by
          simp only [mem_Ioo,not_and_or,not_lt] at hx
          rcases hx with hx | hx
          · exact Or.inl (le_antisymm hx hc.1)
          · exact Or.inr (le_antisymm hc.2 hx)
        have hh : f =ᶠ[𝓝 x] (fun _ => 0) := by rcases hab with rfl | rfl; exact ha; exact hb
        filter_upwards [hh] with y hy
        by_cases hy' : y ∈ Ioo a b <;> simp [hy',hy]
      · filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hc] with y hy
        have hy' : y ∉ Ioo a b := fun hh => hy (Ioo_subset_Icc_self hh)
        exact indicator_of_notMem hy' f
    exact contDiffAt_const.congr_of_eventuallyEq he

noncomputable def compactCircleResidual : ℝ → ℝ :=
  (Ioo (-Real.pi) Real.pi).indicator circleStationaryResidual

 theorem compactCircleResidual_contDiff : ContDiff ℝ ∞ compactCircleResidual := by
  apply contDiff_interval_zero_extension circleStationaryResidual_contDiff
  · apply circleStationaryResidual_eventually_zero
    rw [neg_div,Real.cos_neg,Real.cos_pi_div_two]
  · exact circleStationaryResidual_eventually_zero Real.cos_pi_div_two

 theorem compactCircleResidual_tsupport :
    tsupport compactCircleResidual ⊆ Icc (-Real.pi) Real.pi := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have hx' : x ∉ Ioo (-Real.pi) Real.pi := fun hh => hn (Ioo_subset_Icc_self hh)
  exact hx (indicator_of_notMem hx' _)

 theorem compactCircleResidual_sine_support :
    tsupport compactCircleResidual ⊆ {θ : ℝ | (1:ℝ)/8 ≤ |Real.sin θ|} := by
  apply Subset.trans _ circleStationaryResidual_support
  apply closure_mono
  intro x hx hh
  have he : compactCircleResidual x = 0 := by
    unfold compactCircleResidual
    by_cases hx' : x ∈ Ioo (-Real.pi) Real.pi <;> simp [hx',hh]
  exact hx he

noncomputable def circleResidualAmplitude (f : ℝ → ℂ) (θ : ℝ) : ℂ :=
  (compactCircleResidual θ : ℂ)*f θ

 theorem circleResidualAmplitude_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (circleResidualAmplitude f) :=
  (Complex.ofRealCLM.contDiff.comp compactCircleResidual_contDiff).mul hf

 theorem circleResidualAmplitude_support (f : ℝ → ℂ) :
    tsupport (circleResidualAmplitude f) ⊆ tsupport compactCircleResidual := by
  apply closure_mono
  intro x hx hh
  exact hx (by simp [circleResidualAmplitude,hh])

end PlanarFalconer

end OAI
