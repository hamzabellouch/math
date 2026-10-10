import OAI.Probability.SLE.Loewner.FutureArcThinCrossing

namespace OAI

/-! A common vanishing bound for the physical images of shrinking
parameter segments. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma shrinking_physical_segment_bound (p : C(unitInterval,ℂ))
    {s : unitInterval} {t r : ℕ → unitInterval}
    (ht : Tendsto t atTop (𝓝 s)) (hr : Tendsto r atTop (𝓝 s))
    (htr : ∀ n, t n≤r n) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n, ∀ v∈Icc (t n) (r n), ‖p v-p s‖≤ε n := by
  have hmax (n : ℕ) : ∃ v∈Icc (t n) (r n),
      ∀ w∈Icc (t n) (r n), ‖p w-p s‖≤‖p v-p s‖ := by
    exact isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (htr n))
      (p.continuous.sub continuous_const).norm.continuousOn
  choose v hv hbound using hmax
  have hvlim : Tendsto v atTop (𝓝 s) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le ht hr (fun n => (hv n).1) (fun n => (hv n).2)
  refine ⟨fun n => ‖p (v n)-p s‖,?_,hbound⟩
  simpa only [sub_self,norm_zero,Function.comp_def] using
    ((p.continuous.tendsto s).comp hvlim).sub_const (p s) |>.norm

end SLEExactGauge

end

end OAI
