import OAI.Probability.FirstPassage.GridConnectionGeometry

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def gridBinGood (b m K : ℝ) (X h w l : ℤ) (j : ℕ) : Set (Edge → ℝ) :=
  {weights | (∃ t : Fin (j^2), weights ∈ crossingEvent b m K w l (gridTrialTranslate b X h w t)) ∧
    (∑ e ∈ transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w),weights e)
      ≤ 100*(j : ℝ)^2*w ∧
    (∑ e ∈ transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w),weights e)
      ≤ 100*(j : ℝ)^2*w}

lemma measurableSet_gridBinGood (b m K : ℝ) (X h w l : ℤ) (j : ℕ) :
    MeasurableSet (gridBinGood b m K X h w l j) := by
  have ht : MeasurableSet {weights : Edge → ℝ | ∃ t : Fin (j^2),
      weights ∈ crossingEvent b m K w l (gridTrialTranslate b X h w t)} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun _ => measurableSet_crossingEvent ..)
  have hv (Y : ℤ) : MeasurableSet {weights : Edge → ℝ |
      (∑ e ∈ transverseIntervalEdges b Y (gridIntervalLower h w) (gridIntervalUpper j h w),weights e)
        ≤ 100*(j : ℝ)^2*w} :=
    measurableSet_le (Finset.measurable_sum _ (fun e _ => measurable_pi_apply e)) measurable_const
  exact ht.inter ((hv X).inter (hv (X+l)))

lemma gridBinGood_connection (weights : Edge → ℝ) (hweights : ∀ e, 0 ≤ weights e)
    (b m K : ℝ) (hK : 0 ≤ K) (X h w l : ℤ) (hl : 0 ≤ l) (j : ℕ)
    (hj : 1 ≤ j) (hw : 1 ≤ w) (hgood : weights ∈ gridBinGood b m K X h w l j)
    (r₀ : ℝ) (hbin : (h : ℝ)*w ≤ r₀ ∧ r₀ ≤ ((h : ℝ)+1)*w)
    (p q : Vertex) (hp : p.1=X ∧ |transverse b p-r₀| ≤ 1)
    (hq : q.1=X+l ∧ |transverse b q-r₀| ≤ 1) :
    ∃ ds, p+displacement ds=q ∧ pathCost weights p ds ≤ m*l+(K+200)*(j : ℝ)^2*w ∧
      PathIn p ds {z | X-l ≤ z.1 ∧ z.1 ≤ X+2*l ∧
        |transverse b z-r₀| ≤ (K+200)*(j : ℝ)^2*w} :=
  grid_bin_connection weights hweights b m K hK X h w l hl j hj hw
    hgood.1 hgood.2.1 hgood.2.2 r₀ hbin p q hp hq

noncomputable def gridVerticalExponent : ℝ := 50*(1-Real.log 2)

lemma gridVerticalExponent_pos : 0 < gridVerticalExponent := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h
    exact h
  unfold gridVerticalExponent
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gridBinGood_failure_bound (henv : ExponentialEnvironment P τ)
    (b m K q₀ : ℝ) (X h w l : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w)
    (hq : q₀ ≤ P.real {ω | (fun e => τ e ω) ∈ crossingEvent b m K w l 0}) :
    P.real {ω | (fun e => τ e ω) ∉ gridBinGood b m K X h w l j} ≤
      (1-q₀)^(j^2)+2*Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) := by
  let _ := henv.probability
  let F := {ω | ∀ t : Fin (j^2), (fun e => τ e ω) ∉ crossingEvent b m K w l (gridTrialTranslate b X h w t)}
  let V₁ := {ω | 100*(j : ℝ)^2*w < ∑ e ∈ transverseIntervalEdges b X
    (gridIntervalLower h w) (gridIntervalUpper j h w),τ e ω}
  let V₂ := {ω | 100*(j : ℝ)^2*w < ∑ e ∈ transverseIntervalEdges b (X+l)
    (gridIntervalLower h w) (gridIntervalUpper j h w),τ e ω}
  have hsub : {ω | (fun e => τ e ω) ∉ gridBinGood b m K X h w l j} ⊆ F ∪ V₁ ∪ V₂ := by
    intro ω hω
    simp only [gridBinGood,Set.mem_ofPred_eq,not_and_or,not_exists,not_le] at hω
    rcases hω with hf | hv | hv
    · exact Or.inl (Or.inl hf)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hf := gridTrials_failure_bound henv b m K q₀ X h w l hw j hq
  have hv₁ := grid_vertical_cost_tail henv X ⌈gridIntervalLower h w+b*X⌉
    ⌊gridIntervalUpper j h w+b*X⌋ ((j : ℝ)^2*w) (by
      simpa only [transverseIntervalEdges,mul_assoc] using grid_interval_card b X h w j hj hw)
  have hv₂ := grid_vertical_cost_tail henv (X+l) ⌈gridIntervalLower h w+b*(X+l)⌉
    ⌊gridIntervalUpper j h w+b*(X+l)⌋ ((j : ℝ)^2*w) (by
      simpa only [transverseIntervalEdges,mul_assoc,Int.cast_add] using grid_interval_card b (X+l) h w j hj hw)
  have hv₁' : P.real V₁ ≤ Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) := by
    simpa only [V₁,transverseIntervalEdges,gridVerticalExponent,mul_assoc] using hv₁
  have hv₂' : P.real V₂ ≤ Real.exp (-gridVerticalExponent*(j : ℝ)^2*w) := by
    simpa only [V₂,transverseIntervalEdges,gridVerticalExponent,mul_assoc,Int.cast_add] using hv₂
  have hh := (measureReal_mono (μ := P) hsub).trans
    ((measureReal_union_le (μ := P) (F ∪ V₁) V₂).trans
      (add_le_add (measureReal_union_le (μ := P) F V₁) le_rfl))
  change P.real F ≤ _ at hf
  linarith

end PlanarFPP

end OAI
