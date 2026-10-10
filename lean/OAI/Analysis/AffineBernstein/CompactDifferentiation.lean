import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [IsLocallyFiniteMeasure μ]

/- Differentiation over a fixed compact set from smoothness in a neighbourhood
of the zero-parameter slice. The uniform bound is obtained by compactness. -/
theorem hasDerivAt_setIntegral_compact {K : Set E} (hK : IsCompact K)
    {U : Set (ℝ × E)} (hU : IsOpen U) (h0K : {0} ×ˢ K ⊆ U)
    {F : ℝ × E → ℝ} (hF : ContDiffOn ℝ ∞ F U) :
    HasDerivAt (fun t : ℝ => ∫ x in K, F (t,x) ∂μ)
      (∫ x in K, fderiv ℝ F (0,x) (1,0) ∂μ) 0 := by
  obtain ⟨V,W,hV,hW,h0V,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hU h0K
  have hv : V ∈ nhds (0 : ℝ) := hV.mem_nhds (h0V (by simp))
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hv
  let I : Set ℝ := Icc (-ε / 2) (ε / 2)
  have hIV : I ⊆ V := by
    intro t ht
    apply hεV
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    exact ⟨by dsimp [I] at ht; linarith [ht.1], by dsimp [I] at ht; linarith [ht.2]⟩
  have hIU : I ×ˢ K ⊆ U := fun p hp => hVW ⟨hIV hp.1, hKW hp.2⟩
  have hI0 : (0 : ℝ) ∈ I := by
    change -ε / 2 ≤ 0 ∧ 0 ≤ ε / 2
    constructor <;> linarith
  have hIn : I ∈ nhds (0 : ℝ) := Icc_mem_nhds (by linarith) (by linarith)
  let D : ℝ × E → ℝ := fun p => fderiv ℝ F p (1,0)
  have hDc : ContinuousOn D U := by
    intro p hp
    exact (((hF.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  have hFt (t : ℝ) (ht : t ∈ I) : ContinuousOn (fun x => F (t,x)) K :=
    hF.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => hIU ⟨ht,hx⟩)
  have hDt (t : ℝ) (ht : t ∈ I) : ContinuousOn (fun x => D (t,x)) K :=
    hDc.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => hIU ⟨ht,hx⟩)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hDc.mono hIU)
  have hder (x : E) (hx : x ∈ K) (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (fun r => F (r,x)) (D (t,x)) t := by
    have hh := ((hF.contDiffAt (hU.mem_nhds (hIU ⟨ht,hx⟩))).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    convert! hh using 1
  have hi : IntegrableOn (fun _ : E => C) K μ := continuousOn_const.integrableOn_compact hK
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.restrict K) (F := fun t x => F (t,x)) (F' := fun t x => D (t,x))
    (s := I) (bound := fun _ => C) hIn
    (Filter.eventually_of_mem hIn (fun t ht => ((hFt t ht).integrableOn_compact hK).aestronglyMeasurable))
    ((hFt 0 hI0).integrableOn_compact hK)
    ((hDt 0 hI0).integrableOn_compact hK).aestronglyMeasurable
    (ae_restrict_mem hK.measurableSet |>.mono (fun x hx t ht => hC (t,x) ⟨ht,hx⟩))
    hi (ae_restrict_mem hK.measurableSet |>.mono (fun x hx t ht => hder x hx t ht))).2

end AffineBernstein
end

end OAI
