import OAI.Analysis.CircleDomains.Selection.LocalizedRealStage
import OAI.Analysis.CircleDomains.Transfer.RealMarkedModels
import OAI.Analysis.CircleDomains.Selection.RealSequenceRetention

namespace OAI

/-! Passing localized line payment to the constructed real-model limit. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem localized_line_payment
    (harea : ExteriorCoefficientAreaTheorem) (hε : Tendsto ε atTop (𝓝 0))
    (l : ℕ) {L : ℝ} (hL : 3 * M.radius ≤ L)
    {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ realChartDomain K)
    (W : ℕ → Set ℂ) (hW : ∀ n, MeasurableSet (W n))
    (hWB : ∀ n, W n ⊆ closedBall 0 L)
    (hWsrc : ∀ᶠ n in atTop, W n ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap (M.stages (A.subsequence n)).forward ''
        (realChartDomain (openCompletedRegion (M.stages (A.subsequence n)).terminals.H) \ E)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s < t ∧
      (horizontalLine y s : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      (horizontalLine y t : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      horizontalLine y s ∈ closedBall 0 L ∧ horizontalLine y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (horizontalLine y s)) = 0 ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (horizontalLine y t)) = 1 ∧
      ∀ x ∈ Icc s t, (horizontalLine y x : Sphere) ∈ (M.stages (A.subsequence n)).domain →
        horizontalLine y x ∈ W n) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain G \ E,
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  let E₀ := ∫ x in realChartDomain G \ E,
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x
  let B := Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2)
  have hL0 : 0 ≤ L := (mul_nonneg (by norm_num) M.radius_pos.le).trans hL
  have hbound (n : ℕ) : (M.stages (A.subsequence n)).domainᶜ ⊆
      ((↑) : ℂ → Sphere) '' closedBall 0 L := by
    have h := (normalized_model_uniform_bound harea (M.stages (A.subsequence n)).equivalence
      (M.stages (A.subsequence n)).circle_domain.1 M.radius_pos
      ((M.exterior_core (A.subsequence n)).trans (M.core_model (A.subsequence n)))
      ((M.core_conformal (A.subsequence n)).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans
          (M.exterior_core (A.subsequence n))))
      (M.stages (A.subsequence n)).principal).1
    exact fun p hp => image_mono (closedBall_subset_closedBall hL) (h p hp)
  have hpay : ∀ᶠ n in atTop, (volume J).toReal ≤
      Real.sqrt Real.pi * L * Real.sqrt (E₀ + ε (A.subsequence n)) +
      2 * L * (B + ε (A.subsequence n)) := by
    filter_upwards [A.strict.tendsto_atTop (M.eventually_core_contains hK hKG),
      A.strict.tendsto_atTop (prefixIndex_eq l), hWsrc, hcross] with n hn hl hsrc hcr
    have hec : E ⊆ (M.stages (A.subsequence n)).core := by
      intro x hx
      apply interior_subset ((M.stages (A.subsequence n)).core_contains ?_)
      exact preimage_mono hn (hEK hx)
    have hp := (M.stages (A.subsequence n)).localized_line_payment
      (A.assignment (A.subsequence n)) (prefixIndex l (A.subsequence n)) hL0 (hbound n)
      hE hec (hW n) (hWB n) hsrc hJ hcr
    change (prefixIndex l (A.subsequence n)).val = l at hl
    simpa only [E₀, B, hl] using hp
  have ht₀ : Tendsto (fun n => E₀ + ε (A.subsequence n)) atTop (𝓝 E₀) := by
    simpa only [add_zero, Function.comp_def] using tendsto_const_nhds.add (hε.comp A.strict.tendsto_atTop)
  have hs : Tendsto (fun n => Real.sqrt (E₀ + ε (A.subsequence n))) atTop (𝓝 (Real.sqrt E₀)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp ht₀
  have ht : Tendsto (fun n => Real.sqrt Real.pi * L * Real.sqrt (E₀ + ε (A.subsequence n)) +
      2 * L * (B + ε (A.subsequence n))) atTop
      (𝓝 (Real.sqrt Real.pi * L * Real.sqrt E₀ + 2 * L * B)) := by
    simpa only [add_zero, Function.comp_def] using (hs.const_mul (Real.sqrt Real.pi * L)).add
      ((tendsto_const_nhds.add (hε.comp A.strict.tendsto_atTop)).const_mul (2 * L))
  exact ge_of_tendsto ht hpay

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
