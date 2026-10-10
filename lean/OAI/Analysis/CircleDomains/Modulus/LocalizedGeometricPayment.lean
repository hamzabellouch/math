import OAI.Analysis.CircleDomains.Transfer.RetainedRegionAvoidance

namespace OAI

/-! Local line payment off a compact source set whose limiting image misses the crossing region. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem line_payment_away_from_compact
    (harea : ExteriorCoefficientAreaTheorem) (hε : Tendsto ε atTop (𝓝 0))
    (l : ℕ) {L : ℝ} (hL : 3 * M.radius ≤ L)
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hWB : W ⊆ closedBall 0 L)
    (hd : Disjoint (A.function '' K) W)
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
        horizontalLine y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' K),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * L * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  let V (n : ℕ) : Set ℂ :=
    (((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain) ∩ W
  have hEK : Complex.equivRealProdCLM '' K ⊆ realChartDomain (((↑) : ℂ → Sphere) '' K) := by
    rintro x ⟨z, hz, rfl⟩
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z) : ℂ) : Sphere) ∈ ((↑) : ℂ → Sphere) '' K
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact mem_image_of_mem _ hz
  apply A.localized_line_payment harea hε l hL (hK.image OnePoint.continuous_coe)
    (by rintro _ ⟨z, hz, rfl⟩; exact hKG hz)
    (hK.image Complex.equivRealProdCLM.continuous).measurableSet hEK V
    (fun n => (((M.stages (A.subsequence n)).circle_domain.1.preimage
      OnePoint.continuous_coe).measurableSet.inter hW.measurableSet))
    (fun _ => inter_subset_right.trans hWB)
    (A.eventually_region_over_source_complement hK hKG hW hd) hJ
  filter_upwards [hcross] with n hn
  intro y hy
  obtain ⟨s, t, hst, hsD, htD, hsB, htB, hs0, ht1, hsegment⟩ := hn y hy
  refine ⟨s, t, hst, hsD, htD, hsB, htB, hs0, ht1, ?_⟩
  intro x hx hxd
  exact ⟨hxd, hsegment x hx hxd⟩

end CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit

end

end OAI
