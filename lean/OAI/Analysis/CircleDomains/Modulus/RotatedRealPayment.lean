import OAI.Analysis.CircleDomains.Modulus.RotatedLocalizedPayment
import OAI.Analysis.CircleDomains.Modulus.LocalizedGeometricPayment

namespace OAI

/-! Arbitrary-direction localized payment for the actual assigned finite models and their limit. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity
open FiniteTransfer

theorem TerminalComponentAssignment.rotated_line_payment_in_region
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V) (rot : Circle)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsCircleDomain V) (hinf : OnePoint.infty ∈ V)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : Vᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    (w : (ℝ × ℝ) → ℝ) {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O) (hw : ContinuousOn w O)
    (hv : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (((↑) : ℂ → Sphere) ⁻¹' V))
    {W : Set ℂ} (hW : MeasurableSet W) (hWD : W ⊆ ((↑) : ℂ → Sphere) ⁻¹' V) (hWB : W ⊆ closedBall 0 L)
    (henergy : IntegrableOn
      (euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))) W)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ V ∧ (rotatedLine rot y t : Sphere) ∈ V ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction w (fi (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction w (fi (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ V → rotatedLine rot y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      (∫ z in W,
        euclideanGradientEnergy ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) z) +
      2 * L * Real.sqrt (∑ i, Metric.diam (w '' frontier (realJordanInterior (T i))) ^ 2) := by
  obtain ⟨c, r, hr, he, hd, hU⟩ := a.exists_disk_coordinates hV hinf
  let A : I → ℝ := fun i => Metric.diam (w '' frontier (realJordanInterior (T i)))
  have hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall (0 : ℂ) L :=
    fun i => terminal_disk_subset_bound (he i) hbound
  have hcl : ∀ i p q u v, p ∈ closedBall (c i) (r i) → q ∈ closedBall (c i) (r i) →
      MapClusterPt u (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] p)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) →
      MapClusterPt v (𝓝[(⋃ j, closedBall (c j) (r j))ᶜ] q)
        ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere)) → |v - u| ≤ A i := by
    intro i p q u v hp hq hu hv
    apply a.real_planar_cluster_gap_le hf i w hO (hTO i) hw
    · rw [he i]
      exact mem_image_of_mem _ hp
    · rw [he i]
      exact mem_image_of_mem _ hq
    · simpa only [hU] using hu
    · simpa only [hU] using hv
  have hv' : ContDiffOn ℝ 1 ((sphereRealFunction w ∘ fi) ∘ ((↑) : ℂ → Sphere))
      (⋃ j, closedBall (c j) (r j))ᶜ := by simpa only [hU] using hv
  apply CircleDomainRigidity.rotated_line_payment_in_region rot c r A hr
    (fun _ => Metric.diam_nonneg) hL hd hsub hv' hW (by simpa only [hU] using hWD) hWB henergy hcl hJ
  intro y hy
  obtain ⟨s, t, hst, hsV, htV, hsB, htB, hs0, ht1, hsegment⟩ := hcross y hy
  refine ⟨s, t, hst, ?_, ?_, hsB, htB, hs0, ht1, ?_⟩
  · rw [← hU]
    exact hsV
  · rw [← hU]
    exact htV
  · intro x hx hxd
    apply hsegment x hx
    change rotatedLine rot y x ∈ ((↑) : ℂ → Sphere) ⁻¹' V
    rwa [hU]

end CircleDomainRigidity

namespace CircleDomainRigidity.FiniteTransfer.RealTransferStage


variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}
  (M : RealTransferStage G π σ u a b Flag O K₀ ε)

theorem rotated_localized_line_payment
    (T : TerminalComponentAssignment M.terminals.H M.forward M.domain)
    (rot : Circle) (l : Fin n) {L : ℝ} (hL : 0 ≤ L)
    (hbound : M.domainᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) L)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEc : E ⊆ M.core)
    {W : Set ℂ} (hW : MeasurableSet W) (hWD : W ⊆ ((↑) : ℂ → Sphere) ⁻¹' M.domain) (hWB : W ⊆ closedBall 0 L)
    (hWsrc : W ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap M.forward '' (realChartDomain (openCompletedRegion M.terminals.H) \ E)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ M.domain ∧ (rotatedLine rot y t : Sphere) ∈ M.domain ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction (M.functions l) (M.inverse (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction (M.functions l) (M.inverse (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ M.domain → rotatedLine rot y x ∈ W) :
    (volume J).toReal ≤ Real.sqrt Real.pi * L * Real.sqrt
      ((∫ x in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε) +
      2 * L * (Real.sqrt (∑' s, (b l s - a l s) ^ 2) + ε) := by
  let _ : Fintype M.indices := M.finite_indices.fintype
  obtain ⟨hv, _, _⟩ := transported_real_energy M.equivalence
    (isOpen_openCompletedRegion M.terminals.H) M.circle_domain.1 M.source_infty M.principal.1
    (M.functions l) (M.functions_smooth_source l) M.metric_conformal
    (fun x _ => M.metric_pos x) (M.functions_integrable_source l)
  obtain ⟨hi, henergy⟩ := M.transported_energy_away_lt l hE hEc hWsrc
  have hp := T.rotated_line_payment_in_region rot M.equivalence M.circle_domain
    (M.equivalence.infty_mem_target M.source_infty M.principal.1) hL hbound
    (M.functions l) M.extension_open M.terminal_frontier_extension
    (M.functions_smooth l).continuousOn hv hW hWD hWB hi hJ hcross
  have hosc : Real.sqrt (∑ i : M.indices,
      diam (M.functions l '' frontier (realJordanInterior (M.terminals.H i))) ^ 2) ≤
      Real.sqrt (∑' s, (b l s - a l s) ^ 2) + ε := by
    simpa only [terminalOscillation, tsum_fintype] using (M.oscillation l).le
  exact hp.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt henergy.le)
      (mul_nonneg (Real.sqrt_nonneg _) hL))
    (mul_le_mul_of_nonneg_left hosc (mul_nonneg (by norm_num) hL)))

end CircleDomainRigidity.FiniteTransfer.RealTransferStage

namespace CircleDomainRigidity.FiniteTransfer.AssignedRealModelLimit


variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} (A : AssignedRealModelLimit M)

theorem rotated_localized_line_payment
    (harea : ExteriorCoefficientAreaTheorem) (hε : Tendsto ε atTop (𝓝 0))
    (rot : Circle) (l : ℕ) {L : ℝ} (hL : 3 * M.radius ≤ L)
    {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ realChartDomain K)
    (W : ℕ → Set ℂ) (hW : ∀ n, MeasurableSet (W n))
    (hWD : ∀ n, W n ⊆ ((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain)
    (hWB : ∀ n, W n ⊆ closedBall 0 L)
    (hWsrc : ∀ᶠ n in atTop, W n ⊆ Complex.equivRealProdCLM ⁻¹'
      (sphereRealMap (M.stages (A.subsequence n)).forward ''
        (realChartDomain (openCompletedRegion (M.stages (A.subsequence n)).terminals.H) \ E)))
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      (rotatedLine rot y t : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ (M.stages (A.subsequence n)).domain →
        rotatedLine rot y x ∈ W n) :
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
    have hp := (M.stages (A.subsequence n)).rotated_localized_line_payment
      (A.assignment (A.subsequence n)) rot (prefixIndex l (A.subsequence n)) hL0 (hbound n)
      hE hec (hW n) (hWD n) (hWB n) hsrc hJ hcr
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

theorem rotated_line_payment_away_from_compact
    (harea : ExteriorCoefficientAreaTheorem) (hε : Tendsto ε atTop (𝓝 0))
    (rot : Circle) (l : ℕ) {L : ℝ} (hL : 3 * M.radius ≤ L)
    {K W : Set ℂ} (hK : IsCompact K) (hKG : K ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hW : IsClosed W) (hWB : W ⊆ closedBall 0 L)
    (hd : Disjoint (A.function '' K) W)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J, ∃ s t : ℝ, s ≠ t ∧
      (rotatedLine rot y s : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      (rotatedLine rot y t : Sphere) ∈ (M.stages (A.subsequence n)).domain ∧
      rotatedLine rot y s ∈ closedBall 0 L ∧ rotatedLine rot y t ∈ closedBall 0 L ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y s)) = 0 ∧
      sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
        ((M.stages (A.subsequence n)).inverse (rotatedLine rot y t)) = 1 ∧
      ∀ x ∈ uIcc s t, (rotatedLine rot y x : Sphere) ∈ (M.stages (A.subsequence n)).domain →
        rotatedLine rot y x ∈ W) :
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
  apply A.rotated_localized_line_payment harea hε rot l hL (hK.image OnePoint.continuous_coe)
    (by rintro _ ⟨z, hz, rfl⟩; exact hKG hz)
    (hK.image Complex.equivRealProdCLM.continuous).measurableSet hEK V
    (fun n => (((M.stages (A.subsequence n)).circle_domain.1.preimage
      OnePoint.continuous_coe).measurableSet.inter hW.measurableSet))
    (fun _ => inter_subset_left)
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
