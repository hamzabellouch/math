import OAI.Geometry.Perimeter.Regularity.HasC1TraceAt

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem regular_supersolution_c1_test {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) (hZ : IsClosed Z)
    (hfinite : ∀ R : ℝ, 0 < R → surfaceMeasure S (Metric.ball 0 R) < ⊤)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
      AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
    {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hφZ : Disjoint (tsupport φ) Z) (hpφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S := by
  obtain ⟨r, hr, hKZ⟩ := hc.exists_cthickening_subset_open hZ.isOpen_compl
    (Set.disjoint_left.mp hφZ)
  let K := Metric.cthickening r (tsupport φ)
  have hKc : IsCompact K := hc.cthickening
  have hφK : tsupport φ ⊆ K := Metric.self_subset_cthickening (tsupport φ)
  have hKd : Disjoint K Z := Set.disjoint_left.mpr hKZ
  obtain ⟨F, hF, he⟩ := c1_exists_smooth_representative_near_regular_test hS hZ htrace
    hKc.isClosed hKd
  have hFK : D =ᵐ[(surfaceMeasure S).restrict K] surfaceGradient S F := by
    filter_upwards [ae_restrict_mem hKc.measurableSet,
      ae_restrict_of_ae (ae_restrict_mem hS.measurableSet)] with x hx hxS
    exact (he x ⟨hxS, hx⟩).2.symm
  have hDm : AEStronglyMeasurable D ((surfaceMeasure S).restrict K) :=
    ((hgrad F hF).mono_measure Measure.restrict_le_self).congr hFK.symm
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hKc.isBounded
  have hKfin : surfaceMeasure S K < ⊤ :=
    (measure_mono (hR.trans (Metric.ball_subset_ball (le_max_left R 1)))).trans_lt
      (hfinite (max R 1) (zero_lt_one.trans_le (le_max_right R 1)))
  let : IsFiniteMeasure ((surfaceMeasure S).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hKfin⟩
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    (hF.continuous_fderiv (by norm_num)).continuousOn
  have hDb : ∀ᵐ x ∂(surfaceMeasure S).restrict K, ‖D x‖ ≤ B := by
    filter_upwards [ae_restrict_mem hKc.measurableSet, hFK] with x hx hFx
    rw [hFx]
    exact (surfaceGradient_norm_le_fderiv S F x).trans (hB x hx)
  obtain ⟨M, hM, hb, _⟩ := c1Mollify_pair_bounded S hφ hc
  have ht := tendsto_integral_of_dominated_convergence (μ := (surfaceMeasure S).restrict K)
    (fun _ ↦ B * M)
    (F := fun j x ↦ inner ℝ (D x) (surfaceGradient S (c1Mollify φ j) x))
    (f := fun x ↦ inner ℝ (D x) (surfaceGradient S φ x))
    (fun j ↦ hDm.inner ((hgrad _ ((c1Mollify_contDiff hφ.continuous j).of_le (by norm_num))).mono_measure
      Measure.restrict_le_self)) (integrable_const _) ?_ ?_
  · have hsupp : ∀ᶠ j in atTop, tsupport (c1Mollify φ j) ⊆ K := by
      filter_upwards [c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hr)] with j hj
      exact (c1Mollify_tsupport_subset φ j).trans (Metric.cthickening_mono hj.le _)
    have hn : ∀ᶠ j in atTop, 0 ≤ ∫ x in K,
        inner ℝ (D x) (surfaceGradient S (c1Mollify φ j) x) ∂surfaceMeasure S := by
      filter_upwards [hsupp] with j hj
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        rw [surfaceGradient_eq_zero_of_notMem_tsupport S (fun h ↦ hx (hj h)), inner_zero_right])]
      exact hsup _ (c1Mollify_contDiff hφ.continuous j) (c1Mollify_hasCompactSupport hc j)
        (hKd.mono_left hj) (c1Mollify_nonneg hpφ j)
    have hle := ge_of_tendsto ht hn
    rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      rw [surfaceGradient_eq_zero_of_notMem_tsupport S (fun h ↦ hx (hφK h)), inner_zero_right])] at hle
  · intro j
    filter_upwards [hDb] with x hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul hx (hb j x).2
      (norm_nonneg _) (by linarith [norm_nonneg (D x)]))
  · exact ae_of_all _ fun x ↦ tendsto_const_nhds.inner
      (c1Mollify_surfaceGradient_tendsto S hφ hc x)

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem c1_hausdorff_trace_mem_sobolevGraph {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (V : Set (Space n))
    (hV : Bornology.IsBounded V) (hVm : MeasurableSet V)
    [IsFiniteMeasure ((surfaceMeasure S).restrict V)]
    (hZc : IsCompact Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasC1TraceJetAt S h G x)
    (hh : MemLp h 2 ((surfaceMeasure S).restrict V))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict V))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(surfaceMeasure S).restrict V, ‖h x‖ ≤ M)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) ((surfaceMeasure S).restrict V))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z, ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict V (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V) := by
  obtain ⟨χ, hχ, hχlim, hχE⟩ := exists_memLp_capacity_sequence hn S V Z hZc hZd
    hgrad hA hr₀ hgrowth
  exact c1_capacity_trace_mem_sobolevGraph hS V hV hVm hgrad hreg hh hG hM hbound χ
    (fun i ↦ (hχ i).1) (fun i ↦ (hχ i).2.2.1)
    (fun i ↦ ae_of_all _ (hχ i).2.1) hχlim (fun i ↦ (hχ i).2.2.2) hχE

theorem HasC1TraceJetAt.mul_smooth {n : ℕ} {S : Set (Space n)}
    {h : Space n → ℝ} {G : Space n → Space n} {x : Space n}
    (hxS : x ∈ S) (hx : HasC1TraceJetAt S h G x)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    HasC1TraceJetAt S (fun y ↦ ψ y * h y)
      (fun y ↦ ψ y • G y + h y • surfaceGradient S ψ y) x := by
  obtain ⟨U, hU, hxU, f, hf, he, hG⟩ := hx
  refine ⟨U, hU, hxU, fun y ↦ ψ y * f y, (hψ.of_le (by norm_num)).contDiffOn.mul hf, ?_, ?_⟩
  · intro y hy
    exact congrArg (fun a ↦ ψ y * a) (he hy)
  · rw [surfaceGradient_mul (hψ.differentiable (by simp) x)
        ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)),
        hG, he ⟨hxS, hxU⟩]

theorem c1_regular_trace_jet_mul_spatial {n : ℕ} {S Z : Set (Space n)}
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasC1TraceJetAt S h G x)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ∀ x ∈ S \ (Z ∩ tsupport ψ), HasC1TraceJetAt S (fun y ↦ ψ y * h y)
      (fun y ↦ ψ y • G y + h y • surfaceGradient S ψ y) x := by
  intro x hx
  by_cases hxZ : x ∈ Z
  · have hxs : x ∉ tsupport ψ := fun hxψ ↦ hx.2 ⟨hxZ, hxψ⟩
    have hloc : ψ =ᶠ[𝓝 x] (0 : Space n → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hxs
    obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hloc
    have hψgrad : gradient ψ x = 0 := by
      simpa only [Pi.zero_def, gradient_fun_const] using hloc.gradient_eq
    have hψx : ψ x = 0 := hloc.self_of_nhds
    refine ⟨U, hU, hxU, fun _ ↦ 0, contDiffOn_const, ?_, ?_⟩
    · intro y hy
      have hy0 : ψ y = 0 := hUsub hy.2
      simp only [hy0, zero_mul]
    · simp only [hψx, surfaceGradient, hψgrad, gradient_fun_const,
        map_zero, Submodule.coe_zero, zero_smul, smul_zero, add_zero]
  · exact (hreg x ⟨hx.1, hxZ⟩).mul_smooth hx.1 hψ

theorem c1_hausdorff_trace_mem_sobolevGraph_ball {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (hZ : IsClosed Z)
    (hZd : dimH Z ≤ (n - 8 : ℕ)) {R : ℝ} (hR : 0 < R)
    [IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R))]
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasC1TraceJetAt S h G x)
    (hh : MemLp h 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(surfaceMeasure S).restrict (Metric.ball 0 R), ‖h x‖ ≤ M)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f)
        ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z ∩ Metric.closedBall 0 (R + 2), ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S (Metric.ball 0 R)) := by
  let b : ContDiffBump (0 : Space n) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let K : Set (Space n) := Z ∩ tsupport b
  have hKc : IsCompact K := b.hasCompactSupport.of_isClosed_subset
    (hZ.inter (isClosed_tsupport b)) inter_subset_right
  have hKd : dimH K ≤ (n - 8 : ℕ) :=
    (dimH_mono (show K ⊆ Z from inter_subset_left)).trans hZd
  have hb : ∀ x ∈ Metric.ball (0 : Space n) R, b =ᶠ[𝓝 x] 1 := by
    intro x hx
    apply b.eventuallyEq_one_of_mem_ball
    exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hx).trans (by dsimp [b]; linarith))
  have hbG : ∀ x ∈ Metric.ball (0 : Space n) R, surfaceGradient S b x = 0 := by
    intro x hx
    have hgr : gradient b x = 0 := by
      simpa only [Pi.one_def, gradient_fun_const] using (hb x hx).gradient_eq
    simp only [surfaceGradient, hgr, map_zero, Submodule.coe_zero]
  let h' := fun x ↦ b x * h x
  let G' := fun x ↦ b x • G x + h x • surfaceGradient S b x
  have he : h' =ᵐ[(surfaceMeasure S).restrict (Metric.ball 0 R)] h := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp [h']
    rw [(hb x hx).self_of_nhds]
    simp
  have hDe : G' =ᵐ[(surfaceMeasure S).restrict (Metric.ball 0 R)] G := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp [G']
    rw [(hb x hx).self_of_nhds, hbG x hx]
    simp
  let hh' := hh.ae_eq he.symm
  let hG' := hG.ae_eq hDe.symm
  have hbound' : ∀ᵐ x ∂(surfaceMeasure S).restrict (Metric.ball 0 R), ‖h' x‖ ≤ M := by
    filter_upwards [he, hbound] with x hx hbx
    simpa only [hx] using hbx
  have hmem := c1_hausdorff_trace_mem_sobolevGraph hn hS (Metric.ball 0 R)
    Metric.isBounded_ball measurableSet_ball hKc hKd
    (c1_regular_trace_jet_mul_spatial hreg b.contDiff) hh' hG' hM
    hbound' hgrad hA hr₀ (fun c hc r hr hrr ↦ hgrowth c
      ⟨hc.1, by simpa only [b.tsupport_eq] using hc.2⟩ r hr hrr)
  have heLp : hh'.toLp h' = hh.toLp h := hh'.toLp_congr hh he
  have hDeLp : hG'.toLp G' = hG.toLp G := hG'.toLp_congr hG hDe
  change (hh'.toLp h', hG'.toLp G') ∈ _ at hmem
  simpa only [heLp, hDeLp] using hmem

theorem c1_trace_aestronglyMeasurable_of_singular_dim {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : MeasurableSet S) (hZ : MeasurableSet Z)
    (hdim : dimH Z ≤ (n - 8 : ℕ)) {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasC1TraceJetAt S h G x) :
    AEStronglyMeasurable h (surfaceMeasure S) := by
  have hc : ContinuousOn h (S \ Z) := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, he, _⟩ := hreg x hx
    have hf' : ContinuousWithinAt f (S \ Z) x :=
      (hf.contDiffAt (hU.mem_nhds hxU)).continuousAt.continuousWithinAt
    apply hf'.congr_of_eventuallyEq _ (he ⟨hx.1, hxU⟩).symm
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
    exact (he ⟨hy.1, hyU⟩).symm
  have hs : ∀ᵐ x ∂surfaceMeasure S, x ∈ S := ae_restrict_mem hS
  have hz : ∀ᵐ x ∂surfaceMeasure S, x ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      surfaceMeasure_zero_of_singular_dim hn S Z hdim
  have hregular : ∀ᵐ x ∂surfaceMeasure S, x ∈ S \ Z := by
    filter_upwards [hs, hz] with x hx hzx
    exact ⟨hx, hzx⟩
  have hmeas := hc.aestronglyMeasurable (μ := surfaceMeasure S) (hS.diff hZ)
  rwa [Measure.restrict_eq_self_of_ae_mem hregular] at hmeas

theorem c1_min_one_mem_sobolevGraph_ball {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (hZ : IsClosed Z)
    (hZd : dimH Z ≤ (n - 8 : ℕ)) {R : ℝ} (hR : 0 < R)
    [IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R))]
    {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    (hW0 : ∀ᵐ x ∂(surfaceMeasure S).restrict (Metric.ball 0 R), 0 ≤ W x)
    (hG : MemLp (truncatedGradient W D) 2
      ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f)
        ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z ∩ Metric.closedBall 0 (R + 2), ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    ∃ hh : MemLp (fun x ↦ min (W x) 1) 2
        ((surfaceMeasure S).restrict (Metric.ball 0 R)),
      (hh.toLp (fun x ↦ min (W x) 1), hG.toLp (truncatedGradient W D)) ∈
        closure (smoothGradientGraph S (Metric.ball 0 R)) := by
  have hW : AEStronglyMeasurable W ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    (c1_trace_aestronglyMeasurable_of_singular_dim hn hS.measurableSet
    hZ.measurableSet hZd htrace).mono_measure (Measure.restrict_le_self)
  obtain ⟨hh, hf, hF, hlim⟩ := smoothTruncation_pair_tendsto hW hW0 hG
  refine ⟨hh, isClosed_closure.mem_of_tendsto hlim (Filter.Eventually.of_forall ?_)⟩
  intro j
  apply c1_hausdorff_trace_mem_sobolevGraph_ball hn hS hZ hZd hR
    (fun x hx ↦ (htrace x hx).smoothTruncation hx.1 (truncationParameter_pos j))
    (hf j) (hF j) (M := 1) zero_le_one _ hgrad hA hr₀ hgrowth
  filter_upwards [hW0] with x hx
  exact smoothTruncation_norm_le (truncationParameter_pos j) hx

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
section C1RegularTests
variable {n : ℕ} {S Z : Set (Space n)}
variable (hS : IsClosed S) (hZ : IsClosed Z)
variable (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
include hS hZ hfinite hgrad

theorem c1_smoothTruncation_regular_test {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
    {ε : ℝ} (hε : 0 < ε) {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hφZ : Disjoint (tsupport φ) Z) (hpφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, inner ℝ (truncationSlope ε (W x) • D x)
      (surfaceGradient S φ x) ∂surfaceMeasure S := by
  obtain ⟨F, hF, he⟩ := c1_exists_smooth_representative_near_regular_test hS hZ htrace
    (isClosed_tsupport φ) hφZ
  let ψ : Space n → ℝ := fun x ↦ φ x * truncationSlope ε (F x)
  have hψ : ContDiff ℝ 1 ψ := hφ.mul (((truncationSlope_contDiff ε).of_le (by norm_num)).comp hF)
  have hcψ : HasCompactSupport ψ := hcφ.mul_right
  have hψZ : Disjoint (tsupport ψ) Z := hφZ.mono_left tsupport_mul_subset_left
  have htt : ∀ x ∈ S \ Z, HasC1TraceJetAt S (smoothTruncation ε ∘ W)
      (fun y ↦ truncationSlope ε (W y) • D y) x := by
    intro x hx
    simpa only [smoothTruncation_deriv] using
      (htrace x hx).comp hx.1 ((smoothTruncation_contDiff ε).of_le (by norm_num))
  have hi := c1_integrable_regular_test_pair hS hZ hfinite hgrad htrace hψ hcψ hψZ
  have hj := c1_integrable_regular_test_pair hS hZ hfinite hgrad htt hφ hcφ hφZ
  apply (regular_supersolution_c1_test hS hZ hfinite hgrad htrace hsup hψ hcψ hψZ (fun x ↦ mul_nonneg (hpφ x)
    (truncationSlope_mem_Icc ε (F x)).1)).trans
  apply integral_mono_ae hi hj
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  by_cases hxt : x ∈ tsupport φ
  · have hFx := he x ⟨hx, hxt⟩
    have hDp : deriv (truncationSlope ε) (W x) ≤ 0 :=
      (truncationSlope_antitone hε).deriv_nonpos
    have heq : surfaceGradient S ψ x =
        φ x • (deriv (truncationSlope ε) (W x) • D x) +
          truncationSlope ε (W x) • surfaceGradient S φ x := by
      dsimp only [ψ]
      rw [surfaceGradient_mul (S := S) (g := fun y ↦ truncationSlope ε (F y)) (hφ.differentiable (by simp) x)
        ((((truncationSlope_contDiff ε).of_le (by norm_num)).comp hF).differentiable (by simp) x)]
      rw [show (fun y ↦ truncationSlope ε (F y)) = truncationSlope ε ∘ F from rfl,
        surfaceGradient_comp (hF.differentiable (by simp) x)
          ((truncationSlope_contDiff ε).differentiable (by simp) (F x)), hFx.1, hFx.2]
    rw [heq, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hneg : φ x * (deriv (truncationSlope ε) (W x) * ‖D x‖ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hpφ x) (mul_nonpos_of_nonpos_of_nonneg hDp (sq_nonneg _))
    linarith
  · have hxψ : x ∉ tsupport ψ := fun h ↦ hxt (tsupport_mul_subset_left h)
    simp only [surfaceGradient_eq_zero_of_notMem_tsupport S hxt,
      surfaceGradient_eq_zero_of_notMem_tsupport S hxψ, inner_zero_right, le_refl]

end C1RegularTests
end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
section RegularEnergy
variable {n : ℕ} {S Z : Set (Space n)}
variable (hS : IsClosed S) (hZ : IsClosed Z)
variable (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
include hS hZ hfinite hgrad

theorem c1_regular_gradient_memLp_test {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    {η : Space n → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηZ : Disjoint (tsupport η) Z) :
    MemLp (fun x ↦ η x • D x) 2 (surfaceMeasure S) := by
  have hi := c1_regular_gradient_memLp_indicator_test hS hZ hfinite hgrad htrace hcη hηZ
  obtain ⟨M, hM⟩ := hcη.exists_bound_of_continuous hη.continuous
  have hh : MemLp (fun x ↦ η x • (tsupport η).indicator D x) 2 (surfaceMeasure S) := by
    apply hi.of_le_mul (c := M)
      (hη.continuous.aestronglyMeasurable.smul hi.aestronglyMeasurable)
    apply ae_of_all
    intro x
    change ‖η x • (tsupport η).indicator D x‖ ≤ M * ‖(tsupport η).indicator D x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
  apply hh.ae_eq
  apply ae_of_all
  intro x
  by_cases hx : x ∈ tsupport η
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_smul]

theorem c1_smoothTruncation_regular_energy {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    (hW0 : ∀ x ∈ S \ Z, 0 ≤ W x)
    (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
    {ε : ℝ} (hε : 0 < ε) {η : Space n → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηZ : Disjoint (tsupport η) Z) :
    (∫ x, ‖η x • (truncationSlope ε (W x) • D x)‖ ^ 2 ∂surfaceMeasure S) ≤
      4 * ∫ x, ‖surfaceGradient S η x‖ ^ 2 ∂surfaceMeasure S := by
  let T := smoothTruncation ε
  let G : Space n → Space n := fun x ↦ truncationSlope ε (W x) • D x
  have htt : ∀ x ∈ S \ Z, HasC1TraceJetAt S (T ∘ W) G x := by
    intro x hx
    simpa only [T, G, smoothTruncation_deriv] using
      (htrace x hx).comp hx.1 ((smoothTruncation_contDiff ε).of_le (by norm_num))
  obtain ⟨F, hF, he⟩ := c1_exists_smooth_representative_near_regular_test hS hZ htrace
    (isClosed_tsupport η) hηZ
  let ψ : Space n → ℝ := fun x ↦ (η x * η x) * (1 - T (F x))
  have hTF : ContDiff ℝ 1 (T ∘ F) := ((smoothTruncation_contDiff ε).of_le (by norm_num)).comp hF
  have hψ : ContDiff ℝ 1 ψ := (hη.mul hη).mul (contDiff_const.sub hTF)
  have hcψ : HasCompactSupport ψ := hcη.mul_right.mul_right
  have hsub : tsupport ψ ⊆ tsupport η := tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hψZ : Disjoint (tsupport ψ) Z := hηZ.mono_left hsub
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x ↦ mul_nonneg (mul_self_nonneg (η x))
    (sub_nonneg.mpr (smoothTruncation_le_one_all hε (F x)))
  have ht : 0 ≤ ∫ x, inner ℝ (G x) (surfaceGradient S ψ x) ∂surfaceMeasure S :=
    c1_smoothTruncation_regular_test hS hZ hfinite hgrad htrace hsup hε hψ hcψ hψZ hψ0
  let A : Space n → Space n := fun x ↦ η x • G x
  let B : Space n → Space n := surfaceGradient S η
  have hA : MemLp A 2 (surfaceMeasure S) :=
    c1_regular_gradient_memLp_test hS hZ hfinite hgrad htt hη hcη hηZ
  have hB : MemLp B 2 (surfaceMeasure S) :=
    c1_surfaceGradient_memLp_of_compact hfinite hgrad hη hcη
  have hi := c1_integrable_regular_test_pair hS hZ hfinite hgrad htt hψ hcψ hψZ
  have hAs := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
  have hBs := (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB
  have hu : Integrable (fun x ↦ 2 * ‖B x‖ ^ 2 - (1 / 2 : ℝ) * ‖A x‖ ^ 2) (surfaceMeasure S) :=
    (hBs.const_mul 2).sub (hAs.const_mul (1 / 2))
  have hle : (∫ x, inner ℝ (G x) (surfaceGradient S ψ x) ∂surfaceMeasure S) ≤
      ∫ x, 2 * ‖B x‖ ^ 2 - (1 / 2 : ℝ) * ‖A x‖ ^ 2 ∂surfaceMeasure S := by
    apply integral_mono_ae hi hu
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    by_cases hxt : x ∈ tsupport η
    · have hxr : x ∈ S \ Z := ⟨hx, fun hz ↦ Set.disjoint_left.mp hηZ hxt hz⟩
      have hFx := he x ⟨hx, hxt⟩
      have hgT : surfaceGradient S (fun y ↦ T (F y)) x = G x := by
        change surfaceGradient S (T ∘ F) x = G x
        rw [surfaceGradient_comp (hF.differentiable (by simp) x)
          ((smoothTruncation_contDiff ε).differentiable (by simp) (F x))]
        simp only [smoothTruncation_deriv, hFx.1, hFx.2, G]
      have hgψ : surfaceGradient S ψ x =
          (η x * η x) • (-G x) + (1 - T (W x)) • (η x • B x + η x • B x) := by
        dsimp only [ψ]
        rw [surfaceGradient_mul (S := S) (g := fun y ↦ 1 - T (F y)) ((hη.mul hη).differentiable (by simp) x)
          ((contDiff_const.sub hTF).differentiable (by simp) x)]
        rw [surfaceGradient_const_sub S 1, hgT,
          surfaceGradient_mul (hη.differentiable (by simp) x) (hη.differentiable (by simp) x), hFx.1]
      have heq : inner ℝ (G x) (surfaceGradient S ψ x) =
          inner ℝ (A x) ((2 * (1 - T (W x))) • B x - A x) := by
        rw [hgψ]
        simp only [A, inner_add_right, real_inner_smul_right, inner_neg_right,
          real_inner_smul_left, inner_sub_right]
        ring
      rw [heq]
      exact truncation_test_pointwise (A x) (B x)
        (smoothTruncation_nonneg ε (hW0 x hxr)) (smoothTruncation_le_one_all hε (W x))
    · have hAx : A x = 0 := by simp only [A, image_eq_zero_of_notMem_tsupport hxt, zero_smul]
      have hBx : B x = 0 := surfaceGradient_eq_zero_of_notMem_tsupport S hxt
      rw [surfaceGradient_eq_zero_of_notMem_tsupport S (fun h ↦ hxt (hsub h)),
        inner_zero_right, hAx, hBx]
      norm_num
  rw [integral_sub (hBs.const_mul 2) (hAs.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hle
  change (∫ x, ‖A x‖ ^ 2 ∂surfaceMeasure S) ≤ 4 * ∫ x, ‖B x‖ ^ 2 ∂surfaceMeasure S
  linarith

end RegularEnergy
end RPI.Boundary

end

end OAI
