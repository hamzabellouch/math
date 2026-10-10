import OAI.Geometry.Perimeter.Regularity.SurfaceGradientComp

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI

section CutoffTests
variable {X V : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {μ : Measure X}

theorem integral_inner_eq_inner_toLp {G B : X → V}
    (hG : MemLp G 2 μ) (hB : MemLp B 2 μ) :
    (∫ x, inner ℝ (G x) (B x) ∂μ) = inner ℝ (hG.toLp G) (hB.toLp B) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hG.coeFn_toLp, hB.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem integrable_inner_of_memLp {G B : X → V}
    (hG : MemLp G 2 μ) (hB : MemLp B 2 μ) :
    Integrable (fun x ↦ inner ℝ (G x) (B x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hG.toLp G) (hB.toLp B)).congr
  filter_upwards [hG.coeFn_toLp, hB.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem tendsto_integral_inner_of_L2_zero {G : X → V} (hG : MemLp G 2 μ)
    (C : ℕ → X → V) (hC : ∀ i, MemLp (C i) 2 μ)
    (hC0 : Tendsto (fun i ↦ (eLpNorm (C i) 2 μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, inner ℝ (G x) (C i x) ∂μ) atTop (𝓝 0) := by
  have hClim : Tendsto (fun i ↦ (hC i).toLp (C i)) atTop
      (𝓝 (0 : Lp V 2 μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero, Lp.norm_toLp] using hC0
  have hlim := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hG.toLp G)) hClim
  simp only [inner_zero_right] at hlim
  convert hlim using 1
  ext i
  exact integral_inner_eq_inner_toLp hG (hC i)

theorem energy_inequality_of_capacity_cutoffs
    {G B : X → V} (hG : MemLp G 2 μ) (hB : MemLp B 2 μ)
    (χ : ℕ → X → ℝ) (hχ : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχbound : ∀ i, ∀ᵐ x ∂μ, ‖χ i x‖ ≤ 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    (C : ℕ → X → V) (hC : ∀ i, MemLp (C i) 2 μ)
    (hC0 : Tendsto (fun i ↦ (eLpNorm (C i) 2 μ).toReal) atTop (𝓝 0))
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ μ)
    {M : ℝ} (hφbound : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M)
    (htest : ∀ i, 0 ≤ ∫ x, inner ℝ (G x) (χ i x • B x + φ x • C i x) ∂μ) :
    0 ≤ ∫ x, inner ℝ (G x) (B x) ∂μ := by
  let b : X → ℝ := fun x ↦ inner ℝ (G x) (B x)
  have hb : Integrable b μ := integrable_inner_of_memLp hG hB
  have hmainlim : Tendsto (fun i ↦ ∫ x, χ i x * b x ∂μ) atTop (𝓝 (∫ x, b x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖b x‖)
    · intro i
      exact (hχ i).mul hb.aestronglyMeasurable
    · exact hb.norm
    · intro i
      filter_upwards [hχbound i] with x hx
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
    · filter_upwards [hχlim] with x hx
      simpa only [one_mul] using hx.mul_const (b x)
  have hφG : MemLp (fun x ↦ φ x • G x) 2 μ := by
    apply hG.of_le_mul (c := M) (hφ.smul hG.aestronglyMeasurable)
    filter_upwards [hφbound] with x hx
    change ‖φ x • G x‖ ≤ M * ‖G x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have herrlim : Tendsto (fun i ↦ ∫ x, φ x * inner ℝ (G x) (C i x) ∂μ)
      atTop (𝓝 0) := by
    simpa only [real_inner_smul_left] using tendsto_integral_inner_of_L2_zero hφG C hC hC0
  have hsumlim := hmainlim.add herrlim
  rw [add_zero] at hsumlim
  apply ge_of_tendsto hsumlim
  apply Filter.Eventually.of_forall
  intro i
  have hm : Integrable (fun x ↦ χ i x * b x) μ := hb.bdd_mul (hχ i) (hχbound i)
  have he : Integrable (fun x ↦ φ x * inner ℝ (G x) (C i x)) μ :=
    (integrable_inner_of_memLp hG (hC i)).bdd_mul hφ hφbound
  rw [← integral_add hm he]
  simpa only [inner_add_right, real_inner_smul_right, b] using htest i

end CutoffTests
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem surfaceGradient_memLp_on_ball {n : ℕ} {S : Set (Space n)}
    {R : ℝ} [IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R))]
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hm : AEStronglyMeasurable (surfaceGradient S φ)
      ((surfaceMeasure S).restrict (Metric.ball 0 R))) :
    MemLp (surfaceGradient S φ) 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)) := by
  have hc : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt (hφ.of_le (by norm_num)).contDiffAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Space n) R).exists_bound_of_continuousOn
    hc.continuousOn
  apply MemLp.of_bound hm M
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  calc
    ‖surfaceGradient S φ x‖ ≤ ‖gradient φ x‖ := by
      calc
        _ ≤ ‖(tangentPlane S x).orthogonalProjectionOnto‖ * ‖gradient φ x‖ :=
          (tangentPlane S x).orthogonalProjectionOnto.le_opNorm _
        _ ≤ 1 * ‖gradient φ x‖ := mul_le_mul_of_nonneg_right
          (tangentPlane S x).orthogonalProjectionOnto_norm_le (norm_nonneg _)
        _ = _ := one_mul _
    _ ≤ M := hM x (Metric.ball_subset_closedBall hx)

theorem surfaceGradient_eq_zero_of_notMem_tsupport {n : ℕ} (S : Set (Space n))
    {φ : Space n → ℝ} {x : Space n} (hx : x ∉ tsupport φ) :
    surfaceGradient S φ x = 0 := by
  simp only [surfaceGradient, gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero,
    Submodule.coe_zero]

theorem tsupport_mul_disjoint_Singular {n : ℕ} {Z : Set (Space n)}
    {φ χ : Space n → ℝ}
    (hzero : ∃ U : Set (Space n), IsOpen U ∧ Z ∩ tsupport φ ⊆ U ∧ ∀ x ∈ U, χ x = 0) :
    Disjoint (tsupport (fun x ↦ φ x * χ x)) Z := by
  obtain ⟨U, hU, hZU, he⟩ := hzero
  apply Set.disjoint_left.mpr
  intro x hx hxZ
  have hxφ : x ∈ tsupport φ := tsupport_mul_subset_left hx
  have heq : (fun x ↦ φ x * χ x) =ᶠ[𝓝 x] (0 : Space n → ℝ) := by
    filter_upwards [hU.mem_nhds (hZU ⟨hxZ, hxφ⟩)] with y hy
    simp only [he y hy, mul_zero, Pi.zero_apply]
  exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hx

theorem full_test_of_regular_tests {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hZ : IsClosed Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    {G : Space n → Space n}
    (hloc : ∀ R : ℝ, 0 < R → MemLp G 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)))
    (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
    (hgrad : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ →
      AEStronglyMeasurable (surfaceGradient S φ) (surfaceMeasure S))
    (hgrowth : ∀ R : ℝ, 0 < R → ∃ A r₀ : ℝ, 0 < A ∧ 0 < r₀ ∧
      ∀ c ∈ Z ∩ Metric.closedBall 0 R, ∀ r : ℝ, 0 < r → r < r₀ →
        (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
          ENNReal.ofReal (A * r ^ (n - 1)))
    (hreg : ∀ ψ : Space n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Disjoint (tsupport ψ) Z → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, inner ℝ (G x) (surfaceGradient S ψ x) ∂surfaceMeasure S)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hpφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, inner ℝ (G x) (surfaceGradient S φ x) ∂surfaceMeasure S := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.ball (0 : Space n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let μ := (surfaceMeasure S).restrict (Metric.ball 0 R)
  let : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hfinite R hR⟩
  let K := Z ∩ tsupport φ
  have hKc : IsCompact K := hcφ.of_isClosed_subset
    (hZ.inter (isClosed_tsupport φ)) inter_subset_right
  have hKd : dimH K ≤ (n - 8 : ℕ) := (dimH_mono inter_subset_left).trans hZd
  obtain ⟨A, r₀, hA, hr₀, hgr⟩ := hgrowth R hR
  obtain ⟨χ, hχ, hχlim, hχE⟩ := exists_memLp_capacity_sequence hn S (Metric.ball 0 R) K
    hKc hKd (fun f hf ↦ (hgrad f hf).mono_measure Measure.restrict_le_self) hA hr₀
    (fun c hc s hs hsr ↦ hgr c ⟨hc.1, Metric.ball_subset_closedBall (hsupp hc.2)⟩ s hs hsr)
  have hB : MemLp (surfaceGradient S φ) 2 μ := surfaceGradient_memLp_on_ball hφ
    ((hgrad φ hφ).mono_measure Measure.restrict_le_self)
  have hC0 : Tendsto (fun i ↦ (eLpNorm (surfaceGradient S (χ i)) 2 μ).toReal)
      atTop (𝓝 0) := tendsto_eLpNorm_two_toReal_of_vectorEnergy_zero_of_aestronglyMeasurable
        (fun i ↦ (hχ i).2.2.2.aestronglyMeasurable) hχE
  obtain ⟨M, hM⟩ := hcφ.exists_bound_of_continuous hφ.continuous
  have htesteq : ∀ i, (fun x ↦ χ i x • surfaceGradient S φ x + φ x • surfaceGradient S (χ i) x) =
      surfaceGradient S (fun x ↦ φ x * χ i x) := by
    intro i
    ext x
    rw [surfaceGradient_mul (hφ.differentiable (by simp) x)
      ((hχ i).1.differentiable (by simp) x), add_comm]
  have hnonsupp : ∀ x, x ∉ Metric.ball (0 : Space n) R → surfaceGradient S φ x = 0 :=
    fun x hx ↦ surfaceGradient_eq_zero_of_notMem_tsupport S (fun h ↦ hx (hsupp h))
  have hχnorm : ∀ i, ∀ᵐ x ∂μ, ‖χ i x‖ ≤ 1 := by
    intro i
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg ((hχ i).2.1 x).1]
    exact ((hχ i).2.1 x).2
  have hpair : 0 ≤ ∫ x, inner ℝ (G x) (surfaceGradient S φ x) ∂μ := by
    apply energy_inequality_of_capacity_cutoffs (hloc R hR) hB χ
      (fun i ↦ (hχ i).1.continuous.aestronglyMeasurable) hχnorm hχlim
      (fun i ↦ surfaceGradient S (χ i)) (fun i ↦ (hχ i).2.2.2) hC0
      φ hφ.continuous.aestronglyMeasurable (M := M) (ae_of_all _ hM)
    intro i
    simp_rw [congrFun (htesteq i)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hreg _ (hφ.mul (hχ i).1) hcφ.mul_right
        (tsupport_mul_disjoint_Singular (hχ i).2.2.1)
        (fun x ↦ mul_nonneg (hpφ x) ((hχ i).2.1 x).1)
    · intro x hx
      rw [surfaceGradient_eq_zero_of_notMem_tsupport S
        (fun hx' ↦ hx (hsupp (tsupport_mul_subset_left hx'))), inner_zero_right]
  dsimp only [μ] at hpair
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by rw [hnonsupp x hx, inner_zero_right])] at hpair

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem exists_smooth_representative_near_regular_test {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) (hZ : IsClosed Z) {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    {K : Set (Space n)} (hK : IsClosed K) (hKZ : Disjoint K Z) :
    ∃ F : Space n → ℝ, ContDiff ℝ ∞ F ∧
      (∀ x ∈ S ∩ K, F x = W x ∧ surfaceGradient S F x = D x) := by
  obtain ⟨σ, hσ0, hσ1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ (Space n)) hZ hK hKZ.symm (n := (⊤ : ℕ∞))
  have hσ : ContDiff ℝ ∞ σ := σ.contMDiff.contDiff
  obtain ⟨U, hU, hUZ, hUσ⟩ := mem_nhdsSet_iff_exists.mp hσ0
  obtain ⟨F, hF, hFW, hFD⟩ := exists_smooth_cutoff_trace hS htrace σ hσ
    ⟨U, hU, hUZ, hUσ⟩
  refine ⟨F, hF, ?_⟩
  intro x hx
  have hσx : σ x = 1 := hσ1.self_of_nhdsSet x hx.2
  have hσnear : (σ : Space n → ℝ) =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
    hσ1.filter_mono (nhds_le_nhdsSet hx.2)
  have hσg : surfaceGradient S σ x = 0 := by
    have hg : gradient (σ : Space n → ℝ) x = 0 := by
      simpa only [gradient_fun_const] using hσnear.gradient_eq
    simp only [surfaceGradient, hg, map_zero, Submodule.coe_zero]
  exact ⟨by simpa only [hσx, one_mul] using hFW hx.1,
    by simpa only [hσx, one_smul, hσg, smul_zero, add_zero] using hFD hx.1⟩

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
section RegularTests
variable {n : ℕ} {S Z : Set (Space n)}
variable (hS : IsClosed S) (hZ : IsClosed Z)
variable (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))

include hfinite hgrad

theorem surfaceGradient_memLp_of_compact {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    MemLp (surfaceGradient S φ) 2 (surfaceMeasure S) := by
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.ball (0 : Space n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let : IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite R hR⟩
  have hloc := surfaceGradient_memLp_on_ball (R := R) hφ
    ((hgrad φ hφ).mono_measure Measure.restrict_le_self)
  have hh := (memLp_indicator_iff_restrict measurableSet_ball).mpr hloc
  apply hh.ae_eq
  apply ae_of_all
  intro x
  by_cases hx : x ∈ Metric.ball (0 : Space n) R
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx]
    exact (surfaceGradient_eq_zero_of_notMem_tsupport S (fun h ↦ hx (hsupp h))).symm

include hS hZ

theorem regular_gradient_memLp_indicator_test {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    {φ : Space n → ℝ} (hcφ : HasCompactSupport φ) (hφZ : Disjoint (tsupport φ) Z) :
    MemLp ((tsupport φ).indicator D) 2 (surfaceMeasure S) := by
  obtain ⟨F, hF, he⟩ := exists_smooth_representative_near_regular_test hS hZ htrace
    (isClosed_tsupport φ) hφZ
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Space n) |>.mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.ball (0 : Space n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let : IsFiniteMeasure ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite R hR⟩
  have hloc : MemLp (surfaceGradient S F) 2 ((surfaceMeasure S).restrict (tsupport φ)) :=
    (surfaceGradient_memLp_on_ball (R := R) hF ((hgrad F hF).mono_measure Measure.restrict_le_self)).mono_measure
      (Measure.restrict_mono_set _ hsupp)
  apply ((memLp_indicator_iff_restrict (isClosed_tsupport φ).measurableSet).mpr hloc).ae_eq
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  by_cases hxt : x ∈ tsupport φ
  · simp only [indicator_of_mem hxt, (he x ⟨hx, hxt⟩).2]
  · simp only [indicator_of_notMem hxt]

theorem integrable_regular_test_pair {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφZ : Disjoint (tsupport φ) Z) :
    Integrable (fun x ↦ inner ℝ (D x) (surfaceGradient S φ x)) (surfaceMeasure S) := by
  have hD := regular_gradient_memLp_indicator_test hS hZ hfinite hgrad htrace hcφ hφZ
  have hB := surfaceGradient_memLp_of_compact hfinite hgrad hφ hcφ
  apply (integrable_inner_of_memLp hD hB).congr
  apply ae_of_all
  intro x
  by_cases hxt : x ∈ tsupport φ
  · simp only [indicator_of_mem hxt]
  · simp only [indicator_of_notMem hxt, surfaceGradient_eq_zero_of_notMem_tsupport S hxt,
      inner_zero_right]

theorem smoothTruncation_regular_test {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
    {ε : ℝ} (hε : 0 < ε) {φ : Space n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφZ : Disjoint (tsupport φ) Z) (hpφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, inner ℝ (truncationSlope ε (W x) • D x)
      (surfaceGradient S φ x) ∂surfaceMeasure S := by
  obtain ⟨F, hF, he⟩ := exists_smooth_representative_near_regular_test hS hZ htrace
    (isClosed_tsupport φ) hφZ
  let ψ : Space n → ℝ := fun x ↦ φ x * truncationSlope ε (F x)
  have hψ : ContDiff ℝ ∞ ψ := hφ.mul ((truncationSlope_contDiff ε).comp hF)
  have hcψ : HasCompactSupport ψ := hcφ.mul_right
  have hψZ : Disjoint (tsupport ψ) Z := hφZ.mono_left tsupport_mul_subset_left
  have htt : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S (smoothTruncation ε ∘ W)
      (fun y ↦ truncationSlope ε (W y) • D y) x := by
    intro x hx
    simpa only [smoothTruncation_deriv] using
      (htrace x hx).comp hx.1 (smoothTruncation_contDiff ε)
  have hi := integrable_regular_test_pair hS hZ hfinite hgrad htrace hψ hcψ hψZ
  have hj := integrable_regular_test_pair hS hZ hfinite hgrad htt hφ hcφ hφZ
  apply (hsup ψ hψ hcψ hψZ (fun x ↦ mul_nonneg (hpφ x)
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
        (((truncationSlope_contDiff ε).comp hF).differentiable (by simp) x)]
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

end RegularTests
end RPI.Boundary

end

end OAI
