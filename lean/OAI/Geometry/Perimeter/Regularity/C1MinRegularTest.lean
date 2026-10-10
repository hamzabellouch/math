import OAI.Geometry.Perimeter.Regularity.RegularSupersolutionC1Test

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
section TruncationRegularLimit
variable {n : ℕ} {S Z : Set (Space n)}
variable (hS : IsClosed S) (hZ : IsClosed Z)
variable (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
variable {W : Space n → ℝ} {D : Space n → Space n}
variable (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
variable (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
  Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
  0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
include hS hZ hfinite hgrad htrace hsup

theorem c1_min_regular_test {φ : Space n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hφZ : Disjoint (tsupport φ) Z) (hpφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, inner ℝ (truncatedGradient W D x) (surfaceGradient S φ x) ∂surfaceMeasure S := by
  let b : Space n → ℝ := fun x ↦ inner ℝ (D x) (surfaceGradient S φ x)
  have hb : Integrable b (surfaceMeasure S) :=
    c1_integrable_regular_test_pair hS hZ hfinite hgrad htrace hφ hcφ hφZ
  let q : ℕ → Space n → ℝ := fun j x ↦
    inner ℝ (truncationSlope (truncationParameter j) (W x) • D x) (surfaceGradient S φ x)
  have hq : ∀ j, AEStronglyMeasurable (q j) (surfaceMeasure S) := by
    intro j
    have htt : ∀ x ∈ S \ Z, HasC1TraceJetAt S (smoothTruncation (truncationParameter j) ∘ W)
        (fun y ↦ truncationSlope (truncationParameter j) (W y) • D y) x := by
      intro x hx
      simpa only [smoothTruncation_deriv] using
        (htrace x hx).comp hx.1 ((smoothTruncation_contDiff (truncationParameter j)).of_le (by norm_num))
    exact (c1_integrable_regular_test_pair hS hZ hfinite hgrad htt hφ hcφ hφZ).aestronglyMeasurable
  have hlim : Tendsto (fun j ↦ ∫ x, q j x ∂surfaceMeasure S) atTop
      (𝓝 (∫ x, inner ℝ (truncatedGradient W D x) (surfaceGradient S φ x) ∂surfaceMeasure S)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖b x‖) hq hb.norm
    · intro j
      apply ae_of_all
      intro x
      simp only [q, real_inner_smul_left, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (truncationSlope_norm_le _ _)
    · apply ae_of_all
      intro x
      have ht := (truncationSlope_tendsto (W x)).mul_const (b x)
      by_cases hx : W x < 1
      · simpa only [q, b, truncatedGradient, ite_eq_left hx, one_mul, real_inner_smul_left] using ht
      · simpa only [q, b, truncatedGradient, ite_eq_right hx, zero_mul, inner_zero_left,
          real_inner_smul_left] using ht
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  exact c1_smoothTruncation_regular_test hS hZ hfinite hgrad htrace hsup
    (truncationParameter_pos j) hφ hcφ hφZ hpφ

theorem c1_min_regular_energy (hW0 : ∀ x ∈ S \ Z, 0 ≤ W x)
    {η : Space n → ℝ} (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hηZ : Disjoint (tsupport η) Z) :
    MemLp (fun x ↦ η x • truncatedGradient W D x) 2 (surfaceMeasure S) ∧
      vectorEnergy (surfaceMeasure S) (fun x ↦ η x • truncatedGradient W D x) ≤
        4 * vectorEnergy (surfaceMeasure S) (surfaceGradient S η) := by
  let A : ℕ → Space n → Space n := fun j x ↦ η x • (truncationSlope (truncationParameter j) (W x) • D x)
  let H : Space n → Space n := fun x ↦ η x • truncatedGradient W D x
  have hA : ∀ j, MemLp (A j) 2 (surfaceMeasure S) := by
    intro j
    have htt : ∀ x ∈ S \ Z, HasC1TraceJetAt S (smoothTruncation (truncationParameter j) ∘ W)
        (fun y ↦ truncationSlope (truncationParameter j) (W y) • D y) x := by
      intro x hx
      simpa only [smoothTruncation_deriv] using
        (htrace x hx).comp hx.1 ((smoothTruncation_contDiff (truncationParameter j)).of_le (by norm_num))
    exact c1_regular_gradient_memLp_test hS hZ hfinite hgrad htt hη hcη hηZ
  have hB : MemLp (surfaceGradient S η) 2 (surfaceMeasure S) :=
    c1_surfaceGradient_memLp_of_compact hfinite hgrad hη hcη
  have he : ∀ j, vectorEnergy (surfaceMeasure S) (A j) ≤
      4 * vectorEnergy (surfaceMeasure S) (surfaceGradient S η) := by
    intro j
    have h := ENNReal.ofReal_le_ofReal (c1_smoothTruncation_regular_energy hS hZ hfinite hgrad
      htrace hW0 hsup (truncationParameter_pos j) hη hcη hηZ)
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at h
    simpa only [A, vectorEnergy, ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (hA j).aestronglyMeasurable).mp (hA j))
      (ae_of_all _ (fun x ↦ sq_nonneg ‖A j x‖)),
      ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB)
      (ae_of_all _ (fun x ↦ sq_nonneg ‖surfaceGradient S η x‖)), ENNReal.ofReal_ofNat] using h
  have hlim : ∀ᵐ x ∂surfaceMeasure S, Tendsto (fun j ↦ A j x) atTop (𝓝 (H x)) := by
    apply ae_of_all
    intro x
    have ht := (tendsto_const_nhds (x := η x)).smul
      ((truncationSlope_tendsto (W x)).smul_const (D x))
    by_cases hx : W x < 1
    · simpa only [A, H, truncatedGradient, ite_eq_left hx, one_smul] using ht
    · simpa only [A, H, truncatedGradient, ite_eq_right hx, zero_smul] using ht
  have hHm : AEStronglyMeasurable H (surfaceMeasure S) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun j ↦ (hA j).aestronglyMeasurable) hlim
  have hHE := vectorEnergy_le_of_ae_tendsto (fun j ↦ (hA j).aestronglyMeasurable) hlim
    (Eventually.of_forall he) tendsto_const_nhds
  refine ⟨(memLp_two_iff_vectorEnergy hHm).mpr (hHE.trans_lt ?_), hHE⟩
  exact ENNReal.mul_lt_top (by norm_num) ((memLp_two_iff_vectorEnergy hB.aestronglyMeasurable).mp hB)

end TruncationRegularLimit
end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem c1_min_local_energy {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (hZ : IsClosed Z)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ 1 f →
      AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
    (hgrowth : ∀ R : ℝ, 0 < R → ∃ A r₀ : ℝ, 0 < A ∧ 0 < r₀ ∧
      ∀ c ∈ Z ∩ Metric.closedBall 0 R, ∀ r : ℝ, 0 < r → r < r₀ →
        (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
          ENNReal.ofReal (A * r ^ (n - 1)))
    {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasC1TraceJetAt S W D x)
    (hW0 : ∀ x ∈ S \ Z, 0 ≤ W x)
    (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
    {R : ℝ} (hR : 0 < R) :
    MemLp (truncatedGradient W D) 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)) := by
  let b : ContDiffBump (0 : Space n) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  let μ := (surfaceMeasure S).restrict (Metric.ball 0 (R + 3))
  have hR3 : 0 < R + 3 := by linarith
  have : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hfinite _ hR3⟩
  let K := Z ∩ tsupport b
  have hKc : IsCompact K := b.hasCompactSupport.of_isClosed_subset
    (hZ.inter (isClosed_tsupport b)) inter_subset_right
  have hKd : dimH K ≤ (n - 8 : ℕ) := (dimH_mono inter_subset_left).trans hZd
  have hbs : tsupport b ⊆ Metric.ball (0 : Space n) (R + 3) := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  obtain ⟨A, r₀, hA, hr₀, hgr⟩ := hgrowth _ hR3
  obtain ⟨χ, hχ, hχlim, hχE⟩ := exists_memLp_capacity_sequence hn S
    (Metric.ball 0 (R + 3)) K hKc hKd
    (fun f hf ↦ (hgrad f (hf.of_le (by norm_num))).mono_measure Measure.restrict_le_self) hA hr₀
    (fun c hc s hs hsr ↦ hgr c ⟨hc.1, Metric.ball_subset_closedBall (hbs hc.2)⟩ s hs hsr)
  have hb : MemLp (fun x ↦ b x) 2 μ := MemLp.of_bound b.continuous.aestronglyMeasurable 1
    (ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg b.nonneg] using b.le_one))
  have hDb : MemLp (surfaceGradient S b) 2 μ := surfaceGradient_memLp_on_ball b.contDiff
    ((hgrad b b.contDiff).mono_measure Measure.restrict_le_self)
  obtain ⟨_, hB, hBt⟩ := capacity_product_pair_tendsto hb hDb χ
    (fun i ↦ (hχ i).1.continuous.aestronglyMeasurable)
    (fun i ↦ ae_of_all _ (hχ i).2.1) hχlim zero_le_one
    (ae_of_all _ (fun x ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg b.nonneg] using b.le_one))
    (fun i ↦ surfaceGradient S (χ i)) (fun i ↦ (hχ i).2.2.2) hχE
  let η : ℕ → Space n → ℝ := fun i x ↦ b x * χ i x
  let F : ℕ → Space n → Space n := fun i x ↦ η i x • truncatedGradient W D x
  let H : Space n → Space n := fun x ↦ b x • truncatedGradient W D x
  have hη : ∀ i, ContDiff ℝ ∞ (η i) := fun i ↦ b.contDiff.mul (hχ i).1
  have hcη : ∀ i, HasCompactSupport (η i) := fun _ ↦ b.hasCompactSupport.mul_right
  have hηZ : ∀ i, Disjoint (tsupport (η i)) Z := fun i ↦
    tsupport_mul_disjoint_Singular (hχ i).2.2.1
  have hFE : ∀ i, MemLp (F i) 2 (surfaceMeasure S) ∧
      vectorEnergy (surfaceMeasure S) (F i) ≤
        4 * vectorEnergy (surfaceMeasure S) (surfaceGradient S (η i)) := by
    intro i
    exact c1_min_regular_energy hS hZ hfinite hgrad htrace hsup hW0 ((hη i).of_le (by norm_num)) (hcη i) (hηZ i)
  have hFm : ∀ i, MemLp (F i) 2 μ := fun i ↦ (hFE i).1.mono_measure Measure.restrict_le_self
  have hB_eq : ∀ i, (fun x ↦ χ i x • surfaceGradient S b x + b x • surfaceGradient S (χ i) x) =
      surfaceGradient S (η i) := by
    intro i
    funext x
    change _ = surfaceGradient S (fun y ↦ b y * χ i y) x
    have hbDiff : ContDiff ℝ ∞ (fun y ↦ b y) := b.contDiff
    rw [surfaceGradient_mul (hbDiff.differentiable (by simp) x)
      ((hχ i).1.differentiable (by simp) x), add_comm]
  have hBE := vectorEnergy_tendsto_of_toLp_tendsto hB hDb hBt.snd_nhds
  simp_rw [hB_eq] at hBE
  have hbound : ∀ i, vectorEnergy μ (F i) ≤ 4 * vectorEnergy μ (surfaceGradient S (η i)) := by
    intro i
    rw [vectorEnergy_restrict_of_vanish measurableSet_ball, vectorEnergy_restrict_of_vanish measurableSet_ball]
    · exact (hFE i).2
    · intro x hx
      exact surfaceGradient_eq_zero_of_notMem_tsupport S
        (fun h ↦ hx (hbs (tsupport_mul_subset_left h)))
    · intro x hx
      have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hbs h))
      simp only [F, η, hb0, zero_mul, zero_smul]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) atTop (𝓝 (H x)) := by
    filter_upwards [hχlim] with x hx
    simpa only [F, H, η, mul_one] using
      (tendsto_const_nhds.mul hx).smul_const (truncatedGradient W D x)
  have hHm : AEStronglyMeasurable H μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun i ↦ (hFm i).aestronglyMeasurable) hlim
  have hHE := vectorEnergy_le_of_ae_tendsto (fun i ↦ (hFm i).aestronglyMeasurable) hlim
    (Eventually.of_forall hbound) (ENNReal.Tendsto.const_mul hBE (Or.inr (by norm_num)))
  have hH : MemLp H 2 μ := (memLp_two_iff_vectorEnergy hHm).mpr (hHE.trans_lt
    (ENNReal.mul_lt_top (by norm_num) ((memLp_two_iff_vectorEnergy hDb.aestronglyMeasurable).mp hDb)))
  have hHR : MemLp H 2 ((surfaceMeasure S).restrict (Metric.ball 0 R)) :=
    hH.mono_measure (Measure.restrict_mono_set _ (Metric.ball_subset_ball (by linarith)))
  apply hHR.ae_eq
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hbx : b x = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall.mpr
    ((Metric.mem_ball.mp hx).le.trans (by dsimp [b]; linarith)))
  simp only [H, hbx, one_smul]

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem c1_min_wholeBoundarySobolev_and_supersolution_of_regular_geometry
    {n : ℕ} (hn : 8 ≤ n) {E Z : Set (Euc n)} (hE : MeasurableSet E)
    (hZ : IsClosed Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hfinite : ∀ R : ℝ, 0 < R → surfaceMeasure (perimeterSupport E) (Metric.ball 0 R) < ⊤)
    (hgrowth : ∀ R : ℝ, 0 < R → ∃ A r₀ : ℝ, 0 < A ∧ 0 < r₀ ∧
      ∀ c ∈ Z ∩ Metric.closedBall 0 R, ∀ r : ℝ, 0 < r → r < r₀ →
        (surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
          ENNReal.ofReal (A * r ^ (n - 1)))
    (hreg : ∀ x ∈ perimeterSupport E \ Z, ∃ U : Set (Euc n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Euc n → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ perimeterSupport E ↔ f y = 0) ∧
        (∀ y ∈ U, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)))
    {W : Euc n → ℝ} {D : Euc n → Euc n}
    (htrace : ∀ x ∈ perimeterSupport E \ Z, HasC1TraceJetAt (perimeterSupport E) W D x)
    (hW0 : ∀ x ∈ perimeterSupport E \ Z, 0 ≤ W x)
    (hsup : ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient (perimeterSupport E) φ x)
        ∂surfaceMeasure (perimeterSupport E)) :
    WholeBoundarySobolev E (fun x ↦ min (W x) 1) (truncatedGradient W D) ∧
      WholeBoundarySupersolution E (truncatedGradient W D) := by
  have hS := isClosed_perimeterSupport E
  have hlevel : ∀ x ∈ perimeterSupport E \ Z, ∃ U : Set (Euc n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Euc n → ℝ, ContDiffOn ℝ 1 f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ perimeterSupport E ↔ f y = 0) := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, hdf, hs, _⟩ := hreg x hx
    exact ⟨U, hU, hxU, f, hf.of_le (by norm_num), hdf, hs⟩
  have hfilled : ∀ x ∈ perimeterSupport E \ Z, ∃ f : Euc n → ℝ,
      ContDiffAt ℝ 1 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ perimeterSupport E ↔ f y = 0) ∧
      (∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)) := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, hdf, hs, he⟩ := hreg x hx
    refine ⟨f, (hf.of_le (by norm_num)).contDiffAt (hU.mem_nhds hxU),
      (hs x hxU).mp hx.1, hdf x hxU, ?_, ?_⟩
    · filter_upwards [hU.mem_nhds hxU] with y hy using hs y hy
    · filter_upwards [hU.mem_nhds hxU] with y hy using he y hy
  have hgrad : ∀ f : Euc n → ℝ, ContDiff ℝ 1 f →
      AEStronglyMeasurable (surfaceGradient (perimeterSupport E) f)
        (surfaceMeasure (perimeterSupport E)) := by
    intro f hf
    exact surfaceGradient_aestronglyMeasurable_of_regular_locus hn hS.measurableSet
      hZ.measurableSet hZd hlevel hf
  have hloc : ∀ R : ℝ, 0 < R → MemLp (truncatedGradient W D) 2
      ((surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R)) := by
    intro R hR
    exact c1_min_local_energy hn hS hZ hZd hfinite hgrad hgrowth htrace hW0 hsup hR
  have haereg : ∀ᵐ x ∂surfaceMeasure (perimeterSupport E), x ∈ perimeterSupport E \ Z := by
    have hz : ∀ᵐ x ∂surfaceMeasure (perimeterSupport E), x ∉ Z := by
      simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
        surfaceMeasure_zero_of_singular_dim hn (perimeterSupport E) Z hZd
    filter_upwards [ae_restrict_mem hS.measurableSet, hz] with x hx hzx
    exact ⟨hx, hzx⟩
  constructor
  · apply wholeBoundarySobolev_of_local_sobolevGraph_filled hn hE hS.measurableSet hZd hfilled
    intro R hR
    have : IsFiniteMeasure ((surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using hfinite R hR⟩
    have hw : ∀ᵐ x ∂(surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R), 0 ≤ W x := by
      filter_upwards [haereg.filter_mono (ae_mono Measure.restrict_le_self)] with x hx
      exact hW0 x hx
    obtain ⟨A, r₀, hA, hr₀, hgr⟩ := hgrowth (R + 2) (by linarith)
    obtain ⟨hh, hpair⟩ := c1_min_one_mem_sobolevGraph_ball hn hS hZ hZd hR htrace hw (hloc R hR)
      (fun f hf ↦ (hgrad f (hf.of_le (by norm_num))).mono_measure Measure.restrict_le_self) hA hr₀ (by
        intro c hc r hr hrr
        apply le_trans _ (hgr c hc r hr hrr)
        exact Measure.le_iff'.mp (Measure.restrict_mono_set _
          (Metric.ball_subset_ball (by linarith : R ≤ R + 2))) _)
    exact ⟨hh, hloc R hR, hpair⟩
  · intro φ hφ hcφ hpφ
    have hh := full_test_of_regular_tests hn hZ hZd hloc hfinite (fun f hf ↦ hgrad f (hf.of_le (by norm_num))) hgrowth
      (fun ψ hψ hcψ hψZ hpψ ↦ c1_min_regular_test hS hZ hfinite hgrad htrace hsup (hψ.of_le (by norm_num)) hcψ hψZ hpψ)
      hφ hcφ hpφ
    have heq := surfaceGradient_ae_eq_tangentialGradient_filled hn hE hS.measurableSet hZd hfilled φ
    rw [boundaryArea_eq_smul_surfaceMeasure, integral_smul_measure]
    have hi : (∫ x, inner ℝ (truncatedGradient W D x) (tangentialGradient E φ x)
        ∂surfaceMeasure (perimeterSupport E)) =
        ∫ x, inner ℝ (truncatedGradient W D x) (surfaceGradient (perimeterSupport E) φ x)
          ∂surfaceMeasure (perimeterSupport E) := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    rw [hi]
    exact mul_nonneg ENNReal.toReal_nonneg hh

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem c1_min_wholeBoundarySobolev_and_supersolution_of_minimizing_regular_geometry
    {n : ℕ} (hn : 8 ≤ n) {E Z : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E)
    (hZ : IsClosed Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ perimeterSupport E \ Z, ∃ U : Set (Euc n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Euc n → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ perimeterSupport E ↔ f y = 0) ∧
        (∀ y ∈ U, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)))
    {W : Euc n → ℝ} {D : Euc n → Euc n}
    (htrace : ∀ x ∈ perimeterSupport E \ Z, HasC1TraceJetAt (perimeterSupport E) W D x)
    (hW0 : ∀ x ∈ perimeterSupport E \ Z, 0 ≤ W x)
    (hsup : ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient (perimeterSupport E) φ x)
        ∂surfaceMeasure (perimeterSupport E)) :
    WholeBoundarySobolev E (fun x ↦ min (W x) 1) (truncatedGradient W D) ∧
      WholeBoundarySupersolution E (truncatedGradient W D) := by
  have hhalf : ∀ x ∈ perimeterSupport E \ Z, ∃ v, HasHalfspaceBlowup E x v := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, hdf, hs, he⟩ := hreg x hx
    refine ⟨_, hasHalfspaceBlowup_gradient_filled hmin.1
      ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num))
      ((hs x hxU).mp hx.1) (hdf x hxU) ?_⟩
    filter_upwards [hU.mem_nhds hxU] with y hy using he y hy
  obtain ⟨A, hA, harea⟩ := exists_minimizing_surfaceMeasure_growth_of_halfspace hn hmin hZd hhalf
  apply c1_min_wholeBoundarySobolev_and_supersolution_of_regular_geometry hn hmin.1 hZ hZd
    (fun R hR ↦ (harea 0 R hR).trans_lt ENNReal.ofReal_lt_top) _ hreg htrace hW0 hsup
  intro R hR
  refine ⟨A, 1, hA, by norm_num, ?_⟩
  intro c hc r hr hrr
  exact (Measure.restrict_apply_le (Metric.ball 0 R) (Metric.ball c r)).trans (harea c r hr)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI.Boundary
open ContinuousLinearMap
open scoped Convolution

theorem divergence_comp_add_right {n : ℕ} {V : Euc n → Euc n}
    (hV : Differentiable ℝ V) (t x : Euc n) :
    divergence (fun y ↦ V (y + t)) x = divergence V (x + t) := by
  have hd : fderiv ℝ (fun y ↦ V (y + t)) x = fderiv ℝ V (x + t) := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using ((hV _).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const t)).fderiv
  simp only [divergence, hd]

theorem integral_divergence_le_perimeter_real {n : ℕ} (E U : Set (Euc n))
    (hP : perimeter E U ≠ ⊤) {V : Euc n → Euc n} (hV : PerimeterAdmissible U V) :
    ∫ x in E, divergence V x ≤ (perimeter E U).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal hP).mp
  rw [perimeter_eq_iSup_tests]
  exact le_iSup_of_le V (le_iSup_of_le hV le_rfl)

theorem indicator_convolution_variation_le {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (hP : perimeter E univ ≠ ⊤)
    {k : Euc n → ℝ} (hkc : Continuous k) (hk : Integrable k volume)
    (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x = 1)
    {V : Euc n → Euc n} (hV : PerimeterAdmissible univ V) :
    (∫ x, (k ⋆[lsmul ℝ ℝ, volume] E.indicator (fun _ ↦ (1 : ℝ))) x * divergence V x) ≤
      (perimeter E univ).toReal := by
  let χ : Euc n → ℝ := E.indicator (fun _ ↦ 1)
  have hmχ : Measurable χ := measurable_const.indicator hE
  have hbχ : ∀ x, ‖χ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ E <;> simp [χ, hx]
  have hd := integrable_divergence hV.1 hV.2.1
  let F : Euc n × Euc n → ℝ := fun p ↦ k p.1 * χ (p.2 - p.1) * divergence V p.2
  have hFi : Integrable F (volume.prod volume) := by
    apply (hk.norm.mul_prod hd.norm).mono'
    · exact ((hkc.measurable.comp measurable_fst).mul
        (hmχ.comp (measurable_snd.sub measurable_fst))).mul
        ((continuous_divergence hV.1).measurable.comp measurable_snd) |>.aestronglyMeasurable
    · apply ae_of_all
      intro p
      simp only [F, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by nlinarith [hbχ (p.2 - p.1), norm_nonneg (k p.1)]) (norm_nonneg _)
  have hinner : ∀ t, (∫ x, F (t, x)) = k t * (∫ y in E, divergence V (y + t)) := by
    intro t
    simp only [F, mul_assoc, integral_const_mul]
    congr 1
    calc
      (∫ x, χ (x - t) * divergence V x) =
          ∫ y, χ y * divergence V (y + t) := by
        simpa only [add_sub_cancel_right] using
          (integral_add_right_eq_self (fun x ↦ χ (x - t) * divergence V x) t).symm
      _ = ∫ y in E, divergence V (y + t) := by
        rw [← integral_indicator hE]
        apply integral_congr_ae
        apply ae_of_all
        intro y
        by_cases hy : y ∈ E <;> simp [χ, hy]
  have hInt : Integrable (fun t ↦ k t * (∫ y in E, divergence V (y + t))) volume := by
    simpa only [hinner] using hFi.integral_prod_left
  have heq : (∫ x, (k ⋆[lsmul ℝ ℝ, volume] χ) x * divergence V x) =
      ∫ t, k t * (∫ y in E, divergence V (y + t)) := by
    calc
      _ = ∫ x, ∫ t, F (t, x) := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        simp only [convolution_def, lsmul_apply, smul_eq_mul, F, integral_mul_const]
      _ = ∫ t, ∫ x, F (t, x) := integral_integral_swap hFi.swap
      _ = _ := by simp only [hinner]
  have hbound : ∀ t, ∫ y in E, divergence V (y + t) ≤ (perimeter E univ).toReal := by
    intro t
    let Vt : Euc n → Euc n := fun y ↦ V (y + t)
    have hVt : PerimeterAdmissible univ Vt := ⟨hV.1.comp (contDiff_id.add contDiff_const),
      hV.2.1.comp_homeomorph (Homeomorph.addRight t), subset_univ _, fun y ↦ hV.2.2.2 _⟩
    simpa only [Vt, divergence_comp_add_right (hV.1.differentiable (by simp))] using
      integral_divergence_le_perimeter_real E univ hP hVt
  rw [heq]
  calc
    (∫ t, k t * (∫ y in E, divergence V (y + t))) ≤
        ∫ t, k t * (perimeter E univ).toReal := by
      exact integral_mono hInt (hk.mul_const _) fun t ↦
        mul_le_mul_of_nonneg_left (hbound t) (hk0 t)
    _ = (perimeter E univ).toReal := by rw [integral_mul_const, hk1, one_mul]

end RPISingularHarnack

end

end OAI
