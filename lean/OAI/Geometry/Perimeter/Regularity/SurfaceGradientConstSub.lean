import OAI.Geometry.Perimeter.Regularity.IntegralInnerEqInnerToLp

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem surfaceGradient_const_sub {n : ℕ} (S : Set (Space n)) {f : Space n → ℝ}
    {x : Space n} (c : ℝ) :
    surfaceGradient S (fun y ↦ c - f y) x = -surfaceGradient S f x := by
  have hg : gradient (fun y ↦ c - f y) x = -gradient f x := by
    apply (InnerProductSpace.toDual ℝ (Space n)).injective
    simp only [map_neg, toDual_gradient]
    exact fderiv_const_sub c
  simp only [surfaceGradient, hg, map_neg, Submodule.coe_neg]

section RegularEnergy
variable {n : ℕ} {S Z : Set (Space n)}
variable (hS : IsClosed S) (hZ : IsClosed Z)
variable (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
include hS hZ hfinite hgrad

theorem regular_gradient_memLp_test {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    {η : Space n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηZ : Disjoint (tsupport η) Z) :
    MemLp (fun x ↦ η x • D x) 2 (surfaceMeasure S) := by
  have hi := regular_gradient_memLp_indicator_test hS hZ hfinite hgrad htrace hcη hηZ
  obtain ⟨M, hM⟩ := hcη.exists_bound_of_continuous hη.continuous
  have hh : MemLp (fun x ↦ η x • (tsupport η).indicator D x) 2 (surfaceMeasure S) := by
    apply hi.of_le_mul (c := M) (hη.continuous.aestronglyMeasurable.smul hi.aestronglyMeasurable)
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

omit hS hZ hfinite hgrad in
theorem smoothTruncation_le_one_all {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    smoothTruncation ε s ≤ 1 := by
  by_cases hs : 0 ≤ s
  · exact (smoothTruncation_le_min hε hs).trans (min_le_right _ _)
  · have hh := smoothTruncation_monotone ε (le_of_not_ge hs)
    have hz : smoothTruncation ε 0 = 0 := by simp [smoothTruncation]
    exact (hh.trans_eq hz).trans zero_le_one

theorem smoothTruncation_regular_energy {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
    (hW0 : ∀ x ∈ S \ Z, 0 ≤ W x)
    (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
    {ε : ℝ} (hε : 0 < ε) {η : Space n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηZ : Disjoint (tsupport η) Z) :
    (∫ x, ‖η x • (truncationSlope ε (W x) • D x)‖ ^ 2 ∂surfaceMeasure S) ≤
      4 * ∫ x, ‖surfaceGradient S η x‖ ^ 2 ∂surfaceMeasure S := by
  let T := smoothTruncation ε
  let G : Space n → Space n := fun x ↦ truncationSlope ε (W x) • D x
  have htt : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S (T ∘ W) G x := by
    intro x hx
    simpa only [T, G, smoothTruncation_deriv] using
      (htrace x hx).comp hx.1 (smoothTruncation_contDiff ε)
  obtain ⟨F, hF, he⟩ := exists_smooth_representative_near_regular_test hS hZ htrace
    (isClosed_tsupport η) hηZ
  let ψ : Space n → ℝ := fun x ↦ (η x * η x) * (1 - T (F x))
  have hTF : ContDiff ℝ ∞ (T ∘ F) := (smoothTruncation_contDiff ε).comp hF
  have hψ : ContDiff ℝ ∞ ψ := (hη.mul hη).mul (contDiff_const.sub hTF)
  have hcψ : HasCompactSupport ψ := hcη.mul_right.mul_right
  have hsub : tsupport ψ ⊆ tsupport η := tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hψZ : Disjoint (tsupport ψ) Z := hηZ.mono_left hsub
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x ↦ mul_nonneg (mul_self_nonneg (η x))
    (sub_nonneg.mpr (smoothTruncation_le_one_all hε (F x)))
  have ht : 0 ≤ ∫ x, inner ℝ (G x) (surfaceGradient S ψ x) ∂surfaceMeasure S :=
    smoothTruncation_regular_test hS hZ hfinite hgrad htrace hsup hε hψ hcψ hψZ hψ0
  let A : Space n → Space n := fun x ↦ η x • G x
  let B : Space n → Space n := surfaceGradient S η
  have hA : MemLp A 2 (surfaceMeasure S) :=
    regular_gradient_memLp_test hS hZ hfinite hgrad htt hη hcη hηZ
  have hB : MemLp B 2 (surfaceMeasure S) :=
    surfaceGradient_memLp_of_compact hfinite hgrad hη hcη
  have hi := integrable_regular_test_pair hS hZ hfinite hgrad htt hψ hcψ hψZ
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
variable (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
  AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
variable {W : Space n → ℝ} {D : Space n → Space n}
variable (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
variable (hsup : ∀ φ : Space n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
  Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
  0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient S φ x) ∂surfaceMeasure S)
include hS hZ hfinite hgrad htrace hsup

theorem min_regular_test {φ : Space n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφZ : Disjoint (tsupport φ) Z) (hpφ : ∀ x, 0 ≤ φ x) :
    0 ≤ ∫ x, inner ℝ (truncatedGradient W D x) (surfaceGradient S φ x) ∂surfaceMeasure S := by
  let b : Space n → ℝ := fun x ↦ inner ℝ (D x) (surfaceGradient S φ x)
  have hb : Integrable b (surfaceMeasure S) :=
    integrable_regular_test_pair hS hZ hfinite hgrad htrace hφ hcφ hφZ
  let q : ℕ → Space n → ℝ := fun j x ↦
    inner ℝ (truncationSlope (truncationParameter j) (W x) • D x) (surfaceGradient S φ x)
  have hq : ∀ j, AEStronglyMeasurable (q j) (surfaceMeasure S) := by
    intro j
    have htt : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S (smoothTruncation (truncationParameter j) ∘ W)
        (fun y ↦ truncationSlope (truncationParameter j) (W y) • D y) x := by
      intro x hx
      simpa only [smoothTruncation_deriv] using
        (htrace x hx).comp hx.1 (smoothTruncation_contDiff (truncationParameter j))
    exact (integrable_regular_test_pair hS hZ hfinite hgrad htt hφ hcφ hφZ).aestronglyMeasurable
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
  exact smoothTruncation_regular_test hS hZ hfinite hgrad htrace hsup
    (truncationParameter_pos j) hφ hcφ hφZ hpφ

theorem min_regular_energy (hW0 : ∀ x ∈ S \ Z, 0 ≤ W x)
    {η : Space n → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hηZ : Disjoint (tsupport η) Z) :
    MemLp (fun x ↦ η x • truncatedGradient W D x) 2 (surfaceMeasure S) ∧
      vectorEnergy (surfaceMeasure S) (fun x ↦ η x • truncatedGradient W D x) ≤
        4 * vectorEnergy (surfaceMeasure S) (surfaceGradient S η) := by
  let A : ℕ → Space n → Space n := fun j x ↦ η x • (truncationSlope (truncationParameter j) (W x) • D x)
  let H : Space n → Space n := fun x ↦ η x • truncatedGradient W D x
  have hA : ∀ j, MemLp (A j) 2 (surfaceMeasure S) := by
    intro j
    have htt : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S (smoothTruncation (truncationParameter j) ∘ W)
        (fun y ↦ truncationSlope (truncationParameter j) (W y) • D y) x := by
      intro x hx
      simpa only [smoothTruncation_deriv] using
        (htrace x hx).comp hx.1 (smoothTruncation_contDiff (truncationParameter j))
    exact regular_gradient_memLp_test hS hZ hfinite hgrad htt hη hcη hηZ
  have hB : MemLp (surfaceGradient S η) 2 (surfaceMeasure S) :=
    surfaceGradient_memLp_of_compact hfinite hgrad hη hcη
  have he : ∀ j, vectorEnergy (surfaceMeasure S) (A j) ≤
      4 * vectorEnergy (surfaceMeasure S) (surfaceGradient S η) := by
    intro j
    have h := ENNReal.ofReal_le_ofReal (smoothTruncation_regular_energy hS hZ hfinite hgrad
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
namespace RPI

theorem vectorEnergy_restrict_of_vanish {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] {μ : Measure X} {U : Set X} (hU : MeasurableSet U)
    {F : X → V} (hF : ∀ x ∉ U, F x = 0) :
    vectorEnergy (μ.restrict U) F = vectorEnergy μ F := by
  unfold vectorEnergy
  rw [← lintegral_indicator hU]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ U
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, hF x hx, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, ENNReal.ofReal_zero]

end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary

theorem min_local_energy {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (hZ : IsClosed Z)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hfinite : ∀ R : ℝ, 0 < R → (surfaceMeasure S) (Metric.ball 0 R) < ⊤)
    (hgrad : ∀ f : Space n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient S f) (surfaceMeasure S))
    (hgrowth : ∀ R : ℝ, 0 < R → ∃ A r₀ : ℝ, 0 < A ∧ 0 < r₀ ∧
      ∀ c ∈ Z ∩ Metric.closedBall 0 R, ∀ r : ℝ, 0 < r → r < r₀ →
        (surfaceMeasure S).restrict (Metric.ball 0 R) (Metric.ball c r) ≤
          ENNReal.ofReal (A * r ^ (n - 1)))
    {W : Space n → ℝ} {D : Space n → Space n}
    (htrace : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S W D x)
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
    (fun f hf ↦ (hgrad f hf).mono_measure Measure.restrict_le_self) hA hr₀
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
    exact min_regular_energy hS hZ hfinite hgrad htrace hsup hW0 (hη i) (hcη i) (hηZ i)
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

theorem perimeter_mono_region {n : ℕ} (E : Set (Euc n)) {U V : Set (Euc n)}
    (hUV : U ⊆ V) : perimeter E U ≤ perimeter E V := by
  unfold perimeter
  refine iSup_le fun f ↦ iSup_le fun hf ↦ iSup_le fun hc ↦ iSup_le fun hs ↦ iSup_le fun hb ↦ ?_
  exact le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hc
    (le_iSup_of_le (hs.trans hUV) (le_iSup_of_le hb le_rfl))))

theorem isClosed_perimeterSupport {n : ℕ} (E : Set (Euc n)) :
    IsClosed (perimeterSupport E) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  simp only [mem_compl_iff, perimeterSupport, mem_ofPred_eq] at hx
  push Not at hx
  obtain ⟨r, hr, hp⟩ := hx
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro y hy
  change ¬ ∀ s : ℝ, 0 < s → 0 < perimeter E (Metric.ball y s)
  intro hys
  have hsub : Metric.ball y (r / 2) ⊆ Metric.ball x r := by
    intro z hz
    apply Metric.mem_ball.mpr
    have h1 := Metric.mem_ball.mp hy
    have h2 := Metric.mem_ball.mp hz
    have h3 := dist_triangle z y x
    linarith
  exact (not_lt_of_ge ((perimeter_mono_region E hsub).trans hp)) (hys (r / 2) (half_pos hr))

open RPI RPI.Boundary

theorem min_wholeBoundarySobolev_and_supersolution_of_regular_geometry
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
    (htrace : ∀ x ∈ perimeterSupport E \ Z, HasSmoothTraceJetAt (perimeterSupport E) W D x)
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
  have hgrad : ∀ f : Euc n → ℝ, ContDiff ℝ ∞ f →
      AEStronglyMeasurable (surfaceGradient (perimeterSupport E) f)
        (surfaceMeasure (perimeterSupport E)) := by
    intro f hf
    exact surfaceGradient_aestronglyMeasurable_of_regular_locus hn hS.measurableSet
      hZ.measurableSet hZd hlevel (hf.of_le (by norm_num))
  have hloc : ∀ R : ℝ, 0 < R → MemLp (truncatedGradient W D) 2
      ((surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R)) := by
    intro R hR
    exact min_local_energy hn hS hZ hZd hfinite hgrad hgrowth htrace hW0 hsup hR
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
    obtain ⟨hh, hpair⟩ := min_one_mem_sobolevGraph_ball hn hS hZ hZd hR htrace hw (hloc R hR)
      (fun f hf ↦ (hgrad f hf).mono_measure Measure.restrict_le_self) hA hr₀ (by
        intro c hc r hr hrr
        apply le_trans _ (hgr c hc r hr hrr)
        exact Measure.le_iff'.mp (Measure.restrict_mono_set _
          (Metric.ball_subset_ball (by linarith : R ≤ R + 2))) _)
    exact ⟨hh, hloc R hR, hpair⟩
  · intro φ hφ hcφ hpφ
    have hh := full_test_of_regular_tests hn hZ hZd hloc hfinite hgrad hgrowth
      (fun ψ hψ hcψ hψZ hpψ ↦ min_regular_test hS hZ hfinite hgrad htrace hsup hψ hcψ hψZ hpψ)
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

end OAI
