import Mathlib
import OAI.Geometry.NearbyLagrangian.RealizationInjectivity
import OAI.Geometry.NearbyLagrangian.SphereHeights

namespace OAI

/-! Closed exact realizations with quantitative scale bounds. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.EmbeddedRealization

open scoped Manifold ContDiff InnerProductSpace Topology
open Tubes Tubes.RegularHomogeneous CoreSmoothing Cutoff Scales Set

local instance (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) :=
  ⟨by simp⟩

local instance (n : ℕ) : Nonempty (Sphere n) :=
  (NormedSpace.sphere_nonempty.mpr (by norm_num) :
    (Metric.sphere (0 : Euclidean (n+1)) 1).Nonempty).to_subtype

local instance (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (Euclidean 9) (Euclidean n)) (Base n))

local instance (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)

local instance (n : ℕ) : ChartedSpace (CotangentVector n) (Cotangent n) :=
  inferInstanceAs (ChartedSpace (ModelProd (BaseVector n) (BaseVector n →L[ℝ] ℝ)) (Cotangent n))

local instance (n : ℕ) : IsManifold 𝓘(ℝ, CotangentVector n) ∞ (Cotangent n) := by
  have h : IsManifold (CotangentGeometry.cotangentModel (E := BaseVector n)) ∞
      (Cotangent n) :=
    inferInstanceAs (IsManifold (𝓘(ℝ, BaseVector n).prod 𝓘(ℝ, BaseVector n →L[ℝ] ℝ)) ∞
      (Bundle.TotalSpace (BaseVector n →L[ℝ] ℝ)
        (fun q : Base n => TangentSpace 𝓘(ℝ, BaseVector n) q →L[ℝ] ℝ)))
  rw [modelWithCornersSelf_prod]
  exact h

abbrev realization {n : ℕ} (f : Sphere 9 → RegularHomogeneous (Euclidean (n+1)))
    (R : Sphere 9 → ℝ) (T : ℝ) : Base n → Cotangent n :=
  sourceGeneratingMap (E := Euclidean 9) (n := n) f R T

lemma baseModel_eq (n : ℕ) : baseModel n = 𝓘(ℝ, BaseVector n) :=
  modelWithCornersSelf_prod.symm

lemma cotangentModel_eq (n : ℕ) : cotangentModel n =
    CotangentGeometry.cotangentModel (E := BaseVector n) := by
  unfold cotangentModel CotangentGeometry.cotangentModel
  rw [baseModel_eq]

lemma realization_liouville {n : ℕ}
    (z : Cotangent n) (v : TangentSpace (cotangentModel n) z) :
    CotangentGeometry.liouville (E := BaseVector n) (M := Base n) z v = liouville z v := by
  unfold CotangentGeometry.liouville NearbyLagrangian.liouville
  simp only [cotangentModel, baseModel, CotangentGeometry.cotangentModel]
  rfl

lemma realization_liouvilleInChart {n : ℕ}
    (z : Cotangent n) (x : CotangentVector n) :
    CotangentGeometry.liouvilleInChart (E := BaseVector n) (M := Base n) z x =
      liouvilleInChart z x := by
  unfold CotangentGeometry.liouvilleInChart NearbyLagrangian.liouvilleInChart
  rw [cotangentModel_eq]
  apply congrArg (fun p : (TangentSpace (cotangentModel n)
      ((extChartAt (cotangentModel n) z).symm x)) →L[ℝ] ℝ => p.comp _)
  apply ContinuousLinearMap.ext
  intro v
  exact realization_liouville _ _

lemma realization_symplectic {n : ℕ}
    (z : Cotangent n) (u v : TangentSpace (cotangentModel n) z) :
    CotangentGeometry.symplecticForm (E := BaseVector n) (M := Base n) z u v =
      symplecticForm z u v := by
  have he : CotangentGeometry.liouvilleInChart (E := BaseVector n) (M := Base n) z =
      liouvilleInChart z := funext (realization_liouvilleInChart z)
  unfold CotangentGeometry.symplecticForm NearbyLagrangian.symplecticForm
  rw [cotangentModel_eq, he]
  rfl

lemma realization_primitive_bridge {n : ℕ} {i : Base n → Cotangent n}
    {g : Base n → ℝ}
    (h : ∀ q (v : TangentSpace ((𝓡 9).prod (𝓡 n)) q),
      CotangentGeometry.liouville (E := BaseVector n) (M := Base n) (i q)
        (mfderiv ((𝓡 9).prod (𝓡 n))
          (CotangentGeometry.cotangentModel (E := BaseVector n)) i q v) =
        mfderiv ((𝓡 9).prod (𝓡 n)) 𝓘(ℝ, ℝ) g q v) :
    ∀ q (v : TangentSpace (baseModel n) q),
      liouville (i q) (mfderiv (baseModel n) (cotangentModel n) i q v) =
        mfderiv (baseModel n) 𝓘(ℝ, ℝ) g q v := by
  intro q v
  rw [← realization_liouville]
  exact h q v

lemma closedExact_realization_of_bounds {n : ℕ}
    {f : Sphere 9 → RegularHomogeneous (Euclidean (n+1))} {R : Sphere 9 → ℝ}
    {T c C : ℝ} (hfs : SmoothFamily (E := Euclidean 9) f)
    (hRs : ContMDiff (𝓡 9) 𝓘(ℝ, ℝ) ∞ R) (hT₁ : 1 < T) (hc : 0 < c)
    (hR : ∀ b, 0 < R b) (hCR : ∀ b, C < R b)
    (hcap₁ : ∀ b, R b / c < T) (hcap₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun z => smoothCore (fun x : Sphere 9 × Euclidean (n+1) => f x.1 x.2)
        (b, z)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (hinj : Function.Injective (realization f R T)) :
    IsClosedExactLagrangian (realization f R T) := by
  have hs := contMDiff_sourceGeneratingMap (n := n) hfs hRs (zero_lt_one.trans hT₁)
  have hD := sourceGeneratingMap_mfderiv_injective (n := n) hfs hRs hT₁ hc hR hCR
    hcap₁ hcap₂ hsmall hlower hupper
  let : ContinuousSMul ℝ (BaseVector n) := Prod.continuousSMul
  let : T2Space (BaseVector n →L[ℝ] ℝ) := ContinuousLinearMap.instT2Space
  let : T2Space (Cotangent n) := CotangentGeometry.bundleTotalSpace_t2Space
  have hemb : Manifold.IsSmoothEmbedding (baseModel n) (cotangentModel n) ∞
      (realization f R T) := by
    simp only [baseModel, cotangentModel, ← modelWithCornersSelf_prod] at hs hD ⊢
    exact LocalGeometry.isSmoothEmbedding_of_compact_injective_mfderiv hs hinj hD
  refine ⟨hemb, ?_, ?_, ?_⟩
  · exact isCompact_range_sourceGeneratingMap (n := n) hfs hRs (zero_lt_one.trans hT₁)
  · intro q u v
    rw [← realization_symplectic, cotangentModel_eq]
    exact sourceGeneratingMap_isotropic (n := n) hfs hRs hT₁ hc hR hCR
      hcap₁ hcap₂ hsmall hlower hupper q u v
  · refine ⟨sourceFamily f R T ∘ familyCriticalParam f R, ?_, ?_⟩
    · exact (contMDiff_sourceFamily (n := n) hfs hRs (zero_lt_one.trans hT₁)).comp
        (contMDiff_familyCriticalParam hfs hRs)
    · apply realization_primitive_bridge
      exact sourceGeneratingMap_primitive (n := n) hfs hRs hT₁ hc hR hCR
        hcap₁ hcap₂ hsmall hlower hupper

theorem exists_closedExact_realization {n : ℕ}
    {f : Sphere 9 → RegularHomogeneous (Euclidean (n+1))}
    (hf : Continuous f) (hfs : SmoothFamily (E := Euclidean 9) f)
    {e : Euclidean 10} (he : ‖e‖ = 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hcap : ∀ b, a < |SphereDirection.height e b| → Function.Injective (gradient (f b))) :
    ∃ K Λ T : ℝ, 0 < K ∧ 0 < Λ ∧ 1 < T ∧
      IsClosedExactLagrangian
        (realization f (exponentialScale (SphereDirection.height e) K Λ) T) := by
  let θ : Sphere 9 → ℝ := SphereDirection.height e
  obtain ⟨c, C, hc, hC, hgrad⟩ := uniform_gradient_bounds hf
  obtain ⟨M, hM, hcore⟩ := exists_core_bound (contMDiff_smoothCore hfs)
  have hhomo : ∀ b (r : ℝ), 0 < r → ∀ w, f b (r • w) = r ^ 2 * f b w :=
    fun b r hr w => (f b).homogeneity r hr w
  obtain ⟨C₁, hC₁, hmixed⟩ := HeightSeparation.exists_momentum_scale_bound
    (n := 9) he (fun b => (f b).map_zero) hhomo hfs
  have hδ : 0 < 1 - a ^ 2 := by nlinarith
  obtain ⟨K, Λ, T, bmin, bmax, hK, hΛ, hchoice, hmin, hmax, hT⟩ :=
    exists_source_scales (θ := θ) (HeightSeparation.contMDiff_height (n := 9) e).continuous
      (c := c) (C := C) (C₁ := C₁) (M := M) (δ := 1-a^2) (D := cutoffControl beta)
      hc hC.le hC₁ hM hδ
  let R := exponentialScale θ K Λ
  have hR : ∀ b, 0 < R b := fun b => exponentialScale_pos hΛ b
  have hRs : ContMDiff (𝓡 9) 𝓘(ℝ, ℝ) ∞ R :=
    contMDiff_exponentialScale K Λ (HeightSeparation.contMDiff_height (n := 9) e)
  have hCR : ∀ b, C < R b := fun b =>
    (le_max_left C M).trans_lt (hmin.trans_le (hmax b).1)
  have hMR : ∀ b, M < R b := fun b =>
    (le_max_right C M).trans_lt (hmin.trans_le (hmax b).1)
  have hT₁ : 1 < T := (le_max_left _ _).trans_lt hT
  have hcap₁ : ∀ b, R b / c < T := by
    intro b
    exact (div_le_div_of_nonneg_right (hmax b).2 hc.le).trans_lt
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hT)
  have hcap₂ : ∀ b, cutoffControl beta * R b / c < T := by
    intro b
    have hD : 0 ≤ cutoffControl beta := zero_le_one.trans one_le_beta_control
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmax b).2 hD) hc.le).trans_lt
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT)
  have hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun z => smoothCore (fun x : Sphere 9 × Euclidean (n+1) => f x.1 x.2)
        (b, z)) w‖ < R b :=
    fun b w hw => (hcore b w hw).trans_lt (hMR b)
  have hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖ := fun b w => (hgrad b w).1
  have hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖ := fun b w => (hgrad b w).2
  have hinj : Function.Injective (realization f R T) := by
    apply sourceGeneratingMap_injective hfs hRs (zero_lt_one.trans hT₁) hc hR hCR
      hcap₁ hlower hupper
    intro b
    by_cases hb : a < |θ b|
    · exact Or.inl (hcap b hb)
    · right
      obtain ⟨hbder, hbderbound, hbdom⟩ :=
        hmixed a c K Λ ha ha1 hK hΛ hchoice b (le_of_not_gt hb)
      exact ⟨SphereDirection.tangent (n := 9) e b, C₁, hC₁, hbder, hbderbound, hbdom⟩
  exact ⟨K, Λ, T, hK, hΛ, hT₁,
    closedExact_realization_of_bounds hfs hRs hT₁ hc hR hCR hcap₁ hcap₂ hsmall
      hlower hupper hinj⟩

end NearbyLagrangian.EmbeddedRealization

end

end OAI
