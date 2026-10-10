import Mathlib
import OAI.Geometry.NearbyLagrangian.GeneratingEmbeddings
import OAI.Geometry.NearbyLagrangian.RealizationFamilies

namespace OAI

/-! Critical annuli, regular vertical equations and isotropic realization. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.EmbeddedRealization

open scoped Manifold ContDiff InnerProductSpace Topology
open Tubes Tubes.RegularHomogeneous CoreSmoothing Cutoff Scales
open Set Filter

variable {W E B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ, E) ∞ B]
  {n : ℕ} [Fact (Module.finrank ℝ W = n + 1)]

omit [TopologicalSpace B] in
lemma sourceFamily_eq_uncut {f : B → RegularHomogeneous W} {R : B → ℝ}
    {T : ℝ} (hT : 0 < T) (b : B) (v : Metric.sphere (0 : W) 1) (w : W)
    (hlow : 1 ≤ ‖w‖) (hupp : ‖w‖ ≤ T) :
    sourceFamily f R T ((b, v), w) = f b w - R b * ⟪(v : W), w⟫_ℝ := by
  have hβ : beta (‖w‖ / T) = 1 := beta_eq_one
    ⟨div_nonneg (norm_nonneg _) hT.le, (div_le_one hT).mpr hupp⟩
  simp only [sourceFamily, Cutoff.family, cutoffLinear, smoothCore_eq (p := (b, w)) hlow, hβ, one_mul]

omit [TopologicalSpace B] in
lemma fderiv_sourceFamily_of_annulus {f : B → RegularHomogeneous W}
    {R : B → ℝ} {T : ℝ} (hT : 0 < T)
    (b : B) (v : Metric.sphere (0 : W) 1) (w : W)
    (hlow : 1 < ‖w‖) (hupp : ‖w‖ < T) :
    fderiv ℝ (fun a => sourceFamily f R T ((b, v), a)) w =
      (InnerProductSpace.toDual ℝ W) (gradient (f b) w - R b • (v : W)) := by
  have he : (fun a => sourceFamily f R T ((b, v), a)) =ᶠ[𝓝 w]
      (fun a => f b a - R b * ⟪(v : W), a⟫_ℝ) := by
    filter_upwards [continuous_norm.continuousAt.eventually (eventually_gt_nhds hlow),
      continuous_norm.continuousAt.eventually (eventually_lt_nhds hupp)] with a ha₁ ha₂
    exact sourceFamily_eq_uncut hT b v a ha₁.le ha₂.le
  rw [he.fderiv_eq]
  have hd : HasFDerivAt (fun a => f b a - R b * ⟪(v : W), a⟫_ℝ)
      (fderiv ℝ (f b) w - R b • innerSL ℝ (v : W)) w :=
    ((f b).differentiable w).hasFDerivAt.sub ((innerSL ℝ (v : W)).hasFDerivAt.const_mul (R b))
  rw [hd.fderiv]
  simp only [map_sub, map_smul, toDual_gradient]
  rfl

omit [TopologicalSpace B] in

lemma sourceFamily_eq_neg_at_critical {f : B → RegularHomogeneous W}
    {R : B → ℝ} {T : ℝ} (hT : 0 < T)
    (b : B) (v : Metric.sphere (0 : W) 1) (w : W)
    (hlow : 1 ≤ ‖w‖) (hupp : ‖w‖ ≤ T)
    (hcrit : gradient (f b) w = R b • (v : W)) :
    sourceFamily f R T ((b, v), w) = -f b w := by
  rw [sourceFamily_eq_uncut hT b v w hlow hupp]
  have he := (f b).euler w
  have hd := (gradient_eq_smul_iff (f b) w (v : W) (R b)).mp hcrit
  rw [hd] at he
  change R b * ⟪(v : W), w⟫_ℝ = 2 * f b w at he
  linarith

omit [TopologicalSpace B] in
lemma critical_annulus {f : B → RegularHomogeneous W} {R : B → ℝ} {T c C : ℝ}
    (hc : 0 < c) (b : B) (hR : 0 < R b) (hC : C < R b) (hscale : R b / c < T)
    (hlower : ∀ w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (v : Metric.sphere (0 : W) 1) (w : W)
    (hcrit : gradient (f b) w = R b • (v : W)) :
    1 < ‖w‖ ∧ ‖w‖ < T := by
  have hn : ‖gradient (f b) w‖ = R b := by
    rw [hcrit, norm_smul, Real.norm_eq_abs, abs_of_pos hR, norm_eq_of_mem_sphere v, mul_one]
  have hl := hlower w
  have hu := hupper w
  rw [hn] at hl hu
  have hCp : 0 < C := by nlinarith [norm_nonneg w]
  constructor
  · by_contra h
    have hw := le_of_not_gt h
    nlinarith
  · exact ((le_div_iff₀ hc).mpr (by nlinarith)).trans_lt hscale

def sourceVertical (f : B → RegularHomogeneous W) (R : B → ℝ) (T : ℝ)
    (p : (B × Metric.sphere (0 : W) 1) × W) : W →L[ℝ] ℝ :=
  fderiv ℝ (fun a => sourceFamily f R T (p.1, a)) p.2

omit [IsManifold 𝓘(ℝ, E) ∞ B] in

theorem sourceVertical_fixed_regular {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ} {T : ℝ} (hT : 0 < T)
    (b : B) (hR : 0 < R b) (p : (f b).CriticalLocus (R b))
    (hlow : 1 < ‖p.val.1‖) (hupp : ‖p.val.1‖ < T) :
    Function.Surjective (mfderiv (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W →L[ℝ] ℝ)
      (fun y : W × Metric.sphere (0 : W) 1 => sourceVertical f R T ((b, y.2), y.1)) p.val) := by
  have he : (fun y : W × Metric.sphere (0 : W) 1 =>
      sourceVertical f R T ((b, y.2), y.1)) =ᶠ[𝓝 p.val]
      (fun y => (InnerProductSpace.toDual ℝ W) ((f b).criticalEquation (R b) y)) := by
    filter_upwards [continuous_fst.norm.continuousAt.eventually (eventually_gt_nhds hlow),
      continuous_fst.norm.continuousAt.eventually (eventually_lt_nhds hupp)] with y hy₁ hy₂
    exact fderiv_sourceFamily_of_annulus hT b y.2 y.1 hy₁ hy₂
  have hw : p.val.1 ≠ 0 := (f b).critical_ne_zero _ hR p
  have hg : ContMDiffAt (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun y : W × Metric.sphere (0 : W) 1 => gradient (f b) y.1) p.val :=
    ContDiffAt.comp_contMDiffAt (f := Prod.fst) (g := gradient (f b))
      ((f b).contDiffAt_gradient (hf.smoothOffZero b) hw) contMDiffAt_fst
  have hv : ContMDiffAt (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W) ∞
      (fun y : W × Metric.sphere (0 : W) 1 => (y.2 : W)) p.val :=
    (contMDiff_coe_sphere (n := n) (m := ∞) p.val.2).comp p.val contMDiffAt_snd
  have hconst : ContMDiffAt (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun _ : W × Metric.sphere (0 : W) 1 => R b) p.val := contMDiffAt_const
  have hEq : MDifferentiableAt (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W)
      ((f b).criticalEquation (R b)) p.val :=
    (hg.sub (hconst.smul hv)).mdifferentiableAt (by simp)
  let A : W →L[ℝ] (W →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ W).toContinuousLinearEquiv.toContinuousLinearMap
  have hd := (A.hasFDerivAt (x := (f b).criticalEquation (R b) p.val)).hasMFDerivAt.comp p.val
    hEq.hasMFDerivAt
  rw [he.mfderiv_eq]
  erw [hd.mfderiv]
  intro z
  obtain ⟨a, ha⟩ := (f b).criticalEquation_regular (n := n) (hf.smoothOffZero b)
    (R b) hR p ((InnerProductSpace.toDual ℝ W).symm z)
  refine ⟨a, ?_⟩
  change (InnerProductSpace.toDual ℝ W)
    (mfderiv (𝓘(ℝ, W).prod (𝓡 n)) 𝓘(ℝ, W) ((f b).criticalEquation (R b)) p.val a) = z
  rw [ha]
  exact (InnerProductSpace.toDual ℝ W).apply_symm_apply z

local instance : ChartedSpace (E × EuclideanSpace ℝ (Fin n))
    (B × Metric.sphere (0 : W) 1) :=
  inferInstanceAs (ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin n)))
    (B × Metric.sphere (0 : W) 1))

local instance : IsManifold 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) ∞
    (B × Metric.sphere (0 : W) 1) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, E)) (I' := 𝓡 n) B (Metric.sphere (0 : W) 1)

lemma contMDiff_sourceVertical {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T : ℝ} (hT : 0 < T) :
    ContMDiff ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) 𝓘(ℝ, W →L[ℝ] ℝ) ∞
      (sourceVertical f R T) := by
  have hG := contMDiff_sourceFamily (n := n) hf hR hT
  rw [← modelWithCornersSelf_prod] at hG ⊢
  exact fun p => CoreSmoothing.contMDiffAt_vertical (hG p)

theorem sourceVertical_regular {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T : ℝ} (hT : 0 < T)
    (b : B) (hR : 0 < R b) (p : (f b).CriticalLocus (R b))
    (hlow : 1 < ‖p.val.1‖) (hupp : ‖p.val.1‖ < T) :
    Function.Surjective (mfderiv ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W))
      𝓘(ℝ, W →L[ℝ] ℝ) (sourceVertical f R T) ((b, p.val.2), p.val.1)) := by
  let j : W × Metric.sphere (0 : W) 1 → (B × Metric.sphere (0 : W) 1) × W :=
    fun y => ((b, y.2), y.1)
  have hj : ContMDiff (𝓘(ℝ, W).prod (𝓡 n)) ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) ∞ j :=
    (contMDiff_const.prodMk contMDiff_snd).prodMk contMDiff_fst
  have hd := mfderiv_comp p.val
    ((contMDiff_sourceVertical hf hRs hT).mdifferentiable (by simp) (j p.val))
    (hj.mdifferentiable (by simp) p.val)
  intro z
  obtain ⟨a, ha⟩ := sourceVertical_fixed_regular (n := n) hf hT b hR p hlow hupp z
  refine ⟨mfderiv (𝓘(ℝ, W).prod (𝓡 n))
    ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) j p.val a, ?_⟩
  have he := congrArg (fun A => A a) hd
  exact he.symm.trans ha

end NearbyLagrangian.EmbeddedRealization

namespace NearbyLagrangian.EmbeddedRealization

open scoped Manifold ContDiff InnerProductSpace Topology
open Tubes Tubes.RegularHomogeneous CoreSmoothing Cutoff Scales
open Set Filter

variable {W E B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ, E) ∞ B]
  {n : ℕ} [Fact (Module.finrank ℝ W = n + 1)]

local instance : ChartedSpace (E × EuclideanSpace ℝ (Fin n))
    (B × Metric.sphere (0 : W) 1) :=
  inferInstanceAs (ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin n)))
    (B × Metric.sphere (0 : W) 1))

local instance : IsManifold 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) ∞
    (B × Metric.sphere (0 : W) 1) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, E)) (I' := 𝓡 n) B (Metric.sphere (0 : W) 1)

theorem sourceGeneratingMap_isotropic {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T c C : ℝ}
    (hT : 1 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale₁ : ∀ b, R b / c < T)
    (hscale₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => smoothCore (fun x : B × W => f x.1 x.2) (b, a)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (x : B × Metric.sphere (0 : W) 1)
    (u v : TangentSpace (𝓘(ℝ, E).prod (𝓡 n)) x) :
    CotangentGeometry.symplecticForm (sourceGeneratingMap (E := E) (n := n) f R T x)
      (mfderiv (𝓘(ℝ, E).prod (𝓡 n))
        (CotangentGeometry.cotangentModel (E := E × EuclideanSpace ℝ (Fin n)))
        (sourceGeneratingMap (E := E) (n := n) f R T) x u)
      (mfderiv (𝓘(ℝ, E).prod (𝓡 n))
        (CotangentGeometry.cotangentModel (E := E × EuclideanSpace ℝ (Fin n)))
        (sourceGeneratingMap (E := E) (n := n) f R T) x v) = 0 := by
  have hG := contMDiff_sourceFamily (n := n) hf hRs (zero_lt_one.trans hT)
  have hq : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod (𝓡 n)) ∞
      (fun p : B × Metric.sphere (0 : W) 1 => (p.1, (f p.1).direction p.2)) :=
    contMDiff_fst.prodMk (contMDiff_family_direction (n := n) hf)
  have hw := contMDiff_family_radialSolution (n := n) hf hRs
  have hcrit := radialSolution_sourceFamily_critical hf hT hc hR hC
    hscale₁ hscale₂ hsmall hlower hupper
  rw [← modelWithCornersSelf_prod] at hG hq hw
  have h := CotangentGeometry.generatingMap_isotropic hG (hq x) (hw x)
    (Filter.Eventually.of_forall hcrit) u v
  convert! h using 1

theorem sourceGeneratingMap_mfderiv_injective {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hRs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T c C : ℝ}
    (hT : 1 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale₁ : ∀ b, R b / c < T)
    (hscale₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => smoothCore (fun x : B × W => f x.1 x.2) (b, a)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (x : B × Metric.sphere (0 : W) 1) :
    Function.Injective (mfderiv (𝓘(ℝ, E).prod (𝓡 n))
      (CotangentGeometry.cotangentModel (E := E × EuclideanSpace ℝ (Fin n)))
      (sourceGeneratingMap (E := E) (n := n) f R T) x) := by
  have hG := contMDiff_sourceFamily (n := n) hf hRs (zero_lt_one.trans hT)
  have hq : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod (𝓡 n)) ∞
      (fun p : B × Metric.sphere (0 : W) 1 => (p.1, (f p.1).direction p.2)) :=
    contMDiff_fst.prodMk (contMDiff_family_direction (n := n) hf)
  have hw := contMDiff_family_radialSolution (n := n) hf hRs
  have hcrit := radialSolution_sourceFamily_critical hf hT hc hR hC
    hscale₁ hscale₂ hsmall hlower hupper
  let p : (f x.1).CriticalLocus (R x.1) :=
    ⟨((f x.1).radialSolution (R x.1) x.2, (f x.1).direction x.2),
      (f x.1).radialSolution_critical _ (hR _) x.2⟩
  have hann := critical_annulus hc x.1 (hR _) (hC _) (hscale₁ _)
    (hlower _) (hupper _) p.val.2 p.val.1 p.property
  have hreg := sourceVertical_regular (n := n) hf hRs (zero_lt_one.trans hT)
    x.1 (hR _) p hann.1 hann.2
  have hjinj := mfderiv_familyCriticalParam_injective (n := n) hf hRs hR x
  rw [← modelWithCornersSelf_prod] at hG hq hw hreg hjinj
  have h := CotangentGeometry.generatingMap_mfderiv_injective hG (hq x) (hw x)
    (Filter.Eventually.of_forall hcrit) hreg hjinj
  convert! h using 1

end NearbyLagrangian.EmbeddedRealization

end

end OAI
