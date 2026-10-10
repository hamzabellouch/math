import Mathlib
import OAI.Geometry.NearbyLagrangian.SmoothFamilies
import OAI.Geometry.NearbyLagrangian.CotangentForms
import OAI.Geometry.NearbyLagrangian.SmoothCore

namespace OAI

/-! Smooth coupled generating families, their primitives and compact images. -/

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

def sourceFamily (f : B → RegularHomogeneous W) (R : B → ℝ) (T : ℝ)
    (p : (B × Metric.sphere (0 : W) 1) × W) : ℝ :=
  Cutoff.family (fun w => smoothCore (fun x : B × W => f x.1 x.2) (p.1.1, w))
    beta T (R p.1.1) p.1.2 p.2

omit [IsManifold 𝓘(ℝ, E) ∞ B] in

theorem contMDiff_sourceFamily {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T : ℝ} (hT : 0 < T) :
    ContMDiff ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (sourceFamily f R T) := by
  have hcore := contMDiff_smoothCore hf
  have h₁ : ContMDiff ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W))
      (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞
      (fun p : (B × Metric.sphere (0 : W) 1) × W => (p.1.1, p.2)) :=
    (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
  have h₂ : ContMDiff ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W))
      𝓘(ℝ, W × W) ∞
      (fun p : (B × Metric.sphere (0 : W) 1) × W => ((p.1.2 : W), p.2)) := by
    have hv : ContMDiff ((𝓘(ℝ, E).prod (𝓡 n)).prod 𝓘(ℝ, W)) (𝓡 n) ∞
        (fun p : (B × Metric.sphere (0 : W) 1) × W => p.1.2) :=
      contMDiff_snd.comp contMDiff_fst
    exact ((show ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞
      ((↑) : Metric.sphere (0 : W) 1 → W) from contMDiff_coe_sphere).comp hv).prodMk_space contMDiff_snd
  exact (hcore.comp h₁).sub ((hR.comp (contMDiff_fst.comp contMDiff_fst)).mul
    ((contDiff_cutoffLinear_joint hT contDiff_beta (fun _ hs => beta_eq_one hs)).comp_contMDiff h₂))

omit [FiniteDimensional ℝ W] [IsManifold 𝓘(ℝ, E) ∞ B] in
lemma norm_gradient_eq_norm_fderiv [CompleteSpace W] (g : W → ℝ) (w : W) :
    ‖gradient g w‖ = ‖fderiv ℝ g w‖ := by
  exact (InnerProductSpace.toDual ℝ W).symm.norm_map _

omit [IsManifold 𝓘(ℝ, E) ∞ B] in
lemma gradient_eq_smul_iff (g : W → ℝ) (w v : W) (R : ℝ) :
    gradient g w = R • v ↔ fderiv ℝ g w = R • innerSL ℝ v := by
  have hd : (InnerProductSpace.toDual ℝ W) (R • v) = R • innerSL ℝ v := by
    ext a
    simp
  constructor
  · intro h
    rw [← toDual_gradient, h, hd]
  · intro h
    apply (InnerProductSpace.toDual ℝ W).injective
    rw [toDual_gradient, hd, h]

omit [IsManifold 𝓘(ℝ, E) ∞ B] in

theorem sourceFamily_critical_iff {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ} {T c C : ℝ}
    (hT : 1 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale₁ : ∀ b, R b / c < T)
    (hscale₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => smoothCore (fun x : B × W => f x.1 x.2) (b, a)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (b : B) (v : Metric.sphere (0 : W) 1) (w : W) :
    fderiv ℝ (fun a => sourceFamily f R T ((b, v), a)) w = 0 ↔
      gradient (f b) w = R b • (v : W) := by
  have : Nontrivial W := nontrivial_of_ne (v : W) 0 (ne_zero_of_mem_unit_sphere v)
  have hG : Differentiable ℝ (fun a => smoothCore (fun x : B × W => f x.1 x.2) (b, a)) := by
    have hi : ContMDiff 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, W)) ∞
        (fun a : W => (b, a)) := contMDiff_const.prodMk contMDiff_id
    have h := (contMDiff_smoothCore hf).comp hi
    exact (contMDiff_iff_contDiff.mp h).differentiable (by simp)
  rw [gradient_eq_smul_iff]
  exact Cutoff.critical_iff hT (hR b) hc (hC b) (hscale₁ b) (hscale₂ b)
    (contDiff_beta.differentiable (by simp)) (fun _ hs => beta_eq_one hs)
    (fun _ hs => beta_le_control hs) (norm_eq_of_mem_sphere v) hG
    (fun _ hw => smoothCore_eq hw) (hsmall b)
    (fun a => by simpa only [norm_gradient_eq_norm_fderiv] using hlower b a)
    (fun a => by simpa only [norm_gradient_eq_norm_fderiv] using hupper b a)

omit [TopologicalSpace B] in

theorem sourceFamily_eq_outside {f : B → RegularHomogeneous W} {R : B → ℝ}
    {T : ℝ} (hT : 1 < T) (b : B) (v : Metric.sphere (0 : W) 1) (w : W)
    (hw : 2 * T ≤ ‖w‖) : sourceFamily f R T ((b, v), w) = f b w :=
  Cutoff.family_eq_outside hT (fun _ hs => beta_eq_zero hs)
    (fun _ hs => smoothCore_eq hs) hw

omit [IsManifold 𝓘(ℝ, E) ∞ B] in

theorem radialSolution_sourceFamily_critical {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ} {T c C : ℝ}
    (hT : 1 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale₁ : ∀ b, R b / c < T)
    (hscale₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => smoothCore (fun x : B × W => f x.1 x.2) (b, a)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (p : B × Metric.sphere (0 : W) 1) :
    fderiv ℝ (fun a => sourceFamily f R T ((p.1, (f p.1).direction p.2), a))
      ((f p.1).radialSolution (R p.1) p.2) = 0 :=
  (sourceFamily_critical_iff hf hT hc hR hC hscale₁ hscale₂ hsmall hlower hupper
    p.1 ((f p.1).direction p.2) _).mpr ((f p.1).radialSolution_critical _ (hR _) p.2)

local instance : ChartedSpace (E × EuclideanSpace ℝ (Fin n))
    (B × Metric.sphere (0 : W) 1) :=
  inferInstanceAs (ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin n)))
    (B × Metric.sphere (0 : W) 1))

local instance : IsManifold 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) ∞
    (B × Metric.sphere (0 : W) 1) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, E)) (I' := 𝓡 n) B (Metric.sphere (0 : W) 1)

def sourceGeneratingMap (f : B → RegularHomogeneous W) (R : B → ℝ) (T : ℝ) :
    (B × Metric.sphere (0 : W) 1) →
      CotangentGeometry.Cotangent (E := E × EuclideanSpace ℝ (Fin n))
        (M := B × Metric.sphere (0 : W) 1) :=
  CotangentGeometry.generatingMap (sourceFamily f R T)
    (fun p => (p.1, (f p.1).direction p.2))
    (fun p => (f p.1).radialSolution (R p.1) p.2)

theorem contMDiff_sourceGeneratingMap {f : B → RegularHomogeneous W}
    (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T : ℝ} (hT : 0 < T) :
    ContMDiff (𝓘(ℝ, E).prod (𝓡 n))
      (CotangentGeometry.cotangentModel (E := E × EuclideanSpace ℝ (Fin n))) ∞
      (sourceGeneratingMap (E := E) (n := n) f R T) := by
  have hG := contMDiff_sourceFamily (n := n) hf hR hT
  have hq : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod (𝓡 n)) ∞
      (fun p : B × Metric.sphere (0 : W) 1 => (p.1, (f p.1).direction p.2)) :=
    contMDiff_fst.prodMk (contMDiff_family_direction (n := n) hf)
  have hw := contMDiff_family_radialSolution (n := n) hf hR
  rw [← modelWithCornersSelf_prod] at hG hq hw ⊢
  intro x
  exact CotangentGeometry.contMDiffAt_generatingMap (hG _) (hq _) (hw _)

theorem sourceGeneratingMap_primitive {f : B → RegularHomogeneous W}
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
    (v : TangentSpace (𝓘(ℝ, E).prod (𝓡 n)) x) :
    CotangentGeometry.liouville (sourceGeneratingMap (E := E) (n := n) f R T x)
      (mfderiv (𝓘(ℝ, E).prod (𝓡 n))
        (CotangentGeometry.cotangentModel (E := E × EuclideanSpace ℝ (Fin n)))
        (sourceGeneratingMap (E := E) (n := n) f R T) x v) =
      mfderiv (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, ℝ)
        (sourceFamily f R T ∘ familyCriticalParam f R) x v := by
  have hG := contMDiff_sourceFamily (n := n) hf hRs (zero_lt_one.trans hT)
  have hq : ContMDiff (𝓘(ℝ, E).prod (𝓡 n)) (𝓘(ℝ, E).prod (𝓡 n)) ∞
      (fun p : B × Metric.sphere (0 : W) 1 => (p.1, (f p.1).direction p.2)) :=
    contMDiff_fst.prodMk (contMDiff_family_direction (n := n) hf)
  have hw := contMDiff_family_radialSolution (n := n) hf hRs
  have hcrit := radialSolution_sourceFamily_critical hf hT hc hR hC
    hscale₁ hscale₂ hsmall hlower hupper x
  rw [← modelWithCornersSelf_prod] at hG hq hw
  have h := CotangentGeometry.generatingMap_primitive (hG _) (hq _) (hw _) hcrit v
  convert! h using 1

theorem isCompact_range_sourceGeneratingMap [CompactSpace B]
    {f : B → RegularHomogeneous W} (hf : SmoothFamily (E := E) f) {R : B → ℝ}
    (hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ R) {T : ℝ} (hT : 0 < T) :
    IsCompact (Set.range (sourceGeneratingMap (E := E) (n := n) f R T)) :=
  isCompact_range (contMDiff_sourceGeneratingMap (E := E) (n := n) hf hR hT).continuous

end NearbyLagrangian.EmbeddedRealization

end

end OAI
