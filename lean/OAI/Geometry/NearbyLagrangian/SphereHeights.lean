import Mathlib
import OAI.Geometry.NearbyLagrangian.Stabilization
import OAI.Geometry.NearbyLagrangian.Radialization
import OAI.Geometry.NearbyLagrangian.SmoothCore
import OAI.Geometry.NearbyLagrangian.MomentumSeparation

namespace OAI

/-! Sphere height derivatives and uniform scale separation estimates. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.SphereDirection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

def height (e : V) (b : Metric.sphere (0 : V) 1) : ℝ := ⟪e, (b : V)⟫_ℝ

def direction (e : V) (b : Metric.sphere (0 : V) 1) : V := e - height e b • (b : V)

lemma inner_direction (e : V) (b : Metric.sphere (0 : V) 1) :
    ⟪(b : V), direction e b⟫_ℝ = 0 := by
  rw [direction, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_eq_of_mem_sphere b]
  simp [height, real_inner_comm]

def line (e : V) (p : ℝ × Metric.sphere (0 : V) 1) : V :=
  (p.2 : V) + p.1 • direction e p.2

lemma line_ne_zero (e : V) (p : ℝ × Metric.sphere (0 : V) 1) : line e p ≠ 0 := by
  have hi : ⟪(p.2 : V), line e p⟫_ℝ = 1 := by
    rw [line, inner_add_right, inner_smul_right, inner_direction,
      real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p.2]
    norm_num
  intro h
  rw [h, inner_zero_right] at hi
  norm_num at hi

def curve (e : V) (p : ℝ × Metric.sphere (0 : V) 1) : Metric.sphere (0 : V) 1 :=
  ⟨‖line e p‖⁻¹ • line e p, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (line_ne_zero e p))]⟩

@[simp] lemma curve_zero (e : V) (b : Metric.sphere (0 : V) 1) : curve e (0, b) = b := by
  apply Subtype.ext
  simp [curve, line]

theorem contMDiff_curve (e : V) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (curve e) := by
  have hb : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, V) ∞
      (fun p : ℝ × Metric.sphere (0 : V) 1 => (p.2 : V)) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  have hh : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × Metric.sphere (0 : V) 1 => height e p.2) :=
    (innerSL ℝ e).contMDiff.comp hb
  have hl : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, V) ∞ (line e) :=
    hb.add (contMDiff_fst.smul (contMDiff_const.sub (hh.smul hb)))
  have hn : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p => ‖line e p‖) := by
    intro p
    exact ContDiffAt.comp_contMDiffAt (f := line e) (g := norm)
      (contDiffAt_id.norm ℝ (line_ne_zero e p)) (hl p)
  exact ((hn.inv₀ (fun p => norm_ne_zero_iff.mpr (line_ne_zero e p))).smul hl).codRestrict_sphere _

theorem hasDerivAt_curve (e : V) (b : Metric.sphere (0 : V) 1) :
    HasDerivAt (fun t : ℝ => (curve e (t, b) : V)) (direction e b) 0 := by
  have hl : HasDerivAt (fun t : ℝ => line e (t, b)) (direction e b) 0 := by
    change HasDerivAt (fun t : ℝ => (b : V) + t • direction e b) (direction e b) 0
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (direction e b)).const_add (b : V)
  have hn : HasDerivAt (fun t : ℝ => ‖line e (t, b)‖) 0 0 := by
    have hsq := hl.norm_sq
    simp only [line, zero_smul, add_zero, inner_direction, mul_zero] at hsq
    have hs := hsq.sqrt (by simp)
    simpa only [Real.sqrt_sq (norm_nonneg _), zero_div, line] using hs
  have hi := hn.inv (by simp [line])
  convert! hi.smul hl using 1
  simp [line]

theorem hasDerivAt_height_curve {e : V} (he : ‖e‖ = 1)
    (b : Metric.sphere (0 : V) 1) :
    HasDerivAt (fun t : ℝ => height e (curve e (t, b))) (1 - (height e b) ^ 2) 0 := by
  have h := (innerSL ℝ e).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_curve e b)
  convert! h using 1
  change 1 - (height e b) ^ 2 = ⟪e, direction e b⟫_ℝ
  rw [direction, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he]
  simp [height, pow_two]

def tangent (e : V) (b : Metric.sphere (0 : V) 1) : EuclideanSpace ℝ (Fin n) :=
  (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun t : ℝ => curve e (t, b)) 0) 1

theorem deriv_curve_eq (e : V) {f : Metric.sphere (0 : V) 1 → ℝ}
    {b : Metric.sphere (0 : V) 1}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f b) :
    deriv (fun t : ℝ => f (curve e (t, b))) 0 =
      (show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f b)
        (tangent (n := n) e b) := by
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun t : ℝ => curve e (t, b)) 0 :=
    ((contMDiff_curve e _).comp _ (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      (by simp)
  have he := mfderiv_comp_apply_of_eq (x := (0 : ℝ)) hf hc (curve_zero e b) 1
  rw [mfderiv_eq_fderiv] at he
  exact he

end NearbyLagrangian.SphereDirection

namespace NearbyLagrangian.ScalarMixed

open scoped Manifold ContDiff InnerProductSpace Topology
open Set

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

local instance : ChartedSpace (EuclideanSpace ℝ (Fin n) × W)
    (Metric.sphere (0 : V) 1 × W) :=
  inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) W)
    (Metric.sphere (0 : V) 1 × W))

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × W) ∞
    (Metric.sphere (0 : V) 1 × W) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 n) (I' := 𝓘(ℝ, W)) (Metric.sphere (0 : V) 1) W

def momentum (e : V) (g : Metric.sphere (0 : V) 1 → W → ℝ)
    (b : Metric.sphere (0 : V) 1) (w : W) : ℝ :=
  deriv (fun t : ℝ => g (SphereDirection.curve e (t, b)) w) 0

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in

theorem momentum_eq_baseDerivative (e : V)
    {g : Metric.sphere (0 : V) 1 → W → ℝ} (b : Metric.sphere (0 : V) 1) (w : W)
    (hg : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun q => g q w) b) :
    momentum e g b w =
      MixedDerivative.baseDerivative (E := EuclideanSpace ℝ (Fin n)) g b w
        (SphereDirection.tangent (n := n) e b) :=
  SphereDirection.deriv_curve_eq e hg

theorem contMDiffAt_momentum (e : V) {g : Metric.sphere (0 : V) 1 → W → ℝ}
    (hg : ∀ p : Metric.sphere (0 : V) 1 × W, p.2 ≠ 0 →
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry g) p)
    {p : Metric.sphere (0 : V) 1 × W} (hp : p.2 ≠ 0) :
    ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (fun q => momentum e g q.1 q.2) p := by
  let F : (Metric.sphere (0 : V) 1 × W) → ℝ → ℝ :=
    fun q t => g (SphereDirection.curve e (t, q.1)) q.2
  have hh : ContMDiffAt (((𝓡 n).prod 𝓘(ℝ, W)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry F) (p, 0) := by
    have hmap : ContMDiffAt (((𝓡 n).prod 𝓘(ℝ, W)).prod 𝓘(ℝ, ℝ))
        ((𝓡 n).prod 𝓘(ℝ, W)) ∞
        (fun q : (Metric.sphere (0 : V) 1 × W) × ℝ =>
          (SphereDirection.curve e (q.2, q.1.1), q.1.2)) (p, 0) :=
      ((SphereDirection.contMDiff_curve e _).comp _
        (contMDiffAt_snd.prodMk (contMDiffAt_fst.comp _ contMDiffAt_fst))).prodMk
          (contMDiffAt_snd.comp _ contMDiffAt_fst)
    exact (hg (SphereDirection.curve e (0, p.1), p.2) hp).comp (p, 0) hmap
  rw [← modelWithCornersSelf_prod] at hh ⊢
  exact MixedDerivative.contMDiffAt_param_deriv hh

theorem exists_uniform_mixed_bound [ProperSpace V] [ProperSpace W]
    (e : V) {g : Metric.sphere (0 : V) 1 → W → ℝ}
    (hzero : ∀ b, g b 0 = 0)
    (hhom : ∀ b (r : ℝ), 0 < r → ∀ w, g b (r • w) = r ^ 2 * g b w)
    (hg : ∀ p : Metric.sphere (0 : V) 1 × W, p.2 ≠ 0 →
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry g) p) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ b, Differentiable ℝ (momentum e g b) ∧
      ∀ w, ‖fderiv ℝ (momentum e g b) w‖ ≤ C₁ * ‖w‖ := by
  have hPzero : ∀ b, momentum e g b 0 = 0 := by
    intro b
    simp [momentum, hzero]
  have hPhom : ∀ b (r : ℝ), 0 < r → ∀ w,
      momentum e g b (r • w) = r ^ 2 • momentum e g b w := by
    intro b r hr w
    unfold momentum
    simp_rw [hhom _ r hr]
    exact deriv_const_mul_field _
  have hdiff : ∀ b w, w ≠ 0 → DifferentiableAt ℝ (momentum e g b) w := by
    intro b w hw
    exact ((contMDiffAt_momentum e hg hw).comp w
      (contMDiffAt_const.prodMk contMDiffAt_id)).contDiffAt.differentiableAt (by simp)
  have hD : Continuous (fun p : Metric.sphere (0 : V) 1 × Metric.sphere (0 : W) 1 =>
      fderiv ℝ (momentum e g p.1) (p.2 : W)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : (p.2 : W) ≠ 0 := by
      exact norm_ne_zero_iff.mp (by rw [norm_eq_of_mem_sphere p.2]; norm_num)
    have hh := MixedDerivative.contMDiffAt_param_fderiv
      (E := EuclideanSpace ℝ (Fin n)) (B := Metric.sphere (0 : V) 1)
      (g := momentum e g) (p := (p.1, (p.2 : W)))
      (contMDiffAt_momentum e hg hp)
    exact hh.continuousAt.comp
      (f := fun q : Metric.sphere (0 : V) 1 × Metric.sphere (0 : W) 1 =>
        (q.1, (q.2 : W)))
      ((continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt)
  exact MixedRadial.exists_uniform_derivative_bound hPzero hPhom hdiff hD

end NearbyLagrangian.ScalarMixed

namespace NearbyLagrangian.HeightSeparation

open scoped Manifold ContDiff InnerProductSpace Topology

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

lemma contMDiff_height (e : V) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (SphereDirection.height e) :=
  (innerSL ℝ e).contMDiff.comp contMDiff_coe_sphere

def scaleDerivative (R : Metric.sphere (0 : V) 1 → ℝ)
    (b : Metric.sphere (0 : V) 1) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  mfderiv (𝓡 n) 𝓘(ℝ, ℝ) R b

lemma scaleDerivative_height {e : V} (he : ‖e‖ = 1) (K Λ : ℝ)
    (b : Metric.sphere (0 : V) 1) :
    scaleDerivative (n := n) (Scales.exponentialScale (SphereDirection.height e) K Λ) b
      (SphereDirection.tangent (n := n) e b) =
      K * Scales.exponentialScale (SphereDirection.height e) K Λ b *
        (1 - (SphereDirection.height e b) ^ 2) := by
  have hh := (contMDiff_height (n := n) e b).mdifferentiableAt (by simp)
  have ht := (SphereDirection.deriv_curve_eq e hh).symm.trans
    (SphereDirection.hasDerivAt_height_curve he b).deriv
  unfold scaleDerivative
  rw [Scales.mfderiv_exponentialScale K Λ hh]
  change (K * Scales.exponentialScale (SphereDirection.height e) K Λ b) *
      (show EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (SphereDirection.height e) b)
          (SphereDirection.tangent (n := n) e b) = _
  rw [ht]

lemma height_direction_lower {e : V} {b : Metric.sphere (0 : V) 1}
    {a : ℝ} (ha : 0 ≤ a) (hb : |SphereDirection.height e b| ≤ a) :
    1 - a ^ 2 ≤ 1 - (SphereDirection.height e b) ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg (SphereDirection.height e b)) ha).2 hb
  rw [sq_abs] at h
  nlinarith

theorem exists_momentum_scale_bound [ProperSpace V] [ProperSpace W]
    {e : V} (he : ‖e‖ = 1) {g : Metric.sphere (0 : V) 1 → W → ℝ}
    (hzero : ∀ b, g b 0 = 0)
    (hhom : ∀ b (r : ℝ), 0 < r → ∀ w, g b (r • w) = r ^ 2 * g b w)
    (hg : ∀ p : Metric.sphere (0 : V) 1 × W, p.2 ≠ 0 →
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞ (Function.uncurry g) p) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (a c K Λ : ℝ), 0 ≤ a → a < 1 →
      0 < K → 0 < Λ → C₁ / c < K * (1 - a ^ 2) →
      ∀ b, |SphereDirection.height e b| ≤ a →
        Differentiable ℝ (fun w => MixedDerivative.baseDerivative
          (E := EuclideanSpace ℝ (Fin n)) g b w (SphereDirection.tangent (n := n) e b)) ∧
        (∀ w, ‖fderiv ℝ (fun z => MixedDerivative.baseDerivative
          (E := EuclideanSpace ℝ (Fin n)) g b z (SphereDirection.tangent (n := n) e b)) w‖
          ≤ C₁ * ‖w‖) ∧
        C₁ * (Scales.exponentialScale (SphereDirection.height e) K Λ b / c) <
          |scaleDerivative (n := n)
            (Scales.exponentialScale (SphereDirection.height e) K Λ) b
              (SphereDirection.tangent (n := n) e b)| := by
  obtain ⟨C₁, hC₁, hbound⟩ := ScalarMixed.exists_uniform_mixed_bound (n := n) e hzero hhom hg
  have heq : ∀ b, ScalarMixed.momentum e g b =
      (fun w => MixedDerivative.baseDerivative (E := EuclideanSpace ℝ (Fin n)) g b w
        (SphereDirection.tangent (n := n) e b)) := by
    intro b
    funext w
    apply ScalarMixed.momentum_eq_baseDerivative
    by_cases hw : w = 0
    · subst w
      have hh : (fun q => g q 0) = fun _ => 0 := funext hzero
      rw [hh]
      exact mdifferentiableAt_const
    · exact ((hg (b, w) hw).comp b (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        (by simp)
  refine ⟨C₁, hC₁, ?_⟩
  intro a c K Λ ha ha1 hK hΛ hchoice b hb
  refine ⟨?_, ?_, ?_⟩
  · rw [← heq b]
    exact (hbound b).1
  · rw [← heq b]
    exact (hbound b).2
  · rw [scaleDerivative_height he]
    have hδ : 0 < 1 - a ^ 2 := by nlinarith
    have hθ := height_direction_lower ha hb
    simpa only [Real.norm_eq_abs, smul_eq_mul] using
      (BranchSeparation.exponential_differential_dominates hK
        (Scales.exponentialScale_pos hΛ b) hchoice
        (dθ := (1 - (SphereDirection.height e b) ^ 2 : ℝ))
        (by rw [Real.norm_eq_abs, abs_of_pos (hδ.trans_le hθ)]; exact hθ))

end NearbyLagrangian.HeightSeparation

namespace NearbyLagrangian.Tubes

open scoped InnerProductSpace
open RegularHomogeneous

lemma standardForm_fderiv_apply (k l : ℕ) (w z : Euclidean (k+l)) :
    fderiv ℝ (standardForm k l) w z =
      -2 * ⟪(EuclideanSpace.finAddEquivProd w).1,
        (EuclideanSpace.finAddEquivProd z).1⟫_ℝ +
      2 * ⟪(EuclideanSpace.finAddEquivProd w).2,
        (EuclideanSpace.finAddEquivProd z).2⟫_ℝ := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := l)
  let ex : Euclidean (k+l) →L[ℝ] Euclidean k :=
    (ContinuousLinearMap.fst ℝ (Euclidean k) (Euclidean l)).comp e.toContinuousLinearMap
  let ey : Euclidean (k+l) →L[ℝ] Euclidean l :=
    (ContinuousLinearMap.snd ℝ (Euclidean k) (Euclidean l)).comp e.toContinuousLinearMap
  have hx := (hasStrictFDerivAt_norm_sq (ex w)).hasFDerivAt.comp w ex.hasFDerivAt
  have hy := (hasStrictFDerivAt_norm_sq (ey w)).hasFDerivAt.comp w ey.hasFDerivAt
  have hd := hx.neg.add hy
  change HasFDerivAt (standardForm k l) _ w at hd
  rw [hd.fderiv]
  simp only [add_apply, neg_apply,
    ContinuousLinearMap.comp_apply, two_smul, innerSL_apply_apply]
  change -(⟪(e w).1, (e z).1⟫_ℝ + ⟪(e w).1, (e z).1⟫_ℝ) +
    (⟪(e w).2, (e z).2⟫_ℝ + ⟪(e w).2, (e z).2⟫_ℝ) = _
  dsimp [e]
  ring

theorem standardForm_gradient_injective (k l : ℕ) :
    Function.Injective (gradient (standardForm k l)) := by
  intro w w' h
  have hd : fderiv ℝ (standardForm k l) w = fderiv ℝ (standardForm k l) w' := by
    rw [← toDual_gradient, ← toDual_gradient, h]
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := l)
  apply e.injective
  apply Prod.ext
  · apply ext_inner_right ℝ
    intro z
    have hh := congrArg (fun A : Euclidean (k+l) →L[ℝ] ℝ => A (e.symm (z, 0))) hd
    rw [standardForm_fderiv_apply, standardForm_fderiv_apply] at hh
    change -2 * ⟪(e w).1, (e (e.symm (z, 0))).1⟫_ℝ +
      2 * ⟪(e w).2, (e (e.symm (z, 0))).2⟫_ℝ =
      -2 * ⟪(e w').1, (e (e.symm (z, 0))).1⟫_ℝ +
      2 * ⟪(e w').2, (e (e.symm (z, 0))).2⟫_ℝ at hh
    simp only [e.apply_symm_apply, inner_zero_right, mul_zero, add_zero] at hh
    linarith
  · apply ext_inner_right ℝ
    intro z
    have hh := congrArg (fun A : Euclidean (k+l) →L[ℝ] ℝ => A (e.symm (0, z))) hd
    rw [standardForm_fderiv_apply, standardForm_fderiv_apply] at hh
    change -2 * ⟪(e w).1, (e (e.symm (0, z))).1⟫_ℝ +
      2 * ⟪(e w).2, (e (e.symm (0, z))).2⟫_ℝ =
      -2 * ⟪(e w').1, (e (e.symm (0, z))).1⟫_ℝ +
      2 * ⟪(e w').2, (e (e.symm (0, z))).2⟫_ℝ at hh
    simp only [e.apply_symm_apply, inner_zero_right, mul_zero, zero_add] at hh
    linarith

end NearbyLagrangian.Tubes

end

end OAI
