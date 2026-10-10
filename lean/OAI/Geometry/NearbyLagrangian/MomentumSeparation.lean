import Mathlib

namespace OAI

/-! Separation of branches by sphere and base momenta. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.BranchSeparation

variable {W Z : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem sub_mem_radial_of_sphere_momenta [FiniteDimensional ℝ W] {n : ℕ}
    [Fact (Module.finrank ℝ W = n + 1)] (v : Metric.sphere (0 : W) 1)
    {w w' : W}
    (heq : ∀ a : TangentSpace (𝓡 n) v,
      ⟪w, mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) v a⟫_ℝ =
      ⟪w', mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) v a⟫_ℝ) :
    ∃ t : ℝ, w - w' = t • (v : W) := by
  have horth : w - w' ∈ ((ℝ ∙ (v : W))ᗮ)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hzr : z ∈ (mvfderiv (𝓡 n)
        ((↑) : Metric.sphere (0 : W) 1 → W) v).range := by
      rwa [range_mvfderiv_subtypeVal]
    obtain ⟨a, rfl⟩ := hzr
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (heq a)
  rw [Submodule.orthogonal_orthogonal] at horth
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp horth
  exact ⟨t, ht.symm⟩

theorem base_momentum_bound {P : W → Z} (hP : Differentiable ℝ P)
    {C₁ A : ℝ} (hC₁ : 0 ≤ C₁)
    (hbound : ∀ w, ‖fderiv ℝ P w‖ ≤ C₁ * ‖w‖)
    {w w' : W} (hw : ‖w‖ ≤ A) (hw' : ‖w'‖ ≤ A) :
    ‖P w - P w'‖ ≤ (C₁ * A) * ‖w - w'‖ := by
  apply (convex_closedBall (0 : W) A).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hP x) _ (by simpa using hw') (by simpa using hw)
  intro x hx
  have hx' : ‖x‖ ≤ A := by simpa using hx
  exact (hbound x).trans (mul_le_mul_of_nonneg_left hx' hC₁)

theorem eq_of_equal_base_momenta {P : W → Z} (hP : Differentiable ℝ P)
    {C₁ A : ℝ} (hC₁ : 0 ≤ C₁)
    (hbound : ∀ w, ‖fderiv ℝ P w‖ ≤ C₁ * ‖w‖)
    {v w w' : W} (hv : ‖v‖ = 1)
    (hw : ‖w‖ ≤ A) (hw' : ‖w'‖ ≤ A)
    {dR : Z} (hscale : C₁ * A < ‖dR‖)
    (hrad : ∃ t : ℝ, w - w' = t • v)
    (heq : P w - ⟪v, w⟫_ℝ • dR = P w' - ⟪v, w'⟫_ℝ • dR) :
    w = w' := by
  obtain ⟨t, ht⟩ := hrad
  have hin : ⟪v, w⟫_ℝ - ⟪v, w'⟫_ℝ = t := by
    rw [← inner_sub_right, ht, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hp : P w - P w' = t • dR := by
    rw [← hin, sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mpr heq
  have hb := base_momentum_bound hP hC₁ hbound hw hw'
  rw [hp, ht, norm_smul, norm_smul, hv, mul_one, Real.norm_eq_abs] at hb
  have ht0 : t = 0 := by
    by_contra h
    have habs : 0 < |t| := abs_pos.mpr h
    have hh : |t| * (C₁ * A) < |t| * ‖dR‖ := mul_lt_mul_of_pos_left hscale habs
    nlinarith
  exact sub_eq_zero.mp (by simpa [ht0] using ht)

theorem exponential_differential_dominates {c C₁ K R δ : ℝ}
    (hK : 0 < K) (hR : 0 < R)
    (hchoice : C₁ / c < K * δ) {dθ : Z} (hθ : δ ≤ ‖dθ‖) :
    C₁ * (R / c) < ‖(K * R) • dθ‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hK hR)]
  calc
    C₁ * (R / c) = (C₁ / c) * R := by ring
    _ < (K * δ) * R := mul_lt_mul_of_pos_right hchoice hR
    _ ≤ (K * ‖dθ‖) * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ hK.le) hR.le
    _ = K * R * ‖dθ‖ := by ring

end NearbyLagrangian.BranchSeparation

namespace NearbyLagrangian.MomentumCalculus

variable {W E B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B]
  {n : ℕ} [Fact (Module.finrank ℝ W = n + 1)]

theorem uncut_mfderiv {f R : B → ℝ} {b : B}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f b)
    (hR : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) R b)
    (w : W) (v : Metric.sphere (0 : W) 1)
    (a : TangentSpace 𝓘(ℝ, E) b) (d : TangentSpace (𝓡 n) v) :
    mvfderiv (𝓘(ℝ, E).prod (𝓡 n))
      (fun q : B × Metric.sphere (0 : W) 1 => f q.1 - R q.1 * ⟪w, (q.2 : W)⟫_ℝ)
      (b, v) (a, d) =
      (mvfderiv 𝓘(ℝ, E) f b a : ℝ) -
        (mvfderiv 𝓘(ℝ, E) R b a : ℝ) * ⟪w, (v : W)⟫_ℝ -
        R b * ⟪w, mvfderiv (𝓡 n) ((↑) : Metric.sphere (0 : W) 1 → W) v d⟫_ℝ := by
  have hfp := hf.hasMFDerivAt.comp (b, v)
    (mdifferentiableAt_fst (I := 𝓘(ℝ, E)) (I' := 𝓡 n)).hasMFDerivAt
  have hRp := hR.hasMFDerivAt.comp (b, v)
    (mdifferentiableAt_fst (I := 𝓘(ℝ, E)) (I' := 𝓡 n)).hasMFDerivAt
  have hv := ((contMDiff_coe_sphere (m := ∞) v).mdifferentiableAt (by simp)).hasMFDerivAt.comp
    (b, v) (mdifferentiableAt_snd (I := 𝓘(ℝ, E)) (I' := 𝓡 n)).hasMFDerivAt
  have hl := (innerSL ℝ w).hasMFDerivAt.comp (b, v) hv
  have hd := (hfp.sub (hRp.mul hl)).mfderiv
  change mfderiv (𝓘(ℝ, E).prod (𝓡 n)) 𝓘(ℝ, ℝ)
    (fun q : B × Metric.sphere (0 : W) 1 => f q.1 - R q.1 * ⟪w, (q.2 : W)⟫_ℝ)
    (b, v) (a, d) = _
  erw [hd]
  rw [mfderiv_fst, mfderiv_snd]
  change mvfderiv 𝓘(ℝ, E) f b a - (R b * ⟪w, mvfderiv (𝓡 n)
    ((↑) : Metric.sphere (0 : W) 1 → W) v d⟫_ℝ +
    ⟪w, (v : W)⟫_ℝ * mvfderiv 𝓘(ℝ, E) R b a) = _
  ring

end NearbyLagrangian.MomentumCalculus

namespace NearbyLagrangian.MixedDerivative

variable {W E B Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ, E) 1 B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def baseDerivative (f : B → W → ℝ) (b : B) (w : W) : E →L[ℝ] ℝ := by
  change TangentSpace 𝓘(ℝ, E) b →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (f b w)
  exact mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q => f q w) b

theorem contDiffAt_baseDerivative {f : B → W → ℝ} {b : B} {w : W}
    (hf : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (fun p : B × W => f p.1 p.2) (b, w)) :
    ContDiffAt ℝ ∞ (baseDerivative (E := E) f b) w := by
  let F : W → B → ℝ := fun a q => f q a
  have hs : ContMDiffAt (𝓘(ℝ, W).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry F) (w, b) :=
    hf.comp (w, b) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hd := hs.mfderiv (m := ∞) F (fun _ => b) contMDiffAt_const (by simp)
  have heq : inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun _ : W => b) (fun a => F a b)
      (baseDerivative (E := E) f b) w =
      (baseDerivative (E := E) f b) := by
    funext a
    erw [inTangentCoordinates_eq _ _ _ (mem_chart_source E b) (mem_univ _)]
    rw [tangentBundleCore_coordChange_model_space]
    ext v
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (F a) b)
      ((tangentBundleCore 𝓘(ℝ, E) B).coordChange (achart E b) (achart E b) b v) = _
    rw [(tangentBundleCore 𝓘(ℝ, E) B).coordChange_self _ _ (mem_achart_source E b)]
    rfl
  change ContMDiffAt 𝓘(ℝ, W) 𝓘(ℝ, E →L[ℝ] ℝ) ∞
    (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun _ : W => b) (fun a => F a b)
      (baseDerivative (E := E) f b) w) w at hd
  rw [heq] at hd
  exact contMDiffAt_iff_contDiffAt.mp hd

theorem contMDiffAt_param_deriv {g : B → ℝ → ℝ} {b : B} {t : ℝ}
    (hg : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry g) (b, t)) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun q => deriv (g q) t) b := by
  have h := hg.mfderiv (m := ∞) g (fun _ => t) contMDiffAt_const (by simp)
  erw [inTangentCoordinates_model_space] at h
  have hd : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ →L[ℝ] ℝ) ∞
      (fun q => fderiv ℝ (g q) t) b := by
    simpa only [mfderiv_eq_fderiv] using h
  exact hd.clm_apply contMDiffAt_const

theorem contMDiffAt_param_fderiv {g : B → W → ℝ} {p : B × W}
    (hg : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry g) p) :
    ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, W)) 𝓘(ℝ, W →L[ℝ] ℝ) ∞
      (fun q => fderiv ℝ (g q.1) q.2) p := by
  let F : (B × W) → W → ℝ := fun q w => g q.1 w
  have hF : ContMDiffAt ((𝓘(ℝ, E).prod 𝓘(ℝ, W)).prod 𝓘(ℝ, W)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry F) (p, p.2) :=
    hg.comp (p, p.2) ((contMDiffAt_fst.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  have h := hF.mfderiv (m := ∞) F Prod.snd contMDiffAt_snd (by simp)
  erw [inTangentCoordinates_model_space] at h
  simpa only [F, mfderiv_eq_fderiv] using h

end NearbyLagrangian.MixedDerivative

end

end OAI
