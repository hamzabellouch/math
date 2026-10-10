import OAI.GroupTheory.PolycyclicRecognition.Analysis.LeftInvariantRiemannianMetric

namespace OAI

/-! # Left translation preserves the Riemannian length -/

noncomputable section
namespace PolycyclicRecognition

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology Bundle

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  (e : E ≃L[ℝ] F)

abbrev leftRiemannianBundle : RiemannianBundle (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
  ⟨(leftInvariantRiemannianMetric (G := G) e).toRiemannianMetric⟩

theorem leftRiemannian_inner (g : G) (v w : TangentSpace (𝓘(ℝ, E)) g) :
    letI := leftRiemannianBundle (G := G) e
    inner ℝ v w = leftInvariantInner e g v w := rfl

theorem norm_mfderiv_leftTranslation (g h : G) (v : TangentSpace (𝓘(ℝ, E)) h) :
    letI := leftRiemannianBundle (G := G) e
    ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v‖ = ‖v‖ := by
  let := leftRiemannianBundle (G := G) e
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    leftRiemannian_inner, leftRiemannian_inner]
  exact leftInvariantInner_mul e g h v v

theorem pathELength_leftTranslation (g : G) {γ : ℝ → G} {a b : ℝ}
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 γ (Icc a b)) :
    letI := leftRiemannianBundle (G := G) e
    Manifold.pathELength (𝓘(ℝ, E)) (fun t => g * γ t) a b =
      Manifold.pathELength (𝓘(ℝ, E)) γ a b := by
  let := leftRiemannianBundle (G := G) e
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hγt := (hγ t ⟨ht.1.le, ht.2.le⟩).mdifferentiableWithinAt one_ne_zero
    |>.mdifferentiableAt (Icc_mem_nhds ht.1 ht.2)
  have hd := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) t
    ((contMDiff_mul_left (a := g) (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp)) hγt
  have hv := congrArg (fun D => D (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) hd
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t => g * γ t) t 1 =
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t 1) at hv
  change ‖mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun t => g * γ t) t 1‖ₑ =
    ‖mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t 1‖ₑ
  calc
    _ = ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ t 1)‖ₑ :=
      congrArg (fun v : TangentSpace (𝓘(ℝ, E)) (g * γ t) => ‖v‖ₑ) hv
    _ = _ := by simp only [enorm, nnnorm, norm_mfderiv_leftTranslation e]

theorem riemannianEDist_leftTranslation (g x y : G) :
    letI := leftRiemannianBundle (G := G) e
    Manifold.riemannianEDist (𝓘(ℝ, E)) (g * x) (g * y) =
      Manifold.riemannianEDist (𝓘(ℝ, E)) x y := by
  let := leftRiemannianBundle (G := G) e
  have hle (a u v : G) : Manifold.riemannianEDist (𝓘(ℝ, E)) (a * u) (a * v) ≤
      Manifold.riemannianEDist (𝓘(ℝ, E)) u v := by
    apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hr
    have hbound := Manifold.riemannianEDist_le_pathELength
      ((contMDiffOn_const (c := a)).mul hγ)
      (congrArg (a * ·) h₀) (congrArg (a * ·) h₁) (by norm_num : (0 : ℝ) ≤ 1)
    change Manifold.riemannianEDist (𝓘(ℝ, E)) (a * u) (a * v) ≤
      Manifold.pathELength (𝓘(ℝ, E)) (fun t => a * γ t) 0 1 at hbound
    rw [pathELength_leftTranslation e a hγ] at hbound
    exact hbound.trans_lt hlen
  apply le_antisymm (hle g x y)
  simpa only [inv_mul_cancel_left] using hle g⁻¹ (g * x) (g * y)

end PolycyclicRecognition

end

end OAI
