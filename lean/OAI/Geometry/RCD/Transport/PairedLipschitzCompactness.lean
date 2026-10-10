import OAI.Geometry.RCD.Sobolev.CountableLipschitzCompactness

namespace OAI

/-! # One subsequence for all spatial regions and prescribed time slices -/

open Set Filter
open scoped NNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem paired_uniform_lipschitz_subsequence
    {Y : ℕ → Type*} [∀ m, MetricSpace (Y m)] [∀ m, CompactSpace (Y m)]
    (f : ∀ m, ℕ → ℕ → Y m → ℝ) (L : ℕ → ℕ → ℝ≥0) (A : ℕ → ℕ → ℝ)
    (hl : ∀ m i k, LipschitzWith (L m i) (f m i k))
    (hb : ∀ m i k x, |f m i k x| ≤ A m i) :
    ∃ (g : ∀ m, ℕ → Y m → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ∀ m i, LipschitzWith (L m i) (g m i) ∧ (∀ x, |g m i x| ≤ A m i) ∧
        TendstoUniformly (fun k => f m i (a k)) (g m i) atTop := by
  let F : ∀ j : ℕ × ℕ, ℕ → Y j.1 →ᵇ ℝ := fun j k =>
    BoundedContinuousFunction.mkOfCompact ⟨f j.1 j.2 k,(hl j.1 j.2 k).continuous⟩
  have hc (j : ℕ × ℕ) : IsCompact (closure (range (F j))) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (-(A j.1 j.2)) (A j.1 j.2))
      isCompact_Icc (range (F j))
    · rintro q x ⟨k,rfl⟩
      exact abs_le.mp (hb j.1 j.2 k x)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L j.1 j.2:ℝ)*r)
        (by simpa only [mul_zero] using
          (show Continuous (fun r : ℝ => (L j.1 j.2:ℝ)*r) by fun_prop).tendsto (0:ℝ))
      rintro x y ⟨q,k,rfl⟩
      exact (hl j.1 j.2 k).dist_le_mul x y
  obtain ⟨g,_,a,ha,hlim⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (fun k j => subset_closure (mem_range_self k))
  have hm (m i : ℕ) : Tendsto (fun k => F (m,i) (a k)) atTop (𝓝 (g (m,i))) :=
    ((continuous_apply (m,i)).tendsto g).comp hlim
  have hp (m i : ℕ) (x : Y m) : Tendsto (fun k => f m i (a k) x) atTop (𝓝 (g (m,i) x)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.tendsto (g (m,i))).comp (hm m i)
  refine ⟨fun m i => g (m,i),a,ha,?_⟩
  intro m i
  refine ⟨?_,?_,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hm m i)⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hp m i x).dist (hp m i y))
      (Eventually.of_forall fun k => (hl m i (a k)).dist_le_mul x y)
  · intro x
    exact le_of_tendsto (hp m i x).abs (Eventually.of_forall fun k => hb m i (a k) x)

end RegularPointCoordinates

end

end OAI
