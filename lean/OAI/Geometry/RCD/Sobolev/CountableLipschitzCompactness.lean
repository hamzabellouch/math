import OAI.Geometry.RCD.Sobolev.LipschitzCompactSubsequence

namespace OAI

/-! # One uniform-convergence subsequence for a countable family

Each family has its own compact domain and Lipschitz bound. The product
of the Arzela--Ascoli compact sets supplies a single common subsequence.
-/

open Set Filter
open scoped NNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem countable_uniform_lipschitz_subsequence
    {Y : ℕ → Type*} [∀ m, MetricSpace (Y m)] [∀ m, CompactSpace (Y m)]
    (f : ∀ m, ℕ → Y m → ℝ) (L : ℕ → ℝ≥0) (A : ℕ → ℝ)
    (hl : ∀ m k, LipschitzWith (L m) (f m k))
    (hb : ∀ m k y, |f m k y|≤A m) :
    ∃ (g : ∀ m, Y m → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ∀ m, LipschitzWith (L m) (g m) ∧ (∀ y, |g m y|≤A m) ∧
        TendstoUniformly (fun k => f m (a k)) (g m) atTop := by
  let F : ∀ m, ℕ → Y m →ᵇ ℝ := fun m k =>
    BoundedContinuousFunction.mkOfCompact ⟨f m k,(hl m k).continuous⟩
  have hc (m : ℕ) : IsCompact (closure (range (F m))) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (-(A m)) (A m))
      isCompact_Icc (range (F m))
    · rintro q y ⟨k,rfl⟩
      exact abs_le.mp (hb m k y)
    · apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L m:ℝ)*r)
        (by simpa only [mul_zero] using
          (show Continuous (fun r : ℝ => (L m:ℝ)*r) by fun_prop).tendsto (0:ℝ))
      rintro y z ⟨q,k,rfl⟩
      exact (hl m k).dist_le_mul y z
  obtain ⟨g,_,a,ha,hlim⟩ := (isCompact_pi_infinite hc).tendsto_subseq
    (fun k m => subset_closure (mem_range_self k))
  have hm (m : ℕ) : Tendsto (fun k => F m (a k)) atTop (𝓝 (g m)) :=
    ((continuous_apply m).tendsto g).comp hlim
  have hp (m : ℕ) (y : Y m) : Tendsto (fun k => f m (a k) y) atTop (𝓝 (g m y)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const y).continuous.tendsto (g m)).comp (hm m)
  refine ⟨fun m => g m,a,ha,?_⟩
  intro m
  refine ⟨?_,?_,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (hm m)⟩
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    exact le_of_tendsto ((hp m y).dist (hp m z))
      (Eventually.of_forall fun k => (hl m (a k)).dist_le_mul y z)
  · intro y
    exact le_of_tendsto (hp m y).abs (Eventually.of_forall fun k => hb m (a k) y)

theorem countable_lipschitz_subsequence_on_compact {Z : Type*} [MetricSpace Z]
    {s : Set Z} (hs : IsCompact s) (f : ℕ → ℕ → Z → ℝ)
    (L : ℕ → ℝ≥0) (A : ℕ → ℝ)
    (hl : ∀ m k, LipschitzWith (L m) (f m k))
    (hb : ∀ m k z, z∈s → |f m k z|≤A m) :
    ∃ (g : ℕ → Z → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ∀ m, LipschitzWith (L m) (g m) ∧ (∀ z∈s, |g m z|≤A m) ∧
        ∀ ε : ℝ, 0<ε → ∀ᶠ k in atTop, ∀ z∈s, |f m (a k) z-g m z|<ε := by
  classical
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  obtain ⟨G,a,ha,hG⟩ := countable_uniform_lipschitz_subsequence
    (Y := fun _ => s) (fun m k z => f m k z) L A
    (fun m k => by simpa only [mul_one,Function.comp_def] using
      (hl m k).comp (LipschitzWith.subtype_val s)) (fun m k z => hb m k z z.property)
  let G0 : ℕ → Z → ℝ := fun m z => if h:z∈s then G m ⟨z,h⟩ else 0
  have hG0 (m : ℕ) : LipschitzOnWith (L m) (G0 m) s := by
    intro x hx y hy
    simpa only [G0,dite_eq_left hx,dite_eq_left hy,Subtype.edist_eq] using
      (hG m).1 ⟨x,hx⟩ ⟨y,hy⟩
  choose g hg he using fun m => (hG0 m).extend_real
  have heq (m : ℕ) (z:s) : G m z=g m z := by
    simpa only [G0,dite_eq_left z.property] using he m z.property
  refine ⟨g,a,ha,?_⟩
  intro m
  refine ⟨hg m,?_,?_⟩
  · intro z hz
    rw [← heq m ⟨z,hz⟩]
    exact (hG m).2.1 ⟨z,hz⟩
  · intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hG m).2.2) ε hε] with k hk
    intro z hz
    simpa only [Real.dist_eq,heq,abs_sub_comm] using hk ⟨z,hz⟩

end RegularPointCoordinates

end

end OAI
