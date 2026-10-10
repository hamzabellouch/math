import OAI.Geometry.RCD.Sobolev.CountableLipschitzCompactness

namespace OAI

/-! # Simultaneous Lipschitz limits on distinct compact domains -/

open Set Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem countable_lipschitz_subsequence_on_compacts {Z : Type*} [MetricSpace Z]
    (s : ℕ → Set Z) (hs : ∀ m, IsCompact (s m)) (f : ℕ → ℕ → Z → ℝ)
    (L : ℕ → ℝ≥0) (A : ℕ → ℝ)
    (hl : ∀ m k, LipschitzWith (L m) (f m k))
    (hb : ∀ m k z, z ∈ s m → |f m k z| ≤ A m) :
    ∃ (g : ℕ → Z → ℝ) (a : ℕ → ℕ), StrictMono a ∧
      ∀ m, LipschitzWith (L m) (g m) ∧ (∀ z ∈ s m, |g m z| ≤ A m) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ z ∈ s m,
          |f m (a k) z-g m z| < ε := by
  classical
  let (m : ℕ) : CompactSpace (s m) := isCompact_iff_compactSpace.mp (hs m)
  obtain ⟨G,a,ha,hG⟩ := countable_uniform_lipschitz_subsequence
    (Y := fun m => s m) (fun m k z => f m k z) L A
    (fun m k => by simpa only [mul_one,Function.comp_def] using
      (hl m k).comp (LipschitzWith.subtype_val (s m))) (fun m k z => hb m k z z.property)
  let G0 : ℕ → Z → ℝ := fun m z => if h : z ∈ s m then G m ⟨z,h⟩ else 0
  have hG0 (m : ℕ) : LipschitzOnWith (L m) (G0 m) (s m) := by
    intro x hx y hy
    simpa only [G0,dite_eq_left hx,dite_eq_left hy,Subtype.edist_eq] using
      (hG m).1 ⟨x,hx⟩ ⟨y,hy⟩
  choose g hg he using fun m => (hG0 m).extend_real
  have heq (m : ℕ) (z : s m) : G m z = g m z := by
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
