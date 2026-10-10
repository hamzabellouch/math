import OAI.Geometry.RCD.Transport.PairedLipschitzCompactness
import OAI.Geometry.RCD.Sobolev.AlmostMonotoneUniformLimit
import OAI.Geometry.RCD.Sobolev.DenseTimeSequence

namespace OAI

/-! # One time-compactness subsequence for a countable exhaustion

Each spatial region can have its own positive time margin and bounds.
The subsequence and exceptional time set are common to every region.
-/

open Set Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem countable_almost_monotone_compactness
    {Y : ℕ → Type*} [∀ m, MetricSpace (Y m)] [∀ m, CompactSpace (Y m)]
    [∀ m, Nonempty (Y m)] (δ M : ℕ → ℝ) (L : ℕ → ℝ≥0)
    (hδ : ∀ m, δ m ≤ 1) (hM : ∀ m, 0 ≤ M m)
    (f : ∀ m, ℕ → ℝ → Y m → ℝ) (e : ℕ → ℕ → ℝ)
    (he : ∀ m, Tendsto (e m) atTop (𝓝 0))
    (hb : ∀ m k t, t ∈ Icc (δ m) 1 → ∀ x, |f m k t x| ≤ M m)
    (hL : ∀ m k t, t ∈ Icc (δ m) 1 → LipschitzWith (L m) (f m k t))
    (ho : ∀ m k a b, δ m ≤ a → a ≤ b → b ≤ 1 → ∀ x,
      f m k a x-f m k b x ≤ e m k*(b-a)) :
    ∃ (g : ∀ m, ℝ → Y m → ℝ) (a : ℕ → ℕ) (N : Set ℝ),
      StrictMono a ∧ N.Countable ∧ ∀ m,
        (∀ t x, |g m t x| ≤ M m) ∧ (∀ t, LipschitzWith (L m) (g m t)) ∧
        (∀ x, Monotone (fun t => g m t x)) ∧
        ∀ t ∈ Ioo (δ m) 1, t ∉ N →
          TendstoUniformly (fun k => f m (a k) t) (g m t) atTop := by
  classical
  choose s hs hdense using fun m => exists_dense_time_sequence (hδ m)
  obtain ⟨v,a,ha,hv⟩ := paired_uniform_lipschitz_subsequence
    (Y := Y) (fun m i k => f m k (s m i)) (fun m _ => L m) (fun m _ => M m)
    (fun m i k => hL m k (s m i) (hs m i))
    (fun m i k x => hb m k (s m i) (hs m i) x)
  let g := fun m t x => timeLowerEnvelope (M m) (s m) (fun i => v m i x) t
  have hex (m : ℕ) : ∃ N : Set ℝ, N.Countable ∧
      ∀ t ∈ Ioo (δ m) 1, t ∉ N →
        TendstoUniformly (fun k => f m (a k) t) (g m t) atTop :=
    almost_monotone_uniform_limit (hM m) (s m) (v m) (L m) (hs m) (hdense m)
      (fun k => f m (a k)) (fun k => e m (a k)) ((he m).comp ha.tendsto_atTop)
      (fun k t ht x => hb m (a k) t ht x) (fun i => (hv m i).2.1)
      (fun i => (hv m i).1) (fun k t ht => hL m (a k) t ht)
      (fun i x => (hv m i).2.2.tendsto_at x)
      (fun k u w hu huw hw x => ho m (a k) u w hu huw hw x)
  choose N hN hlim using hex
  refine ⟨g,a,⋃ m, N m,ha,Set.countable_iUnion hN,?_⟩
  intro m
  refine ⟨?_,?_,?_,?_⟩
  · intro t x
    exact timeLowerEnvelope_bounds (hM m) (s m) (fun i => v m i x) (fun i => (hv m i).2.1 x) t
  · intro t
    exact timeLowerEnvelope_lipschitz (hM m) (s m) (v m) (L m)
      (fun i => (hv m i).2.1) (fun i => (hv m i).1) t
  · intro x
    exact timeLowerEnvelope_monotone (hM m) (s m) (fun i => v m i x) (fun i => (hv m i).2.1 x)
  · intro t ht hnot
    exact hlim m t ht (fun hm => hnot (mem_iUnion.mpr ⟨m,hm⟩))

end RegularPointCoordinates

end

end OAI
