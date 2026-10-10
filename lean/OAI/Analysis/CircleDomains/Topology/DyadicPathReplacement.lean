import OAI.Analysis.CircleDomains.Topology.DyadicPathApproximation

namespace OAI

/-! Replace a finely subdivided map by a path whose endpoints lie in a
fixed set, preserving a uniform error and a prescribed neighborhood. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

def halfTime : I := ⟨1 / 2, by constructor <;> norm_num⟩
@[simp] lemma leftHalf_zero : leftHalf 0 = 0 := by apply Subtype.ext; norm_num [leftHalf]
@[simp] lemma leftHalf_one : leftHalf 1 = halfTime := by apply Subtype.ext; norm_num [leftHalf, halfTime]
@[simp] lemma rightHalf_zero : rightHalf 0 = halfTime := by apply Subtype.ext; norm_num [rightHalf, halfTime]
@[simp] lemma rightHalf_one : rightHalf 1 = 1 := by apply Subtype.ext; norm_num [rightHalf]

lemma dyadic_path_replacement
    {E : Type*} [MetricSpace E] {K : Set E} {τ δ r η : ℝ}
    (hδ : 3 * τ ≤ δ)
    (hjoin : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∃ γ : Path x y, (∀ t, dist (γ t) x < r) ∧
        (∀ t, ∃ c ∈ K, dist (γ t) c < η))
    (n : ℕ) (f k : I → E) (hk : ∀ t, k t ∈ K)
    (hosc : dyadicSmallOscillation n f τ) (hnear : ∀ t, dist (f t) (k t) < τ) :
    ∃ γ : Path (k 0) (k 1), (∀ t, dist (γ t) (f t) < r + 2 * τ) ∧
      (∀ t, ∃ c ∈ K, dist (γ t) c < η) := by
  induction n generalizing f k with
  | zero =>
      have hxy : dist (k 0) (k 1) < δ := by
        have h0 := hnear 0
        have h1 := hnear 1
        have h01 := hosc 0 1
        have ht := dist_triangle (k 0) (f 0) (k 1)
        have ht' := dist_triangle (f 0) (f 1) (k 1)
        rw [dist_comm (k 0) (f 0)] at ht
        linarith
      obtain ⟨γ, hγ, hKγ⟩ := hjoin (k 0) (hk 0) (k 1) (hk 1) hxy
      refine ⟨γ, ?_, hKγ⟩
      intro t
      have h0 := hnear 0
      have hos := hosc 0 t
      have hgt := hγ t
      have ht := dist_triangle (γ t) (k 0) (f t)
      have ht' := dist_triangle (k 0) (f 0) (f t)
      rw [dist_comm (k 0) (f 0)] at ht'
      linarith
  | succ n ih =>
      have hleft := ih (f ∘ leftHalf) (k ∘ leftHalf) (fun t => hk (leftHalf t))
        hosc.1 (fun t => hnear (leftHalf t))
      have hright := ih (f ∘ rightHalf) (k ∘ rightHalf) (fun t => hk (rightHalf t))
        hosc.2 (fun t => hnear (rightHalf t))
      simp only [comp_apply, leftHalf_zero, leftHalf_one] at hleft
      simp only [comp_apply, rightHalf_zero, rightHalf_one] at hright
      obtain ⟨γ₀, he₀, hn₀⟩ := hleft
      obtain ⟨γ₁, he₁, hn₁⟩ := hright
      refine ⟨γ₀.trans γ₁, path_trans_pointwise_error γ₀ γ₁ f he₀ he₁, ?_⟩
      intro t
      have ht : (γ₀.trans γ₁) t ∈ range γ₀ ∪ range γ₁ := by
        rw [← Path.trans_range]
        exact mem_range_self t
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [← hs]
        exact hn₀ s
      · rw [← hs]
        exact hn₁ s

end CircleDomainRigidity

end

end OAI
