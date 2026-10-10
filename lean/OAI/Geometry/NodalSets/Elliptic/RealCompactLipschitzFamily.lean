import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Sequences

namespace OAI

namespace Yau.Geometry
open Set Metric Filter BoundedContinuousFunction
open scoped Topology NNReal
noncomputable section
variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X]

theorem real_bounded_lipschitz_compact (F : ℕ → X →ᵇ ℝ) (B : ℝ) (L : ℝ≥0)
    (hb : ∀ j x, |F j x| ≤ B) (hL : ∀ j, LipschitzWith L (F j)) :
    IsCompact (closure (range F)) := by
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc (range F)
  · rintro f x ⟨j,rfl⟩
    exact abs_le.mp (hb j x)
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε/((L:ℝ)+1),div_pos hε (by positivity),?_⟩
    intro y hy f
    rcases f with ⟨_,j,rfl⟩
    have h := (hL j).dist_le_mul x y
    have hd : dist x y < ε/((L:ℝ)+1) := by simpa only [dist_comm] using hy
    have hh := (lt_div_iff₀ (show 0 < (L:ℝ)+1 by positivity)).mp hd
    exact h.trans_lt (by nlinarith [dist_nonneg (x:=x) (y:=y)])

theorem real_lipschitz_uniform_subsequence (F : ℕ → X → ℝ) (B : ℝ) (L : ℝ≥0)
    (hb : ∀ j x, |F j x| ≤ B) (hL : ∀ j, LipschitzWith L (F j)) :
    ∃ f : X → ℝ, Continuous f ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      TendstoUniformly (fun j ↦ F (nu j)) f atTop := by
  let G : ℕ → X →ᵇ ℝ := fun j ↦ BoundedContinuousFunction.mkOfCompact ⟨F j,(hL j).continuous⟩
  have hc := real_bounded_lipschitz_compact G B L hb hL
  obtain ⟨f,_,nu,hnu,ht⟩ := hc.tendsto_subseq (fun j ↦ subset_closure (mem_range_self j))
  exact ⟨f,f.continuous,nu,hnu,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht⟩

end
end Yau.Geometry

end OAI
