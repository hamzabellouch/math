import Mathlib

namespace OAI

/-! Weak subsequences, closed convex graphs and lower semicontinuity. -/

namespace BFSSNormalAnalysis
noncomputable section
open Filter Topology Set
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [TopologicalSpace.SeparableSpace F]

theorem bounded_weak_subsequence (y : ℕ → F) (B : ℝ) (hB : ∀ n, ‖y n‖ ≤ B) :
    ∃ (z : F) (σ : ℕ → ℕ), StrictMono σ ∧ ‖z‖ ≤ B ∧
      ∀ v : F, Tendsto (fun n => inner ℝ (y (σ n)) v) atTop (𝓝 (inner ℝ z v)) := by
  let t : ℕ → WeakDual ℝ F := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ F (y n))
  have ht : ∀ n, t n ∈ (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ F) B) := by
    intro n
    change dist ((InnerProductSpace.toDual ℝ F) (y n)) 0 ≤ B
    simpa using hB n
  obtain ⟨a,ha,σ,hσ,hs⟩ := (WeakDual.isSeqCompact_closedBall ℝ F 0 B) ht
  let z : F := (InnerProductSpace.toDual ℝ F).symm a.toStrongDual
  refine ⟨z,σ,hσ,?_,?_⟩
  · change dist a.toStrongDual 0 ≤ B at ha
    simpa [z] using ha
  · intro v
    have he := tendsto_iff_forall_eval_tendsto_topDualPairing.mp hs v
    change Tendsto (fun n => inner ℝ (y (σ n)) v) atTop (𝓝 (a.toStrongDual v)) at he
    simpa [z,InnerProductSpace.toDual_symm_apply] using he

omit [TopologicalSpace.SeparableSpace F] in
theorem strong_weak_mem_closed_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set (E × F)) (hCc : Convex ℝ C) (hCcl : IsClosed C)
    (x : ℕ → E) (y : ℕ → F) (x₀ : E) (y₀ : F)
    (hm : ∀ n, (x n,y n) ∈ C) (hx : Tendsto x atTop (𝓝 x₀))
    (hy : ∀ v : F, Tendsto (fun n => inner ℝ (y n) v) atTop (𝓝 (inner ℝ y₀ v))) :
    (x₀,y₀) ∈ C := by
  by_contra hn
  obtain ⟨L,u,hL,hu⟩ := geometric_hahn_banach_closed_point hCc hCcl hn
  let L₁ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E F)
  let L₂ : F →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inr ℝ E F)
  let v : F := (InnerProductSpace.toDual ℝ F).symm L₂
  have he₂ (a : F) : L₂ a = inner ℝ a v := by
    rw [real_inner_comm]
    exact (InnerProductSpace.toDual_symm_apply).symm
  have ht₂ : Tendsto (fun n => L₂ (y n)) atTop (𝓝 (L₂ y₀)) := by
    simpa only [he₂] using hy v
  have ht₁ := L₁.continuous.tendsto x₀ |>.comp hx
  have he (a : E) (b : F) : L (a,b) = L₁ a + L₂ b := by
    change L (a,b) = L (a,0) + L (0,b)
    rw [←map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  have ht : Tendsto (fun n => L (x n,y n)) atTop (𝓝 (L (x₀,y₀))) := by
    simpa only [he,Function.comp_apply] using ht₁.add ht₂
  have hu' : L (x₀,y₀) ≤ u := le_of_tendsto ht (Eventually.of_forall (fun n => (hL _ (hm n)).le))
  exact (not_le_of_gt hu) hu'

omit [CompleteSpace F] [TopologicalSpace.SeparableSpace F] in
theorem weak_norm_sq_le_limit (y : ℕ → F) (y₀ : F) (a : ℝ)
    (hy : ∀ v : F, Tendsto (fun n => inner ℝ (y n) v) atTop (𝓝 (inner ℝ y₀ v)))
    (ha : Tendsto (fun n => ‖y n‖^2) atTop (𝓝 a)) : ‖y₀‖^2 ≤ a := by
  have hi := (hy y₀).pow 2
  have hn := ha.mul_const (‖y₀‖^2)
  have hle : (inner ℝ y₀ y₀)^2 ≤ a*‖y₀‖^2 :=
    le_of_tendsto_of_tendsto hi hn (Eventually.of_forall (fun n =>
      by simpa only [pow_two,real_inner_self_eq_norm_sq] using real_inner_mul_inner_self_le (y n) y₀))
  have ha0 : 0 ≤ a := ge_of_tendsto' ha (fun n => sq_nonneg _)
  rw [real_inner_self_eq_norm_sq] at hle
  by_cases hz : y₀ = 0
  · simpa [hz] using ha0
  · have hpos : 0 < ‖y₀‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    nlinarith
end
end BFSSNormalAnalysis

namespace BFSSNormalAnalysis
noncomputable section
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem weak_norm_sq_add_le_limit (y : ℕ → F) (y₀ : F)
    (a b : ℕ → ℝ) (a₀ b₀ : ℝ)
    (hy : ∀ v : F, Tendsto (fun n => inner ℝ (y n) v) atTop (𝓝 (inner ℝ y₀ v)))
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hle : ∀ᶠ n in atTop, ‖y n‖^2+a n ≤ b n) :
    ‖y₀‖^2+a₀ ≤ b₀ := by
  have hl : ∀ᶠ n in atTop, 2*inner ℝ (y n) y₀-‖y₀‖^2+a n ≤ b n := by
    filter_upwards [hle] with n hn
    have hp := norm_nonneg (y n-y₀)
    have he := sq_nonneg ‖y n-y₀‖
    rw [norm_sub_sq_real] at he
    nlinarith
  have ht := ((hy y₀).const_mul 2).sub_const (‖y₀‖^2) |>.add ha
  have he := le_of_tendsto_of_tendsto ht hb hl
  rw [real_inner_self_eq_norm_sq] at he
  linarith
end
end BFSSNormalAnalysis

end OAI
