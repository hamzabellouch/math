import Mathlib
import OAI.Geometry.SmoothYau.Limits.ExistsCompactSignedEnvelope

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_exhaustible_signed_envelope (g : SmoothMetric E E) {f l : E → ℝ}
    (hf : ContDiff ℝ ∞ f) {R : ℝ} (hR : 0<R)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hbR : b<R/2) (C : ℝ)
    (hmin : ∀ x, C+1≤l x) (heq : ∀ x ∈ closedBall 0 R, f x=l x)
    (hstrict : ∀ x ∈ closedBall 0 R,
      coordinateMetricGradient g f x ≠ 0 ∧ actualProfileStrict g f x) :
    ∃ δ>0, δ≤1/2 ∧ ∃ φ : E → ℝ, ContDiff ℝ ∞ φ ∧
      HasCompactSupport (fun x => φ x-C) ∧
      tsupport (fun x => φ x-C) ⊆ closedBall 0 (3*R/4) ∧
      (∀ x ∈ closedBall 0 (b),
        coordinateMetricGradient g φ x ≠ 0 ∧ actualProfileStrict g φ x) ∧
      (∀ x ∈ closedBall 0 a, φ x=l x+δ) ∧
      (∀ x ∉ closedBall 0 (b), φ x≤l x-δ) := by
  let β : ContDiffBump (0:E) := ⟨a,b,ha,hab⟩
  let χ : ContDiffBump (0:E) := ⟨R/2,3*R/4,by positivity,by linarith⟩
  let h : E → ℝ := fun x => 2*β x-1
  have hh : ContDiff ℝ ∞ h := (contDiff_const.mul β.contDiff).sub contDiff_const
  obtain ⟨ε,hε,hstable⟩ := exists_compact_strict_perturbation g hf hh
    (isCompact_closedBall 0 (b)) (fun x hx => hstrict x
      (closedBall_subset_closedBall (by linarith) hx))
  let δ := min (ε/2) (1/2)
  have hδ : 0<δ := lt_min (half_pos hε) (by norm_num)
  have hδε : |δ|<ε := by rw [abs_of_pos hδ]; exact (min_le_left _ _).trans_lt (half_lt_self hε)
  have hδ1 : δ≤1/2 := min_le_right _ _
  let φ : E → ℝ := fun x => C+χ x*(f x-δ-C)+2*δ*β x
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_const.add (χ.contDiff.mul ((hf.sub contDiff_const).sub contDiff_const))).add
      (contDiff_const.mul β.contDiff)
  have hcover : tsupport (fun x => φ x-C) ⊆ closedBall 0 (3*R/4) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro x hx
    by_contra hh
    have hχ : χ x=0 := χ.zero_of_le_dist (by
      have hn : 3*R/4 < dist x 0 := by simpa only [mem_closedBall,not_le] using hh
      exact hn.le)
    have hβ : β x=0 := β.zero_of_le_dist (by
      have hn : 3*R/4 < dist x 0 := by simpa only [mem_closedBall,not_le] using hh
      dsimp [β]; linarith)
    exact hx (by simp [φ,hχ,hβ])
  refine ⟨δ,hδ,hδ1,φ,hφ,?_,hcover,?_,?_,?_⟩
  · exact (isCompact_closedBall 0 (3*R/4)).of_isClosed_subset (isClosed_tsupport _) hcover
  · intro x hx
    have heχ := χ.eventuallyEq_one_of_mem_ball (show x ∈ ball 0 χ.rIn from
      closedBall_subset_ball (by dsimp [χ]; linarith) hx)
    have he : φ =ᶠ[𝓝 x] (fun y => f y+δ*h y) := by
      filter_upwards [heχ] with y hy
      dsimp [φ,h]
      change χ y=1 at hy
      rw [hy]
      ring
    have hj := actualJet_eventuallyEq g he
    rw [hj.1,hj.2.2.1]
    exact hstable δ hδε x hx
  · intro x hx
    have hβ := β.one_of_mem_closedBall hx
    have hχ := χ.one_of_mem_closedBall (closedBall_subset_closedBall (by dsimp [χ]; linarith) hx)
    have he := heq x (closedBall_subset_closedBall (by linarith) hx)
    dsimp [φ]
    rw [hβ,hχ,he]
    ring
  · intro x hx
    have hd : b < dist x 0 := by simpa only [mem_closedBall,not_le] using hx
    have hβ : β x=0 := β.zero_of_le_dist (by dsimp [β]; linarith)
    have hlow : C≤l x-δ := by have hm:=hmin x; linarith
    dsimp [φ]
    rw [hβ,mul_zero,add_zero]
    by_cases hz : χ x=0
    · simpa [hz] using hlow
    · have hmem : x ∈ ball 0 χ.rOut := by rwa [←χ.support_eq]
      have he := heq x (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by dsimp [χ]; linarith)) hmem)
      rw [he]
      have hc := χ.le_one (x:=x)
      have hn := χ.nonneg (x:=x)
      nlinarith
end YauCounterexamples
end

end OAI
