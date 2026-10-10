import Mathlib

namespace OAI
noncomputable section
open Set Filter Metric
open scoped Topology ZeroAtInfty
namespace FlatCompactness
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma totallyBounded_of_lipschitz_tails (F : Set C₀(V,ℂ)) (M K : ℝ) (_hM : 0≤M) (hK : 0≤K)
    (hm : ∀ f ∈ F, ∀ x, ‖f x‖≤M)
    (hl : ∀ f ∈ F, ∀ x y, ‖f x-f y‖≤K*‖x-y‖)
    (ht : ∀ ε : ℝ, 0<ε → ∃ R : ℝ, 0≤R ∧ ∀ f ∈ F, ∀ x, R≤‖x‖ → ‖f x‖≤ε) :
    TotallyBounded F := by
  classical
  apply totallyBounded_of_finite_discretization
  intro ε hε
  let δ := ε/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  let ρ := δ/(K+1)
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hKρ : K*ρ≤δ := by
    have he : ρ*(K+1)=δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨R,hR,hRt⟩ := ht δ hδ
  obtain ⟨tx,htx,hfx,hcx⟩ := (isCompact_closedBall (0:V) R).finite_cover_balls hρ
  obtain ⟨tz,htz,hfz,hcz⟩ := (isCompact_closedBall (0:ℂ) M).finite_cover_balls hδ
  let := hfx.fintype
  let := hfz.fintype
  have hz : ∀ f : F, ∀ x : tx, ∃ z : tz, dist (f.val x) z<δ := by
    intro f x
    have hv : f.val x ∈ closedBall (0:ℂ) M := by simpa using hm f f.property x
    obtain ⟨z,hzt,hzb⟩ := mem_iUnion₂.mp (hcz hv)
    exact ⟨⟨z,hzt⟩,hzb⟩
  choose Z hZ using hz
  refine ⟨tx → tz,inferInstance,Z,fun f g he => ?_⟩
  have hb : ∀ x : V, dist (f.val x) (g.val x)≤ε/2 := by
    intro x
    by_cases hx : x∈closedBall (0:V) R
    · obtain ⟨y,hyt,hyx⟩ := mem_iUnion₂.mp (hcx hx)
      have hf : dist (f.val x) (f.val y)≤δ := by
        rw [dist_eq_norm]
        exact (hl f f.property x y).trans ((mul_le_mul_of_nonneg_left
          (show ‖x-y‖≤ρ from by simpa only [dist_eq_norm] using (mem_ball.mp hyx).le) hK).trans hKρ)
      have hg : dist (g.val x) (g.val y)≤δ := by
        rw [dist_eq_norm]
        exact (hl g g.property x y).trans ((mul_le_mul_of_nonneg_left
          (show ‖x-y‖≤ρ from by simpa only [dist_eq_norm] using (mem_ball.mp hyx).le) hK).trans hKρ)
      have hv : dist (f.val y) (g.val y)≤2*δ := by
        have hz' := congrArg (fun q : tx → tz => (q ⟨y,hyt⟩ : ℂ)) he
        calc
          _ ≤ dist (f.val y) (Z f ⟨y,hyt⟩)+dist (g.val y) (Z f ⟨y,hyt⟩) := dist_triangle_right _ _ _
          _ = dist (f.val y) (Z f ⟨y,hyt⟩)+dist (g.val y) (Z g ⟨y,hyt⟩) := by rw [hz']
          _ ≤ δ+δ := add_le_add (hZ f ⟨y,hyt⟩).le (hZ g ⟨y,hyt⟩).le
          _ = _ := by ring
      calc
        _ ≤ dist (f.val x) (f.val y)+dist (g.val x) (g.val y)+dist (f.val y) (g.val y) := dist_triangle4_right _ _ _ _
        _ ≤ δ+δ+2*δ := add_le_add (add_le_add hf hg) hv
        _ = ε/2 := by dsimp [δ]; ring
    · have hr : R≤‖x‖ := by
        have hx' : ¬‖x‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hx
        exact (not_le.mp hx').le
      calc
        _ = ‖f.val x-g.val x‖ := dist_eq_norm _ _
        _ ≤ ‖f.val x‖+‖g.val x‖ := norm_sub_le _ _
        _ ≤ δ+δ := add_le_add (hRt f f.property x hr) (hRt g g.property x hr)
        _ ≤ ε/2 := by dsimp [δ]; linarith
  have hd : dist f.val g.val≤ε/2 := by
    rw [←ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
    exact (BoundedContinuousFunction.dist_le (by positivity)).mpr hb
  exact hd.trans_lt (by linarith)
end FlatCompactness

end

end OAI
