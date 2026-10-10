import Mathlib
import OAI.Analysis.AffineBernstein.ConvexLocalLimits

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Normed-space inner containment. In particular this applies to the literal
product coordinates used for the epigraph, whose norm is not a Hilbert norm. -/
omit [ProperSpace E] in
theorem normed_ball_subset_of_infDist_lt {K : Set E} (hcl : IsClosed K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) (a : E) {r : ℝ} (hr : 0 < r)
    (happ : ∀ y ∈ Metric.closedBall a r, infDist y K < r/4) :
    Metric.ball a (r/4) ⊆ K := by
  intro x hx
  by_contra hxn
  obtain ⟨f,s,hsep,hfx⟩ := geometric_hahn_banach_closed_point hcv hcl hxn
  have hf : 0 < ‖f‖ := by
    apply norm_pos_iff.mpr
    intro he
    obtain ⟨z,hz⟩ := hne
    have hh := (hsep z hz).trans hfx
    simp [he] at hh
  obtain ⟨v,hv,hfv⟩ := f.exists_lt_apply_of_lt_opNorm (show ‖f‖/2 < ‖f‖ by linarith)
  obtain ⟨v,hv,hfv⟩ : ∃ v : E, ‖v‖ < 1 ∧ ‖f‖/2 < f v := by
    by_cases hh : 0 ≤ f v
    · exact ⟨v,hv,by simpa only [Real.norm_eq_abs,abs_of_nonneg hh] using hfv⟩
    · exact ⟨-v,by simpa using hv,by simpa only [map_neg,Real.norm_eq_abs,abs_of_neg (lt_of_not_ge hh)] using hfv⟩
  let y := a+r • v
  have hy : y ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    simpa only [y,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_one]
      using (mul_le_mul_of_nonneg_left hv.le hr.le)
  obtain ⟨z,hz,hyz⟩ := (infDist_lt_iff hne).mp (happ y hy)
  have hyz' : ‖y-z‖ < r/4 := by simpa only [dist_eq_norm] using hyz
  have hx' : ‖x-a‖ < r/4 := by simpa only [Metric.mem_ball,dist_eq_norm] using hx
  have hfxy : f y-f x ≤ ‖f‖*‖y-z‖ := by
    have hb : f y-f z ≤ ‖f‖*‖y-z‖ := by
      rw [← map_sub]
      exact (le_abs_self _).trans (f.le_opNorm (y-z))
    linarith [hsep z hz]
  have hfxa : f x-f a ≤ ‖f‖*‖x-a‖ := by
    rw [← map_sub]
    exact (le_abs_self _).trans (f.le_opNorm (x-a))
  have hfy : f y = f a+r*f v := by simp only [y,map_add,map_smul,smul_eq_mul]
  have h1 := mul_lt_mul_of_pos_left hyz' hf
  have h2 := mul_lt_mul_of_pos_left hx' hf
  have h3 := mul_lt_mul_of_pos_left hfv hr
  nlinarith

theorem LocalDistanceConverges.eventually_normed_ball_subset
    {Cj : ℕ → Set E} {C : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {a : E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall a r ⊆ C) :
    ∀ᶠ j in atTop, Metric.ball a (r/4) ⊆ Cj j := by
  have hU := tendstoLocallyUniformly_iff_forall_isCompact.mp h (Metric.closedBall a r)
    (isCompact_closedBall a r)
  have he := Metric.tendstoUniformlyOn_iff.mp hU (r/4) (by positivity)
  filter_upwards [he] with j hj
  apply normed_ball_subset_of_infDist_lt (hclj j) (hcvj j) (hnej j) a hr
  intro y hy
  have he := hj y hy
  rw [infDist_zero_of_mem (hball hy),dist_zero_left,Real.norm_eq_abs,
    abs_of_nonneg infDist_nonneg] at he
  exact he

end AffineBernstein
end

end OAI
