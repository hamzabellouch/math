import Mathlib
import OAI.Analysis.SymmetricDomains.CartanUniqueness
import OAI.Analysis.SymmetricDomains.FiniteNashCoverVertical

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma iterateAverage_sub_id_bound {f : E → E} {T : Set E} {ε : ℝ}
    (he : ∀ j : ℕ, ∀ x ∈ T, ‖f^[j] x-x‖ ≤ ε) (N : ℕ) {x : E} (hx : x ∈ T) :
    ‖iterateAverage f N x-x‖ ≤ ε := by
  have hn : (N+1 : ℝ) ≠ 0 := by positivity
  have hnC : (N+1 : ℂ) ≠ 0 := by exact_mod_cast hn
  have heq : iterateAverage f N x-x =
      (N+1 : ℂ)⁻¹ • ∑ j ∈ Finset.range (N+1), (f^[j] x-x) := by
    rw [Finset.sum_sub_distrib,smul_sub]
    simp only [Finset.sum_const,Finset.card_range,← Nat.cast_smul_eq_nsmul ℂ,
      Nat.cast_add,Nat.cast_one,smul_smul,inv_mul_cancel₀ hnC,one_smul,iterateAverage]
  rw [heq,norm_smul,norm_inv]
  rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by push_cast; rfl,Complex.norm_natCast]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    ((N : ℝ)+1)⁻¹ * ‖∑ j ∈ Finset.range (N+1), (f^[j] x-x)‖ ≤
        ((N : ℝ)+1)⁻¹ * ∑ j ∈ Finset.range (N+1), ‖f^[j] x-x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((N : ℝ)+1)⁻¹ * ∑ _j ∈ Finset.range (N+1), ε := by
      gcongr with j hj
      exact he j x hx
    _ = ε := by simp [hn]

theorem holomorphic_near_id_injective {g : E → E} {p : E} {R : ℝ}
    (hR : 0 < R) (hg : DifferentiableOn ℂ g (ball p R))
    (hb : ∀ x ∈ ball p R, ‖g x-x‖ ≤ R/16) : InjOn g (ball p (R/4)) := by
  intro x hx y hy hxy
  let h : E → E := fun z => g z-z
  have hsub : ball x (R/2) ⊆ ball p R := by
    intro z hz
    rw [mem_ball] at *
    exact (dist_triangle z x p).trans_lt (by linarith)
  have hdiff : DifferentiableOn ℂ h (ball x (R/2)) :=
    (hg.sub differentiableOn_id).mono hsub
  have hm : MapsTo h (ball x (R/2)) (closedBall (h x) (R/8)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by
      have hz' := hb z (hsub hz)
      have hx' := hb x (ball_subset_ball (by linarith) hx)
      dsimp [h]
      linarith)
  have hyx : y ∈ ball x (R/2) := by
    rw [mem_ball] at *
    exact (dist_triangle y p x).trans_lt (by rw [dist_comm p x]; linarith)
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hm hyx
  have he : h y-h x=x-y := by dsimp [h]; rw [← hxy]; abel
  rw [dist_eq_norm,he,← dist_eq_norm,dist_comm x y] at hs
  have hc : (R/8)/(R/2)=(1/4 : ℝ) := by field_simp; ring
  rw [hc] at hs
  exact dist_eq_zero.mp (by linarith [dist_nonneg (x := y) (y := x)]) |>.symm

theorem holomorphic_eq_id_of_small_iterates [ProperSpace E] [SecondCountableTopology E]
    {S : Set E} (hS : IsOpen S) (hc : IsPreconnected S) (hb : Bornology.IsBounded S)
    {f : E → E} (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S)
    {p : E} {R : ℝ} (hR : 0 < R) (hball : ball p R ⊆ S)
    (he : ∀ j : ℕ, ∀ x ∈ ball p R, ‖f^[j] x-x‖ ≤ R/16) : EqOn f id S := by
  obtain ⟨M,hM,hbM⟩ := hb.exists_pos_norm_le
  obtain ⟨g,hg,φ,hφ,hconv⟩ := montel_expanding_domains hS (iterateAverage f) (by
    intro x hx
    obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
    exact ⟨r,hr,M,hM,hrs,Eventually.of_forall (fun N =>
      ⟨(iterateAverage_analytic hf hm N).differentiableOn.mono hrs,
        fun y hy => iterateAverage_bound hm hbM N (hrs hy)⟩)⟩)
  have hnear : ∀ x ∈ ball p R, ‖g x-x‖ ≤ R/16 := by
    intro x hx
    apply le_of_tendsto ((hconv.tendsto_at (hball hx)).sub_const x).norm
    exact Eventually.of_forall (fun j => iterateAverage_sub_id_bound he (φ j) hx)
  have hinj := holomorphic_near_id_injective hR (hg.mono hball) hnear
  have hgf : EqOn (g ∘ f) g S := by
    intro x hx
    have ht := ((hconv.tendsto_at (hm hx)).sub (hconv.tendsto_at hx))
    have hz := (iterateAverage_coboundary_tendsto hm hbM hx).comp hφ.tendsto_atTop
    exact sub_eq_zero.mp (tendsto_nhds_unique ht hz)
  have heq : f =ᶠ[𝓝 p] id := by
    filter_upwards [ball_mem_nhds p (show 0 < R/8 by positivity)] with x hx
    have hxR : x ∈ ball p R := ball_subset_ball (by linarith) hx
    have hsmall : ‖f x-x‖ ≤ R/16 := by simpa using he 1 x hxR
    have hfx : f x ∈ ball p (R/4) := by
      rw [mem_ball]
      have hx' : dist x p < R/8 := hx
      exact (dist_triangle (f x) x p).trans_lt (by rw [dist_eq_norm (f x) x]; linarith)
    exact hinj hfx (ball_subset_ball (by linarith) hx) (hgf (hball hxR))
  exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hc
    (hball (mem_ball_self hR)) heq

end Release061

end

end OAI
