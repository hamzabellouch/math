import Mathlib
import OAI.Analysis.SymmetricDomains.ContinuousFderivLocallyUniform
import OAI.Analysis.SymmetricDomains.IterateAverageCoboundary

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

lemma iterateAverage_coboundary_tendsto {S : Set E} {f : E → E}
    (hm : MapsTo f S S) {M : ℝ} (hb : ∀ x ∈ S, ‖x‖ ≤ M)
    {x : E} (hx : x ∈ S) :
    Tendsto (fun N => iterateAverage f N (f x)-iterateAverage f N x) atTop (𝓝 0) := by
  have he : ∀ N : ℕ, ‖iterateAverage f N (f x)-iterateAverage f N x‖ ≤
      (N+1 : ℝ)⁻¹*(2*M) := by
    intro N
    rw [iterateAverage_coboundary,norm_smul,norm_inv]
    rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
    simp only [Nat.cast_add,Nat.cast_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_sub_le _ _).trans (by linarith [hb _ ((hm.iterate (N+1)) hx),hb x hx])
  apply squeeze_zero_norm he
  have hlim : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    by
      have ht := tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1))
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using ht
  simpa using hlim.mul_const (2*M)

theorem cartan_uniqueness_bounded [ProperSpace E] [SecondCountableTopology E]
    {S : Set E} (hS : IsOpen S) (hconn : IsPreconnected S)
    (hb : Bornology.IsBounded S) {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S)
    {p : E} (hp : p ∈ S) (hfix : f p = p)
    (hd : HasFDerivAt f (1 : E →L[ℂ] E) p) : EqOn f id S := by
  obtain ⟨M,hM,hbM⟩ := hb.exists_pos_norm_le
  obtain ⟨g,hg,φ,hφ,hconv⟩ := montel_expanding_domains hS (iterateAverage f) (by
    intro x hx
    obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
    exact ⟨r,hr,M,hM,hrs,Eventually.of_forall (fun N =>
      ⟨(iterateAverage_analytic hf hm N).differentiableOn.mono hrs,
        fun y hy => iterateAverage_bound hm hbM N (hrs hy)⟩)⟩)
  have hhol : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (iterateAverage f (φ j)) W := by
    intro x hx
    exact ⟨S,hS.mem_nhds hx,Eventually.of_forall (fun j => iterateAverage_analytic hf hm (φ j))⟩
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (iterateAverage f (φ j)) W := by
    intro x hx
    obtain ⟨W,hW,hw⟩ := hhol x hx
    exact ⟨W,hW,hw.mono (fun _ hj => hj.differentiableOn)⟩
  have hder : fderiv ℂ g p = 1 := by
    have ht := (tendstoLocallyUniformlyOn_fderiv hS hconv hdiff).tendsto_at hp
    have he : (fun j => fderiv ℂ (iterateAverage f (φ j)) p) = fun _ : ℕ => 1 := by
      funext j
      exact (iterateAverage_deriv_fixed hfix hd (φ j)).fderiv
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hstrict : HasStrictFDerivAt g (1 : E →L[ℂ] E) p := by
    rw [← hder]
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [hS.mem_nhds hp] with x hx
      exact (hg.differentiableAt (hS.mem_nhds hx)).hasFDerivAt
    · exact continuousAt_fderiv_of_locally_uniform_analytic hS hconv hhol hp
  have hgf : EqOn (g ∘ f) g S := by
    intro x hx
    have ht := ((hconv.tendsto_at (hm hx)).sub (hconv.tendsto_at hx))
    have hz := (iterateAverage_coboundary_tendsto hm hbM hx).comp hφ.tendsto_atTop
    exact sub_eq_zero.mp (tendsto_nhds_unique ht hz)
  have hleft := (show HasStrictFDerivAt g
    ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) p from by simpa only [ContinuousLinearEquiv.coe_refl,ContinuousLinearMap.one_def] using hstrict).eventually_left_inverse
  have hfc : Tendsto f (𝓝 p) (𝓝 p) := by
    simpa only [hfix] using (hf p hp).continuousAt.tendsto
  have heq : f =ᶠ[𝓝 p] id := by
    filter_upwards [hleft,hfc hleft,hS.mem_nhds hp] with x hx hfx hxs
    simp only [Set.mem_preimage,Set.mem_ofPred_eq] at hfx
    rw [show g (f x) = g x from hgf hxs] at hfx
    exact hfx.symm.trans hx
  exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hconn hp heq

end Release061

end

end OAI
