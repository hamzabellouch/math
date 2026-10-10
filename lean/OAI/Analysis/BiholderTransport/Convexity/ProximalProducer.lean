import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SubgradientDifferential

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma lower_contact_subgradient_on {f g : E → ℝ} {s : Set E}
    (hc : ConvexOn ℝ s f) {x : E} (hx : x∈s)
    {g' : E →L[ℝ] ℝ} (hg : HasFDerivAt g g' x)
    (heq : g x=f x) (hle : g≤ᶠ[𝓝 x]f) :
    IsSubgradientOn f s x ((InnerProductSpace.toDual ℝ E).symm g') := by
  intro v hv
  rw [InnerProductSpace.toDual_symm_apply]
  have hp : HasDerivAt (fun t : ℝ => x+t • (v-x)) (v-x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v-x)).const_add x
  have hd : HasDerivAt (fun t : ℝ => g (x+t • (v-x))) (g' (v-x)) 0 := by
    exact (show HasFDerivAt g g' (x+(0:ℝ) • (v-x)) from by simpa using hg).comp_hasDerivAt 0 hp
  have htend : Tendsto (fun t : ℝ => x+t • (v-x)) (𝓝[>]0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ t : ℝ in 𝓝[>]0,
      t⁻¹*(g (x+t • (v-x))-g x)≤f v-f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),htend.eventually hle] with t ht htf
    have hcv := hc.2 hx hv (by linarith [ht.2] : 0≤1-t) ht.1.le (by ring : 1-t+t=1)
    have he : (1-t) • x+t • v=x+t • (v-x) := by
      simp only [sub_smul,one_smul,smul_sub]; abel
    rw [he] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div,div_le_iff₀ ht.1,heq]
    nlinarith only [hcv,htf]
  have hlim : Tendsto (fun t : ℝ => t⁻¹*(g (x+t • (v-x))-g x))
      (𝓝[>]0) (𝓝 (g' (v-x))) := by
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul] using hd.tendsto_slope_zero_right
  have H := le_of_tendsto hlim hb
  linarith only [H]

lemma lower_contact_semiconvex_subgradient_on {f g : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    {g' : E →L[ℝ] ℝ} (hg : HasFDerivAt g g' x)
    (heq : g x=f x) (hle : g≤ᶠ[𝓝 x]f) :
    IsSemiconvexSubgradientOn f s K x ((InnerProductSpace.toDual ℝ E).symm g') := by
  rw [semiconvex_subgradient_iff]
  have hq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (K/2)
  have hh : (fun z => g z+K/2*‖z‖^2)≤ᶠ[𝓝 x](fun z => f z+K/2*‖z‖^2) := by
    filter_upwards [hle] with z hz
    linarith only [hz]
  have h := lower_contact_subgradient_on hc hx (hg.add hq) (by simp only [Pi.add_apply,heq]) hh
  convert h using 1
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]
  ext z
  simp only [add_apply,smul_apply,
    InnerProductSpace.toDual_apply_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma kernel_minimum_semiconvex_subgradient {f k : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    {k' : E →L[ℝ] ℝ} (hk : HasFDerivAt k k' x)
    (hmin : ∀ᶠ y in 𝓝 x, f x+k x≤f y+k y) :
    IsSemiconvexSubgradientOn f s K x ((InnerProductSpace.toDual ℝ E).symm (-k')) := by
  apply lower_contact_semiconvex_subgradient_on hc hx
    (hk.neg.const_add (f x+k x)) (by simp only [Pi.neg_apply]; ring)
  filter_upwards [hmin] with y hy
  simp only [Pi.neg_apply]
  linarith only [hy]

omit [CompleteSpace E] in
lemma semiconvex_subgradient_eq_at_expansion {f : E → ℝ} {x p ξ : E}
    {A : E →L[ℝ] E} (hA : ∀ v w,inner ℝ (A v) w=inner ℝ v (A w))
    (hexp : HasQuadraticExpansion (fun h => f (x+h)) p A)
    {r : ℝ} (hr : 0 < r) (K : ℝ)
    (hsub : IsSemiconvexSubgradientOn f (Metric.ball x r) K x ξ) : ξ=p := by
  obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hr K 1 zero_lt_one
  have hh := H 0 ξ (by simpa using hd) (by
    intro w hw
    have hw' : x+w∈Metric.ball x r := by
      simpa only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hw
    simpa only [add_zero,sub_zero,add_sub_cancel_left] using hsub (x+w) hw')
  have hn : ‖ξ-p‖≤0 := by simpa only [map_zero,sub_zero,norm_zero,mul_zero] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
end WeakMTWTransport

end

end OAI
