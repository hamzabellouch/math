import Mathlib
import OAI.Analysis.BiholderTransport.Contact.SubgradientDifferential
import OAI.Analysis.BiholderTransport.Coordinates.Taylor

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section AlexandrovDerivative
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma semiconvex_selection_hasFDerivWithinAt {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0<R) (K : ℝ)
    {s : Set E} {g : E → E} (hg0 : g 0=p)
    (hg : ∀ z∈s, IsSemiconvexSubgradientOn f (Metric.ball 0 R) K z (g z)) :
    HasFDerivWithinAt g A s 0 := by
  rw [hasFDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff]
  intro eps heps
  obtain ⟨d,hd,H⟩ := semiconvex_subgradient_uniform_differential hA hexp hR K eps heps
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:E) hd)]
      with z hz hzd
  simpa only [sub_zero,hg0] using H z (g z)
    (by simpa only [Metric.mem_ball,dist_zero_right] using hzd) (hg z hz)
variable [CompleteSpace E]

lemma gradient_subgradient_on {f : E → ℝ} {s : Set E}
    (hc : ConvexOn ℝ s f) {x : E} (hx : x∈s)
    {f' : E →L[ℝ] ℝ} (hder : HasFDerivAt f f' x) :
    IsSubgradientOn f s x ((InnerProductSpace.toDual ℝ E).symm f') := by
  intro v hv
  rw [InnerProductSpace.toDual_symm_apply]
  have hd : HasDerivAt (fun t : ℝ => f (x+t • (v-x))) (f' (v-x)) 0 := by
    have hp : HasDerivAt (fun t : ℝ => x+t • (v-x)) (v-x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (v-x)).const_add x
    exact (show HasFDerivAt f f' (x+(0:ℝ) • (v-x)) from by simpa using hder).comp_hasDerivAt 0 hp
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      t⁻¹*(f (x+t • (v-x))-f x)≤f v-f x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have hcv := hc.2 hx hv (by linarith [ht.2] : 0≤1-t) ht.1.le (by ring : 1-t+t=1)
    have heq : (1-t) • x+t • v=x+t • (v-x) := by
      simp only [sub_smul,one_smul,smul_sub]; abel
    rw [heq] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_eq_div,div_le_iff₀ ht.1]
    nlinarith
  have ht : Tendsto (fun t : ℝ => t⁻¹*(f (x+t • (v-x))-f x))
      (𝓝[>] 0) (𝓝 (f' (v-x))) := by
    simpa only [zero_add,zero_smul,add_zero,smul_eq_mul] using hd.tendsto_slope_zero_right
  have H := le_of_tendsto ht hb
  linarith

lemma gradient_semiconvex_subgradient_on {f : E → ℝ} {s : Set E} {K : ℝ}
    (hc : ConvexOn ℝ s (fun z => f z+K/2*‖z‖^2)) {x : E} (hx : x∈s)
    (hd : DifferentiableAt ℝ f x) :
    IsSemiconvexSubgradientOn f s K x
      ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) := by
  rw [semiconvex_subgradient_iff]
  have hq := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (K/2))
  have h := gradient_subgradient_on hc hx (hd.hasFDerivAt.add hq)
  convert h using 1
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]
  ext z
  simp only [add_apply,smul_apply,
    InnerProductSpace.toDual_apply_apply,innerSL_apply_apply,smul_eq_mul]
  ring

lemma semiconvex_gradient_hasFDerivWithinAt {f : E → ℝ} {p : E}
    {A : E →L[ℝ] E} (hA : ∀ x y, inner ℝ (A x) y=inner ℝ x (A y))
    (hexp : HasQuadraticExpansion f p A) {R : ℝ} (hR : 0<R) {K : ℝ}
    (hc : ConvexOn ℝ (Metric.ball 0 R) (fun z => f z+K/2*‖z‖^2)) :
    HasFDerivWithinAt (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)) A
      {z | z∈Metric.ball 0 R ∧ DifferentiableAt ℝ f z} 0 := by
  apply semiconvex_selection_hasFDerivWithinAt hA hexp hR K
  · rw [hexp.hasFDerivAt.fderiv]
    exact (InnerProductSpace.toDual ℝ E).symm_apply_apply p
  · intro z hz
    exact gradient_semiconvex_subgradient_on hc hz.1 hz.2
end AlexandrovDerivative
end WeakMTWTransport

end

end

end

end OAI
