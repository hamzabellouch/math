import Mathlib
import OAI.Probability.SKValue.Gaussian.DensityDerivative
import OAI.Probability.SKValue.Coercivity.Coercivity

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue

lemma integral_flux_zero {f g:ℝ → ℝ} (hc:ContinuousAt f 0)
    (hd:∀ x:ℝ,x≠0 → HasDerivAt f (g x) x) (hf:Integrable f) (hg:Integrable g) :
    (∫ x,g x)=0 := by
  have ht:Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a:=0)
      (fun x hx ↦ hd x (ne_of_gt hx)) hg.integrableOn hf.integrableOn
  have hb:Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a:=(-1:ℝ))
      (fun x hx ↦ hd x (by change x≤(-1:ℝ) at hx;linarith)) hg.integrableOn hf.integrableOn
  rw [←setIntegral_univ,←Iic_union_Ioi (a:=(0:ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hg.integrableOn hg.integrableOn,
    integral_Iic_of_hasDerivAt_of_tendsto hc.continuousWithinAt
      (fun x hx ↦ hd x (ne_of_lt hx)) hg.integrableOn hb,
    integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt
      (fun x hx ↦ hd x (ne_of_gt hx)) hg.integrableOn ht]
  ring

lemma ExpGrowth.zero_mul_continuousAt {F r f:ℝ → ℝ} (hF:ExpGrowth F)
    (hr:ContinuousAt r 0) (hr0:r 0=0) (hf:ContinuousAt f 0) :
    ContinuousAt (fun x ↦ r x*F x*f x) 0 := by
  obtain ⟨a,C,ha,hC,hb⟩ := hF
  have hh:Tendsto (fun x ↦ |r x| *(C*Real.exp (a*|x|))*|f x|) (𝓝 0) (𝓝 0) := by
    have he : Continuous (fun x:ℝ ↦ C*Real.exp (a*|x|)) := by fun_prop
    have hc : ContinuousAt (fun x:ℝ ↦ |r x| *(C*Real.exp (a*|x|))*|f x|) 0 :=
      (hr.abs.mul he.continuousAt).mul hf.abs
    simpa only [hr0,abs_zero,zero_mul] using hc.tendsto

  have hz:Tendsto (fun x ↦ r x*F x*f x) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall (fun x ↦ ?_)) hh
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)) (abs_nonneg _)
  simpa only [ContinuousAt,hr0,zero_mul] using hz
end SKValue

end

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue

lemma ExpGrowth.div_odd_monotone {g r:ℝ → ℝ} {g' r':ℝ}
    (hg:ExpGrowth g) (hg0:g 0=0) (hr0:r 0=0)
    (hdg:HasDerivAt g g' 0) (hdr:HasDerivAt r r' 0) (hr':0<r')
    (hodd:∀ x,r (-x)= -r x) (hmono:Monotone r) (hpos:∀ x,0<x → 0<r x) :
    ExpGrowth (fun x ↦ g x/r x) := by
  have ht:Tendsto (fun x ↦ g x/r x) (𝓝[≠] 0) (𝓝 (g'/r')) := by
    have hgsl:=hdg.tendsto_slope_zero
    have hrsl:=hdr.tendsto_slope_zero
    simp only [zero_add,hg0,hr0,sub_zero,smul_eq_mul] at hgsl hrsl
    apply (hgsl.div hrsl hr'.ne').congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0:x≠0 := by simpa using hx
    change (x⁻¹*g x)/(x⁻¹*r x)=g x/r x
    field_simp
  obtain ⟨K,hK⟩ := ht.abs.isBoundedUnder_le
  have hn:∀ᶠ x in 𝓝 (0:ℝ),x≠0 → |g x/r x|≤K := by
    exact eventually_nhdsWithin_iff.mp hK
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp hn
  let δ:=ε/2
  have hδ:0<δ := by dsimp [δ];linarith
  have hrδ:0<r δ := hpos δ hδ
  obtain ⟨a,C,ha,hC,hb⟩ := hg
  refine ⟨a,max (max K 0) (C/r δ),ha,le_trans (le_max_right K 0) (le_max_left _ _),?_⟩
  intro x
  by_cases hx:|x|<δ
  · have hnear:|g x/r x|≤ max K 0 := by
      by_cases hx0:x=0
      · subst x;simp [hg0]
      · exact (he (by simpa only [Real.dist_eq,sub_zero] using hx.trans (by dsimp [δ];linarith)) hx0).trans (le_max_left _ _)
    exact hnear.trans ((le_max_left _ _).trans (le_mul_of_one_le_right
      (le_trans (le_max_right K 0) (le_max_left _ _)) (Real.one_le_exp (mul_nonneg ha (abs_nonneg x)))))
  · have haway:r δ≤|r x| := by
      rw [not_lt] at hx
      by_cases hs:0≤x
      · rw [abs_of_nonneg hs] at hx
        exact (hmono hx).trans (le_abs_self _)
      · have hxs:x<0 := lt_of_not_ge hs
        rw [abs_of_neg hxs] at hx
        have hm:=hmono hx
        rw [hodd] at hm
        exact hm.trans (neg_le_abs _)
    have hbound:|g x/r x|≤(C/r δ)*Real.exp (a*|x|) := by
      rw [abs_div]
      calc
        _ ≤ (C*Real.exp (a*|x|))/(r δ) :=
          div_le_div₀ (mul_nonneg hC (Real.exp_pos _).le) (hb x) hrδ haway
        _ = _ := by ring
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
end SKValue

end

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue.Certificate
lemma integral_W_zero {r v w z s a d f:ℝ → ℝ}
    (hr:∀ x,HasDerivAt r (v x) x) (hv:∀ x,HasDerivAt v (w x) x)
    (hw:∀ x,HasDerivAt w (z x) x) (hs:∀ x,HasDerivAt s (a x) x)
    (ha:∀ x,HasDerivAt a (d x) x) (hf:∀ x,HasDerivAt f ((r x-s x)*f x) x)
    (hz:Measurable z) (hd:Measurable d) (hr0:r 0=0) (hrn:∀ x,x≠0 → r x≠0)
    (hgr:ExpGrowth r) (hgv:ExpGrowth v) (hgz:ExpGrowth z) (hgs:ExpGrowth s)
    (_:ExpGrowth a) (hgd:ExpGrowth d) (hgb:ExpGrowth (fun x ↦ -w x/r x))
    (hgj:ExpGrowth (fun x ↦ a x-s x/r x*v x))
    (hint:∀ F:ℝ → ℝ,ExpGrowth F → Measurable F → Integrable (fun x ↦ F x*f x)) :
    (∫ x,W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)*f x)=0 := by
  have hmr:Measurable r := (continuous_iff_continuousAt.mpr (fun x ↦ (hr x).continuousAt)).measurable
  have hmv:Measurable v := (continuous_iff_continuousAt.mpr (fun x ↦ (hv x).continuousAt)).measurable
  have hmw:Measurable w := (continuous_iff_continuousAt.mpr (fun x ↦ (hw x).continuousAt)).measurable
  have hms:Measurable s := (continuous_iff_continuousAt.mpr (fun x ↦ (hs x).continuousAt)).measurable
  have hma:Measurable a := (continuous_iff_continuousAt.mpr (fun x ↦ (ha x).continuousAt)).measurable
  have hF:=growth_F (hgr.pow 2) (hgr.mul hgs) hgv hgb hgj
  have hW:=growth_W (hgr.pow 2) (hgr.mul hgs) hgv hgb hgj hgz (hgr.neg.mul hgd)
  have hmF:Measurable (fun x ↦ F₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)) := by
    unfold F₂;fun_prop
  have hmW:Measurable (fun x ↦ W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)) := by unfold W₂ F₂;fun_prop
  exact integral_flux_zero (hF.zero_mul_continuousAt (hr 0).continuousAt hr0 (hf 0).continuousAt)
    (fun x hx ↦ flux_derivative (hr x) (hv x) (hw x) (hs x) (ha x) (hf x) (hrn x hx))
    (hint _ (hgr.mul hF) (hmr.mul hmF)) (hint _ hW hmW)

lemma ForwardDensityData.integrable_density_factor (D:ForwardDensityData)
    {A F:ℝ → ℝ} (hA:SmoothTerminal A) {c:ℝ} (hc:0≤c)
    (hF:ExpGrowth F) (hm:Measurable F) :
    Integrable (fun x ↦ F x*(Real.exp (c*A x)*D.weight x)) := by
  have hi:=D.weight_exp_integrable (hF.mul (ExpGrowth.exp_lipschitz hA.lipschitz hc))
    (hm.mul ((measurable_const.mul hA.smooth.continuous.measurable).exp))
  convert! hi using 1
  funext x;ring
end SKValue.Certificate

end

end OAI
