import OAI.Analysis.BernoulliCone.SmoothIntervalPrimitive

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def clampedHeight (u σ v:E→ℝ) (x:E):ℝ:=max (u x) (min (v x) (σ x))
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma le_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u σ v:E→ℝ) (x:E):u x≤clampedHeight u σ v x:=le_max_left _ _
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma clampedHeight_le [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} (h:u x≤v x):clampedHeight u σ v x≤v x:=
  max_le h (min_le_left _ _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma below_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} {t:ℝ}
    (hl:u x<t) (ht:t<clampedHeight u σ v x):t<σ x := by
  have hh:=lt_max_iff.mp ht
  rcases hh with h|h
  · exact False.elim ((not_lt.mpr hl.le) h)
  · exact h.trans_le (min_le_right _ _)
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma above_clampedHeight [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u σ v:E→ℝ} {x:E} {t:ℝ}
    (hu:clampedHeight u σ v x<t) (ht:t<v x):σ x<t := by
  have hh:min (v x) (σ x)<t:=(le_max_right _ _).trans_lt hu
  exact (min_lt_iff.mp hh).resolve_left (not_lt.mpr ht.le)

omit [FiniteDimensional ℝ E] in
lemma graphPotential_eq_integral [FiniteDimensional ℝ E]
    {A:E×ℝ→E} (hA:Continuous A) (u v:E→ℝ) (x:E) :
    graphPotential A u v x=(2:ℝ) • (∫s in u x..v x,A (x,s)) := by
  have hc:Continuous (fun s:ℝ=>A (x,s)):=hA.comp (continuous_const.prodMk continuous_id)
  unfold graphPotential ParametricIntegral.heightPrimitive
  rw [←intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 (v x))
    (hc.intervalIntegrable 0 (u x))]

lemma clamped_integral_identity {F A B:E×ℝ→E} (hA:Continuous A) (hB:Continuous B)
    {u σ v:E→ℝ} {x:E} (huv:u x≤v x)
    (hFi:∀a b:ℝ,IntervalIntegrable (fun t:ℝ=>F (x,t)) volume a b)
    (hAe:∀t∈Ioo (u x) (v x),t<σ x → F (x,t)=A (x,t))
    (hBe:∀t∈Ioo (u x) (v x),σ x<t → F (x,t)=B (x,t)) :
    (2:ℝ) • (∫s in u x..v x,F (x,s))=
      splitGraphPotential A B u (clampedHeight u σ v) v x := by
  let w:=clampedHeight u σ v x
  have huw:u x≤w:=le_clampedHeight u σ v x
  have hwv:w≤v x:=clampedHeight_le huv
  have heA:(∫s in u x..w,F (x,s))=∫s in u x..w,A (x,s):=
    intervalIntegral.integral_congr_Ioo_of_le huw (fun t ht=>hAe t ⟨ht.1,ht.2.trans_le hwv⟩
      (below_clampedHeight ht.1 ht.2))
  have heB:(∫s in w..v x,F (x,s))=∫s in w..v x,B (x,s):=
    intervalIntegral.integral_congr_Ioo_of_le hwv (fun t ht=>hBe t ⟨huw.trans_lt ht.1,ht.2⟩
      (above_clampedHeight ht.1 ht.2))
  rw [splitGraphPotential,graphPotential_eq_integral hA,graphPotential_eq_integral hB]
  rw [←intervalIntegral.integral_add_adjacent_intervals (hFi (u x) w) (hFi w (v x)),heA,heB,smul_add]

lemma integrated_bulk_open {A:E×ℝ→E} (hA:ContDiff ℝ 1 A) (x:E) {a b:ℝ} (hab:a≤b)
    (hbulk:∀s∈Ioo a b,divergence (fun y:E=>A (y,s)) x+
      inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)≤0) :
    2*(∫s in a..b,divergence (fun y:E=>A (y,s)) x)≤‖A (x,a)‖^2-‖A (x,b)‖^2 := by
  rcases hab.eq_or_lt with he|hlt
  · subst b; simp
  · apply integrated_bulk hA x hab
    have hAC:ContDiff ℝ 1 (fun s:ℝ=>A (x,s)):=hA.comp (contDiff_const.prodMk contDiff_id)
    have hc:Continuous (fun s:ℝ=>divergence (fun y:E=>A (y,s)) x+
        inner ℝ (A (x,s)) (deriv (fun t:ℝ=>A (x,t)) s)):=
      (continuous_spatial_divergence hA x).add (hAC.continuous.inner (hAC.continuous_deriv (by norm_num)))
    exact fun s hs=>le_on_closure hbulk hc.continuousOn continuousOn_const (by rwa [closure_Ioo hlt.ne])

lemma graphPotential_locallyLipschitz {A:E×ℝ→E} (hA:ContDiff ℝ 1 A)
    {u v:E→ℝ} (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) :
    LocallyLipschitz (graphPotential A u v) := by
  have hh:= (ParametricIntegral.heightPrimitive_contDiff_one hA).locallyLipschitz
  exact ((2:ℝ) • ContinuousLinearMap.id ℝ E).lipschitzWith.locallyLipschitz.comp
    ((hh.comp (LocallyLipschitz.id.prodMk hv)).sub (hh.comp (LocallyLipschitz.id.prodMk hu)))

lemma clamped_split_locallyLipschitz {A B:E×ℝ→E} (hA:ContDiff ℝ 1 A) (hB:ContDiff ℝ 1 B)
    {u σ v:E→ℝ} (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (hσ:LocallyLipschitz σ) :
    LocallyLipschitz (splitGraphPotential A B u (clampedHeight u σ v) v) := by
  have hw:LocallyLipschitz (clampedHeight u σ v):=hu.max (hv.min hσ)
  exact (graphPotential_locallyLipschitz hA hu hw).add (graphPotential_locallyLipschitz hB hw hv)
end Bernoulli.Foliation

end
end

end OAI
