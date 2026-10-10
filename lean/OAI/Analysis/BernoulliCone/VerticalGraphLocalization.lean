import OAI.Analysis.BernoulliCone.ClampedFoliationGraph

namespace OAI

universe uE

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.Foliation
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma real_interval_combination {a b s:ℝ} (hab:a≤b) (hs:s∈Icc a b) :
    ∃t∈Icc (0:ℝ) 1,s=(1-t)*a+t*b := by
  rcases hab.eq_or_lt with he|hl
  · subst b
    exact ⟨0,by norm_num,by have hh:=le_antisymm hs.2 hs.1; simpa using hh⟩
  · refine ⟨(s-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hl).le,?_⟩,?_⟩
    · exact (div_le_one (sub_pos.mpr hl)).mpr (sub_le_sub_right hs.2 a)
    · field_simp; ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma eventually_vertical_segment [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u v:E→ℝ} {x:E} (hu:ContinuousAt u x) (hv:ContinuousAt v x)
    (huv:u x≤v x) {V:Set (E×ℝ)} (hV:V∈𝓝ˢ ({x}×ˢ Icc (u x) (v x))) :
    ∀ᶠ y in 𝓝 x,u y≤v y → ∀s∈Icc (u y) (v y),(y,s)∈V := by
  have hh:∀ᶠ y in 𝓝 x,∀t∈Icc (0:ℝ) 1,(y,(1-t)*u y+t*v y)∈V:=by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc:ContinuousAt (fun p:E×ℝ=>(p.1,(1-p.2)*u p.1+p.2*v p.1)) (x,t):=by
      exact continuous_fst.continuousAt.prodMk
        (((continuousAt_const.sub continuous_snd.continuousAt).mul (hu.comp continuous_fst.continuousAt)).add
          (continuous_snd.continuousAt.mul (hv.comp continuous_fst.continuousAt)))
    have hp:(x,(1-t)*u x+t*v x)∈({x}×ˢ Icc (u x) (v x)):=by
      refine ⟨rfl,?_,?_⟩
      · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr huv)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr huv)]
    exact hc.eventually ((nhds_le_nhdsSet hp) hV)
  filter_upwards [hh] with y hy hyuv s hs
  obtain ⟨t,ht,rfl⟩:=real_interval_combination hyuv hs
  exact hy t ht

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma locallyLipschitz_germ [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F Q:E→E} {x:E} (hQ:LocallyLipschitz Q) (he:F =ᶠ[𝓝 x] Q) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K F V := by
  obtain ⟨K,V,hV,hL⟩:=hQ x
  refine ⟨K,V∩{y|F y=Q y},inter_mem hV he,?_⟩
  intro y hy z hz
  rw [hy.2,hz.2]
  exact hL hy.1 hz.1

/-- Primitive of the actual field between two graphs; no assigned derivative. -/
def verticalPotential (F:E×ℝ→E) (u v:E→ℝ) (x:E):E:=(2:ℝ) • (∫s in u x..v x,F (x,s))

lemma verticalPotential_smooth_germ {F:E×ℝ→E} {u v:E→ℝ}
    (hu:LocallyLipschitz u) (hv:LocallyLipschitz v) (huv:∀y,u y≤v y) {x:E}
    {D:Set (E×ℝ)} (hD:IsOpen D) (hFD:ContDiffOn ℝ 1 F D)
    (hK:({x}×ˢ Icc (u x) (v x))⊆D)
    (_hFi:∀y a b,IntervalIntegrable (fun t:ℝ=>F (y,t)) volume a b) :
    ∃K:ℝ≥0,∃V∈𝓝 x,LipschitzOnWith K (verticalPotential F u v) V := by
  obtain ⟨A,hA,hAe⟩:=LocalExtension.exists_contDiff_extension
    (isCompact_singleton.prod isCompact_Icc) hD hK hFD
  have hn:=eventually_vertical_segment hu.continuous.continuousAt hv.continuous.continuousAt
    (huv x) hAe
  apply locallyLipschitz_germ (graphPotential_locallyLipschitz hA hu hv)
  filter_upwards [hn] with y hy
  rw [graphPotential_eq_integral hA.continuous]
  unfold verticalPotential
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (huv y)
  intro s hs
  exact (hy (huv y) s ⟨hs.1.le,hs.2.le⟩).symm
end Bernoulli.Foliation

end
end

end OAI
