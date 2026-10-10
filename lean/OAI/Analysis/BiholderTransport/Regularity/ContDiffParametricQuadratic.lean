import Mathlib
import OAI.Analysis.BiholderTransport.Contact.CompactMinty

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiffAt_parametric_quadratic_upper {f : E×F → ℝ} {x : E} {a : F}
    (hf : ContDiffAt ℝ ∞ f (x,a)) :
    ∃ δ>0, ∃ K>0, ∀ z∈Metric.ball x δ, ∀ w∈Metric.ball x δ,
      ∀ b∈Metric.ball a δ,
        f (w,b)-f (z,b)-fderiv ℝ f (z,b) (w-z,0) ≤ K*‖w-z‖^2 := by
  let K := ‖fderiv ℝ (fderiv ℝ f) (x,a)‖+1
  have hK : 0<K := by dsimp [K]; positivity
  have hc : ContinuousAt (fun q => ‖fderiv ℝ (fderiv ℝ f) q‖) (x,a) :=
    ((hf.fderiv_right (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).continuousAt_fderiv (by norm_num)).norm
  have hf2 : ContDiffAt ℝ 2 f (x,a) := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hk : ‖fderiv ℝ (fderiv ℝ f) (x,a)‖<K := by dsimp [K]; linarith
  have he : ∀ᶠ q in 𝓝 (x,a), ContDiffAt ℝ 2 f q ∧
      ‖fderiv ℝ (fderiv ℝ f) q‖<K :=
    (hf2.eventually (by norm_num)).and (hc.preimage_mem_nhds (Iio_mem_nhds hk))
  obtain ⟨δ,hδ,hbound⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,hδ,K,hK,?_⟩
  intro z hz w hw b hb
  have hzb : (z,b)∈Metric.ball (x,a) δ := by
    simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hz hb
  have hwb : (w,b)∈Metric.ball (x,a) δ := by
    simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hw hb
  have H := c2_quadratic_remainder_on_convex hK.le (convex_ball (x,a) δ)
    (fun q hq => (hbound hq).1) (fun q hq => (hbound hq).2.le) hzb hwb
  have H' := (abs_le.mp (show |f (w,b)-f (z,b)-fderiv ℝ f (z,b) ((w,b)-(z,b))|
      ≤ K*‖(w,b)-(z,b)‖^2 from H)).2
  simpa only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using H'

end
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport

lemma compact_eventually_uniform_radius_bound {A T : Type*}
    [TopologicalSpace A] [TopologicalSpace T] {K : Set A} (hK : IsCompact K)
    {t : T} {P : ℝ → ℝ → T → A → Prop}
    (hmono : ∀ {r R b B : ℝ}, 0<r → r≤R → b≤B → ∀ s a, P R b s a → P r B s a)
    (hlocal : ∀ a∈K, ∃ r>0, ∃ b>0, ∀ᶠ q : T×A in 𝓝 (t,a), P r b q.1 q.2) :
    ∃ r>0, ∃ b>0, ∀ᶠ s in 𝓝 t, ∀ a∈K, P r b s a := by
  apply hK.induction_on
    (p := fun J => ∃ r>0, ∃ b>0, ∀ᶠ s in 𝓝 t, ∀ a∈J, P r b s a)
  · exact ⟨1,by norm_num,1,by norm_num,Filter.Eventually.of_forall (by simp)⟩
  · intro J L hJL hL
    obtain ⟨r,hr,b,hb,H⟩ := hL
    refine ⟨r,hr,b,hb,?_⟩
    filter_upwards [H] with s hs
    exact fun a ha => hs a (hJL ha)
  · intro J L hJ hL
    obtain ⟨r,hr,b,hb,H⟩ := hJ
    obtain ⟨R,hR,B,hB,G⟩ := hL
    refine ⟨min r R,lt_min hr hR,max b B,lt_max_of_lt_left hb,?_⟩
    filter_upwards [H,G] with s hs gs
    intro a ha
    rcases ha with ha|ha
    · exact hmono (lt_min hr hR) (min_le_left _ _) (le_max_left _ _) s a (hs a ha)
    · exact hmono (lt_min hr hR) (min_le_right _ _) (le_max_right _ _) s a (gs a ha)
  · intro a ha
    obtain ⟨r,hr,b,hb,H⟩ := hlocal a ha
    obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp H
    refine ⟨V,mem_nhdsWithin_of_mem_nhds hV,r,hr,b,hb,?_⟩
    filter_upwards [hU] with s hs
    intro a ha
    exact hUV (show (s,a)∈U×ˢV from ⟨hs,ha⟩)

end WeakMTWTransport

end

end

end

end OAI
