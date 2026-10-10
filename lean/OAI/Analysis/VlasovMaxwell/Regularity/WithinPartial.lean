import Mathlib
import OAI.Analysis.VlasovMaxwell.LocalPDE.PicardCurvature

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory Asymptotics
open scoped Topology ContDiff Convex

namespace RVM

lemma time_space_isLittleO_sub_sub_fderiv
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

lemma hasFDerivWithinAt_of_time_space {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {J : Set ℝ} {F : ℝ × U → W} {D : ℝ × U → (U →L[ℝ] W)} {t : ℝ} {x : U} {g : W}
    (ht : t∈J) (hD : ∀ r∈J, ∀ y, HasFDerivAt (fun z => F (r,z)) (D (r,y)) y)
    (hcD : ContinuousOn D {p | p.1∈J})
    (hT : HasDerivWithinAt (fun r => F (r,x)) g J t) :
    HasFDerivWithinAt F (assembleDerivative g (D (t,x))) {p | p.1∈J} (t,x) := by
  let S : Set (ℝ × U) := {p | p.1∈J}
  let l := 𝓝[S] (t,x)
  have hq : Tendsto (fun p : ℝ × U => p) l (𝓝 (t,x)) := nhdsWithin_le_nhds
  have hqt : Tendsto (fun p : ℝ × U => p.1) l (𝓝 t) := continuous_fst.continuousAt.tendsto.comp hq
  have hqx : Tendsto (fun p : ℝ × U => p.2) l (𝓝 x) := continuous_snd.continuousAt.tendsto.comp hq
  have hqtJ : Tendsto (fun p : ℝ × U => p.1) l (𝓝[J] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqt,by exact eventually_mem_nhdsWithin⟩
  have hp : Tendsto (fun q : (ℝ × U) × U => (q.1.1,q.2)) (l ×ˢ 𝓝 x) (𝓝[S] (t,x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hqt.comp tendsto_fst).prodMk_nhds tendsto_snd,?_⟩
    exact (eventually_mem_nhdsWithin : ∀ᶠ p in l, p∈S).prod_mk (Eventually.of_forall fun _ => True.intro) |>.mono (fun q h => h.1)
  have heS : (fun q : ℝ × U => F (q.1,q.2)-F (q.1,x)-(D (t,x)) (q.2-x)) =o[l] (fun q => q.2-x) := by
    apply time_space_isLittleO_sub_sub_fderiv (f:=fun q : ℝ × U => fun y => F (q.1,y))
      (f':=fun q : ℝ × U => fun y => D (q.1,y)) hqx tendsto_const_nhds
    · exact ((eventually_mem_nhdsWithin : ∀ᶠ p in l, p∈S).prod_mk (Eventually.of_forall fun _ => True.intro)).mono
        (fun q h => (hD q.1.1 h.1 q.2).hasFDerivWithinAt)
    · exact (hcD (t,x) ht).tendsto.comp (by simpa only [nhdsWithin_univ] using hp)
  have hbS : (fun q : ℝ × U => q.2-x) =O[l] (fun q => q-(t,x)) := by
    apply isBigO_of_le l
    intro q
    exact norm_snd_le (q-(t,x))
  have heT := hT.hasFDerivWithinAt.isLittleO.comp_tendsto hqtJ
  have hbT : (fun q : ℝ × U => q.1-t) =O[l] (fun q => q-(t,x)) := by
    apply isBigO_of_le l
    intro q
    exact norm_fst_le (q-(t,x))
  rw [hasFDerivWithinAt_iff_isLittleO]
  convert (heS.trans_isBigO hbS).add (heT.trans_isBigO hbT) using 1
  ext q
  change F q-F (t,x)-((q.1-t) • g+(D (t,x)) (q.2-x)) =
    (F (q.1,q.2)-F (q.1,x)-(D (t,x)) (q.2-x)) +
      (F (q.1,x)-F (t,x)-(q.1-t) • g)
  abel

end RVM
end

end OAI
