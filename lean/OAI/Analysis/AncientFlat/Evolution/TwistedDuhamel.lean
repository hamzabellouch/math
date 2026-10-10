import OAI.Analysis.AncientFlat.Evolution.StrongAction

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace AncientMild
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (S : ℝ → E →L[ℂ] E)
  (hc : ∀ v : E, ContinuousOn (fun t => S t v) (Ici (0:ℝ)))
  (ha : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → S (s+t)=(S s).comp (S t))
include hc ha in
lemma backward_right_derivative (u : ℝ → E) {s T : ℝ} (hs : s<T) (F : E)
    (h : Tendsto (fun r : ℝ => (r-s)⁻¹ • (u r-S (r-s) (u s))) (𝓝[>] s) (𝓝 F)) :
    HasDerivWithinAt (fun r => S (max 0 (T-r)) (u r)) (S (T-s) F) (Ici s) s := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mpr
  have hh := ((continuous_action_clamp S hc).tendsto (T-s,F)).comp
    (((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds).prodMk_nhds h)
  rw [max_eq_right (sub_pos.mpr hs).le] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hs)] with r hr hrT
  have hTr : 0 ≤ T-r := sub_nonneg.mpr hrT.le
  have hrs : 0 ≤ r-s := sub_nonneg.mpr hr.le
  dsimp only [Function.comp_apply, id_eq, Prod.fst, Prod.snd]
  simp only [slope_def_module, max_eq_right hTr,max_eq_right (sub_pos.mpr hs).le]
  rw [ContinuousLinearMap.map_smul_of_tower,map_sub]
  congr 2
  rw [←ContinuousLinearMap.comp_apply,←ha (T-r) (r-s) hTr hrs]
  congr 2
  ring
include hc ha in

theorem duhamel_of_twisted_derivative (h0 : S 0=ContinuousLinearMap.id ℂ E)
    (u : ℝ → E) (f : ℝ → E) (hf : Continuous f) {T : ℝ} (hT : 0 ≤ T)
    (hu : ContinuousOn u (Icc (0:ℝ) T))
    (hd : ∀ s ∈ Ico (0:ℝ) T,
      Tendsto (fun r : ℝ => (r-s)⁻¹ • (u r-S (r-s) (u s))) (𝓝[>] s) (𝓝 (f s))) :
    u T=S T (u 0)+∫ r in (0:ℝ)..T, S (T-r) (f r) := by
  let p (s : ℝ) := S (max 0 (T-s)) (u s)
  let q (s : ℝ) := S (max 0 (T-s)) (f s)
  have hp : ContinuousOn p (Icc (0:ℝ) T) := (continuous_action_clamp S hc).continuousOn.comp
    (((continuous_const.sub continuous_id).continuousOn).prodMk hu) (fun _ _ => mem_univ _)
  have hq : Continuous q := (continuous_action_clamp S hc).comp
    ((continuous_const.sub continuous_id).prodMk hf)
  let g (s : ℝ) := S T (u 0)+∫ r in (0:ℝ)..s, q r
  have hg' (s : ℝ) : HasDerivAt g (q s) s := by
    exact (intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 s) (hq.stronglyMeasurableAtFilter volume (𝓝 s)) hq.continuousAt).const_add _
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun s => (hg' s).continuousAt)
  have he := eq_of_has_deriv_right_eq
    (fun s hs => backward_right_derivative S hc ha u hs.2 (f s) (hd s hs))
    (fun s hs => by
      have hh := (hg' s).hasDerivWithinAt (s := Ici s)
      dsimp [q] at hh
      simpa only [max_eq_right (sub_nonneg.mpr hs.2.le)] using hh)
    hp hg.continuousOn (by simp [g,max_eq_right hT]) T ⟨hT,le_rfl⟩
  simp only [sub_self,max_self,h0,ContinuousLinearMap.id_apply,g] at he
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le hT] at hr
  dsimp [q]
  rw [max_eq_right (sub_nonneg.mpr hr.2)]
end AncientMild

end

end OAI
