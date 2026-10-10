import Mathlib
import OAI.Analysis.SymmetricDomains.SelectExcludedOffsets
import OAI.Analysis.SymmetricDomains.WeightedUnscaleC1Error

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
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E F S V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def chartScaledDomain (e : OpenPartialHomeomorph (E × F) (S × V))
    (A : S → Set V) (t : ℝ) : Set (E × F) :=
  {x | weightedScale t x ∈ e.source ∧
    (e (weightedScale t x)).2 ∈ A (e (weightedScale t x)).1}

lemma weightedScale_point_tendsto (x : E × F) :
    Tendsto (fun t => weightedScale t x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (weightedScale_uniform_zero (isCompact_singleton (x := x)).isBounded).tendsto_at (mem_singleton x)

theorem excluded_points_in_scaled_chart
    (e : OpenPartialHomeomorph (E × F) (S × V)) (A : S → Set V)
    (he : (0 : E × F) ∈ e.source) {s₀ : S} (he0 : e 0 = (s₀,0))
    (hei : ContDiffAt ℝ 1 e.symm (s₀,0)) (hA : ∀ s, (0 : V) ∉ A s)
    (d : V → ℝ)
    (hjoint : ∀ (s' : ℕ → S) (t' : ℕ → ℝ), Tendsto s' atTop (𝓝 s₀) →
      Tendsto t' atTop (𝓝 0) → (∀ j, 0 < t' j) → ∀ v : V,
      Tendsto (fun j => offsetDistance A (s' j) (t' j) v) atTop (𝓝 (d v)))
    (x : E × F) {r : V}
    (hr : Tendsto (fun t => t⁻¹ • (e (weightedScale t x)).2) (𝓝[>] (0 : ℝ)) (𝓝 r))
    (hdr : d r = 0) (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (htp : ∀ j, 0 < t j) :
    ∃ y : ℕ → E × F, Tendsto y atTop (𝓝 x) ∧
      (∀ j, y j ∉ chartScaledDomain e A (t j)) ∧
      ∀ j, weightedScale (t j) (y j) ∈ e.source := by
  classical
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall htp⟩
  let q : ℕ → S × V := fun j => e (weightedScale (t j) x)
  let v : ℕ → V := fun j => (t j)⁻¹ • (q j).2
  have hδ := (weightedScale_point_tendsto x).comp ht'
  have hq : Tendsto q atTop (𝓝 (s₀,0)) := by
    simpa only [q,Function.comp_def,he0] using (e.continuousAt he).tendsto.comp hδ
  have hv : Tendsto v atTop (𝓝 r) := hr.comp ht'
  have hd : Tendsto (fun j => infDist (v j) (offsetScaled A (q j).1 (t j))ᶜ) atTop (𝓝 0) :=
    excluded_limit_from_offsetDistance A (fun j => (q j).1) t
      (by simpa only [hdr,Function.comp_def] using hjoint _ t ((continuous_fst.tendsto (s₀,(0:V))).comp hq) ht htp r) hv
  obtain ⟨u,hu,hud⟩ := select_excluded_offsets A (fun j => (q j).1) t v
    (fun j => offset_excluded_nonempty A _ _ (hA _)) hd
  let q' : ℕ → S × V := fun j => ((q j).1,(t j) • u j)
  have hdiff (j : ℕ) : dist (q' j) (q j) = t j * dist (u j) (v j) := by
    have hc : (t j) • v j = (q j).2 := by simp only [v,smul_inv_smul₀ (htp j).ne']
    change dist ((q j).1,(t j) • u j) (q j) = _
    rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg (x := (t j) • u j) (y := (q j).2))]
    rw [← hc,dist_smul₀,Real.norm_eq_abs,abs_of_pos (htp j)]
  have hqd : Tendsto (fun j => dist (q' j) (q j)) atTop (𝓝 0) := by
    simp_rw [hdiff]
    simpa only [zero_mul] using ht.mul hud
  have hq' : Tendsto q' atTop (𝓝 (s₀,0)) :=
    hq.congr_dist (by simpa only [dist_comm] using hqd)
  have herr : Tendsto (fun j => (t j)⁻¹*dist (q' j) (q j)) atTop (𝓝 0) := by
    simpa only [hdiff,inv_mul_cancel_left₀ (htp _).ne'] using hud
  have herror := weightedUnscale_C1_error hei ht htp hq hq' herr
  have hsource : ∀ᶠ j in atTop, weightedScale (t j) x ∈ e.source :=
    hδ.eventually (e.open_source.mem_nhds he)
  have hrest : ∀ᶠ j in atTop, weightedUnscale (t j) (e.symm (q j)) = x := by
    filter_upwards [hsource] with j hj
    change weightedUnscale (t j) (e.symm (e (weightedScale (t j) x))) = x
    rw [e.left_inv hj,weightedUnscale_scale (htp j)]
  have hylim : Tendsto (fun j => weightedUnscale (t j) (e.symm (q' j))) atTop (𝓝 x) := by
    apply tendsto_sub_nhds_zero_iff.mp
    exact herror.congr' (hrest.mono fun j hj => by rw [hj])
  have htarget : (s₀,(0:V)) ∈ e.target := he0 ▸ e.map_source he
  have hevent : ∀ᶠ j in atTop, q' j ∈ e.target := hq'.eventually (e.open_target.mem_nhds htarget)
  let y : ℕ → E × F := fun j => if q' j ∈ e.target then
    weightedUnscale (t j) (e.symm (q' j)) else 0
  have hy0 (j : ℕ) : weightedScale (t j) (0 : E × F) = 0 := by simp [weightedScale]
  refine ⟨y,hylim.congr' (hevent.mono fun j hj => by simp only [y,ite_eq_left hj]),?_,?_⟩
  · intro j
    by_cases hj : q' j ∈ e.target
    · have hc : weightedScale (t j) (y j) = e.symm (q' j) := by
        simp only [y,ite_eq_left hj,weightedScale_unscale (htp j)]
      intro hmem
      have hnormal := hmem.2
      rw [hc,e.right_inv hj] at hnormal
      exact hu j hnormal
    · intro hmem
      have hnormal := hmem.2
      simp only [y,ite_eq_right hj,hy0,he0] at hnormal
      exact hA s₀ hnormal
  · intro j
    by_cases hj : q' j ∈ e.target
    · simpa only [y,ite_eq_left hj,weightedScale_unscale (htp j)] using e.map_target hj
    · simpa only [y,ite_eq_right hj,hy0] using he

theorem weighted_chart_two_sided
    (e : OpenPartialHomeomorph (E × F) (S × V)) (A : S → Set V)
    (he : (0 : E × F) ∈ e.source) {s₀ : S} (he0 : e 0 = (s₀,0))
    (hei : ContDiffAt ℝ 1 e.symm (s₀,0)) (hA : ∀ s, (0 : V) ∉ A s)
    (ha : AnalyticAt ℝ (fun x => (e x).2) 0)
    (hlin : ∀ z : E, fderiv ℝ (fun x => (e x).2) 0 (z,0) = 0)
    (d : V → ℝ) (hd : ∀ v, 0 ≤ d v)
    (hjoint : ∀ (s' : ℕ → S) (t' : ℕ → ℝ), Tendsto s' atTop (𝓝 s₀) →
      Tendsto t' atTop (𝓝 0) → (∀ j, 0 < t' j) → ∀ v : V,
      Tendsto (fun j => offsetDistance A (s' j) (t' j) v) atTop (𝓝 (d v))) :
    ∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) V,
      let R : E × F → V := fun x => fderiv ℝ (fun x => (e x).2) 0 (0,x.2)+Q (fun _ => x.1)
      (∀ K : Set (E × F), IsCompact K → K ⊆ {x | d (R x) ≠ 0} →
        ∀ᶠ t : ℝ in 𝓝[>] 0, K ⊆ chartScaledDomain e A t) ∧
      (∀ x : E × F, d (R x) = 0 → ∀ (t : ℕ → ℝ),
        Tendsto t atTop (𝓝 0) → (∀ j, 0 < t j) →
        ∃ y : ℕ → E × F, Tendsto y atTop (𝓝 x) ∧
          (∀ j, y j ∉ chartScaledDomain e A (t j)) ∧
          ∀ j, weightedScale (t j) (y j) ∈ e.source) := by
  obtain ⟨Q,hQ⟩ := weighted_taylor_uniformly_compact ha
    (by simp only [he0]) hlin
  refine ⟨Q,?_,?_⟩
  · intro K hK hKR
    apply compact_inclusion_from_offsets A (chartScaledDomain e A)
      (fun t x => (e (weightedScale t x)).1)
      (fun t x => t⁻¹ • (e (weightedScale t x)).2)
      (fun x => fderiv ℝ (fun x => (e x).2) 0 (0,x.2)+Q (fun _ => x.1)) d s₀ hK
    · fun_prop
    · simpa only [he0] using weightedScale_continuous_uniform
        (e.continuousAt he |>.fst) hK.isBounded
    · exact hQ K hK
    · exact hjoint
    · filter_upwards [weightedScale_eventually_mem hK.isBounded (e.open_source.mem_nhds he),
        self_mem_nhdsWithin] with t ht htp
      intro x hx
      have htpos : 0 < t := htp
      simp only [chartScaledDomain,mem_ofPred_eq,ht x hx,true_and,offsetScaled,
        smul_inv_smul₀ htpos.ne']
    · intro x hx
      exact lt_of_le_of_ne (hd _) (Ne.symm (hKR hx))
  · intro x hx t ht htp
    exact excluded_points_in_scaled_chart e A he he0 hei hA d hjoint x
      ((hQ {x} isCompact_singleton).tendsto_at (mem_singleton x)) hx t ht htp

end Release061

end

end OAI
