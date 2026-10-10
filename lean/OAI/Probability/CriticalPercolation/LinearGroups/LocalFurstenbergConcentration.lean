import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.LocalProjectiveAction

namespace OAI

section
noncomputable section
open Set Function Filter MeasureTheory NormedSpace Module Metric TopologicalSpace
open scoped Classical Topology ENNReal

namespace CriticalPercolation.LocalProjective
variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]
variable [ProperSpace K] [FiniteDimensional K V]

lemma subspace_full_of_singular_limit
    (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (a : ℕ → V ≃L[K] V) (c : ℕ → K) (hc : ∀ n, c n≠0)
    (A : V →L[K] V) (hA : A≠0)
    (hlim : Tendsto (fun n => c n • (a n).toContinuousLinearMap) atTop (𝓝 A))
    (hμ : ∀ n, Measure.map (action (a n)) μ=μ)
    (hker : μ (subspace A.toLinearMap.ker)=0) :
    ∀ᵐ q ∂μ, q∈subspace A.toLinearMap.range := by
  let : MetricSpace (Space K V) := metrizableSpaceMetric _
  let L : Set (Space K V) := subspace A.toLinearMap.range
  have hL : IsClosed L := closed_subspace _
  have hLne : L.Nonempty := by
    have hex : ∃ x : V, A x≠0 := by
      by_contra hn
      push Not at hn
      exact hA (ContinuousLinearMap.ext hn)
    obtain ⟨x,hx⟩ := hex
    exact ⟨point K V ⟨A x,hx⟩,(point_mem_subspace _ _).mpr ⟨x,rfl⟩⟩
  let f : Space K V → ℝ := fun q => min 1 (infDist q L)
  have hfcont : Continuous f := continuous_const.min (continuous_infDist_pt L)
  have hfnonneg (q : Space K V) : 0≤f q := le_min zero_le_one infDist_nonneg
  have hfbound (q : Space K V) : ‖f q‖≤1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hfnonneg q)]
    exact min_le_left _ _
  have hfi : Integrable f μ := (integrable_const (1:ℝ)).mono' hfcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hfbound)
  have hx : ∀ᵐ q ∂μ, q∉subspace A.toLinearMap.ker := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hker
  have hpoint : ∀ᵐ q ∂μ, Tendsto (fun n => f (action (a n) q)) atTop (𝓝 0) := by
    filter_upwards [hx] with q hq
    obtain ⟨v,rfl⟩ := point_surjective K V q
    have hv : A (v:V)≠0 := by
      simpa only [point_mem_subspace,LinearMap.mem_ker,ContinuousLinearMap.coe_coe] using hq
    let w : ℕ → NZ V := fun n => ⟨(c n • (a n).toContinuousLinearMap) (v:V),
      smul_ne_zero (hc n) (nzImage (a n) v).property⟩
    have hev : Tendsto (fun n => (c n • (a n).toContinuousLinearMap) (v:V)) atTop (𝓝 (A v)) :=
      ((continuous_id.clm_apply continuous_const).tendsto A).comp hlim
    have hw : Tendsto w atTop (𝓝 ⟨A v,hv⟩) := tendsto_subtype_rng.mpr hev
    have hp := (continuous_point K V).continuousAt.tendsto.comp hw
    have he (n : ℕ) : point K V (w n)=action (a n) (point K V v) := by
      rw [action_point,point_eq_iff]
      exact ⟨c n,rfl⟩
    change Tendsto (fun n => point K V (w n)) atTop (𝓝 (point K V ⟨A v,hv⟩)) at hp
    simp_rw [he] at hp
    have hf := hfcont.continuousAt.tendsto.comp hp
    have hin : point K V ⟨A v,hv⟩∈L := (point_mem_subspace _ _).mpr ⟨v,rfl⟩
    have hz : f (point K V ⟨A v,hv⟩)=0 := by
      simp only [f,infDist_zero_of_mem hin,min_eq_right zero_le_one]
    rw [hz] at hf
    exact hf
  have hconv := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=fun n q => f (action (a n) q)) (f:=fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (fun n => (hfcont.comp (continuous_action (a n))).aestronglyMeasurable)
    (integrable_const 1) (fun n => Filter.Eventually.of_forall (fun q => hfbound _)) hpoint
  have he (n : ℕ) : (∫ q, f (action (a n) q) ∂μ)=∫ q, f q ∂μ := by
    rw [←integral_map (continuous_action (a n)).measurable.aemeasurable hfcont.aestronglyMeasurable,
      hμ n]
  simp_rw [he] at hconv
  have hint : (∫ q, f q ∂μ)=0 := by
    exact tendsto_nhds_unique tendsto_const_nhds (by simpa only [integral_zero] using hconv)
  have hz := (integral_eq_zero_iff_of_nonneg hfnonneg hfi).mp hint
  filter_upwards [hz] with q hq
  apply (hL.mem_iff_infDist_zero hLne).mpr
  change min 1 (infDist q L)=0 at hq
  rcases min_choice (1:ℝ) (infDist q L) with he|he
  · rw [he] at hq
    norm_num at hq
  · exact he.symm.trans hq

lemma injective_of_nonzero_projective_limit
    (μ : Measure (Space K V)) [IsProbabilityMeasure μ]
    (hn : ∀ W : Submodule K V, W≠⊤ → μ (subspace W)=0)
    (a : ℕ → V ≃L[K] V) (c : ℕ → K) (hc : ∀ n, c n≠0)
    (A : V →L[K] V) (hA : A≠0)
    (hlim : Tendsto (fun n => c n • (a n).toContinuousLinearMap) atTop (𝓝 A))
    (hμ : ∀ n, Measure.map (action (a n)) μ=μ) : Injective A := by
  have hk : A.toLinearMap.ker≠⊤ := by
    intro he
    apply hA
    ext x
    have hx : x∈A.toLinearMap.ker := he ▸ Submodule.mem_top
    exact hx
  have hae := subspace_full_of_singular_limit μ a c hc A hA hlim hμ (hn _ hk)
  have hr : A.toLinearMap.range=⊤ := by
    by_contra hr
    have hnot : ∀ᵐ q ∂μ, q∉subspace A.toLinearMap.range := by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hn _ hr
    obtain ⟨q,hq,hq'⟩ := (hae.and hnot).exists
    exact hq' hq
  exact LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp hr)

end CriticalPercolation.LocalProjective
end
end

end OAI
