import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped Manifold

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

lemma compact_parametric_abs_bound {f : P → E → ℝ} {p₀ : P} {K : Set E}
    (hK : IsCompact K) (hf : Continuous (fun px : P×E => f px.1 px.2)) :
    ∃ M : ℝ,0<M ∧ ∀ᶠ p in 𝓝 p₀,∀ x∈K,|f p x|≤M := by
  have hbase : Continuous (fun x => f p₀ x) := hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hbase.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hlt : |f p₀ x| < |C|+1 := by
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self C]
  have hct : Tendsto (fun px : P×E => |f px.1 px.2|) (𝓝 (p₀,x)) (𝓝 |f p₀ x|) := hf.abs.continuousAt
  exact (hct.eventually_lt_const hlt).mono (fun _ h => h.le)

lemma compact_parametric_abs_lower {f : P → E → ℝ} {p₀ : P} {K : Set E}
    (hK : IsCompact K) (hf : Continuous (fun px : P×E => f px.1 px.2))
    (hne : ∀ x∈K,f p₀ x≠0) :
    ∃ κ : ℝ,0<κ ∧ ∀ᶠ p in 𝓝 p₀,∀ x∈K,κ≤|f p x| := by
  have hbase : Continuous (fun x => |f p₀ x|) := hf.abs.comp (continuous_const.prodMk continuous_id)
  obtain ⟨κ,hκ,hlo⟩ := hK.exists_forall_le'
    hbase.continuousOn
    (fun x hx => abs_pos.mpr (hne x hx))
  refine ⟨κ/2,by positivity,?_⟩
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hlt : κ/2 < |f p₀ x| := by have := hlo x hx; linarith
  have hct : Tendsto (fun px : P×E => |f px.1 px.2|) (𝓝 (p₀,x)) (𝓝 |f p₀ x|) := hf.abs.continuousAt
  exact (hct.eventually_const_lt hlt).mono (fun _ h => h.le)

lemma exists_smooth_core_cutoff
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K Ω : Set V} (hK : IsCompact K) (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hsub : K⊆Ω) :
    ∃ χ : V → ℝ,ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧
      tsupport χ⊆Ω ∧ (∀ x,χ x∈Icc 0 1) ∧
      (∀ x∈K,χ =ᶠ[𝓝 x] (fun _ => 1)) := by
  obtain ⟨χ,hχ₀,hχ₁,hχb⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ,V))
    hΩ.isClosed_compl hK.isClosed (disjoint_left.mpr (fun _ hx hxK => hx (hsub hxK))) (n:=⊤)
  have ht : tsupport (χ : V → ℝ)⊆Ω := by
    intro x hx
    by_contra hn
    exact (notMem_tsupport_iff_eventuallyEq.mpr (hχ₀.filter_mono (nhds_le_nhdsSet hn))) hx
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,
    (hb.subset ht).isCompact_closure.of_isClosed_subset (isClosed_tsupport _) subset_closure,
    ht,hχb,?_⟩
  intro x hx
  exact hχ₁.filter_mono (nhds_le_nhdsSet hx)

end ScalarConductivity

end

end OAI
