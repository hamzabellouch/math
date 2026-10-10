import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactFlowNeighborhood

namespace OAI

/-! # Compact control of graded legs with a moving pivot coordinate -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Topology

variable {n : ℕ}

/-- A rescaled Cartan leg with its moving initial coordinate retained. -/
def basedDynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (base v : Fin n → ℝ) : C(ℝ, Fin n → ℝ) :=
  ⟨fun t => dynkinProduct a B base (t • v),
    continuous_dynkinProduct a _ _ _ continuous_const continuous_const
      (continuous_id.smul continuous_const)⟩

theorem continuous_basedDynkinFlowMap {c : ℕ} (a : DynkinCoefficients c 2) :
    Continuous (fun p : ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (Fin n → ℝ) × (Fin n → ℝ) => basedDynkinFlowMap a p.1 p.2.1 p.2.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z :
    (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
        dynkinProduct a z.1.1 z.1.2.1 (z.2 • z.1.2.2))
  exact continuous_dynkinProduct (P :=
    (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
      (Fin n → ℝ) × (Fin n → ℝ)) × ℝ)
    a (fun z => z.1.1) (fun z => z.1.2.1) (fun z => z.2 • z.1.2.2)
    continuous_fst.fst continuous_fst.snd.fst
    (continuous_snd.smul continuous_fst.snd.snd)

/-- All sufficiently late actual legs lie in one compact part of the
open profile domain, even though the initial pivot coordinate varies. -/
theorem exists_compact_eventual_based_dynkin_leg
    {c : ℕ} (a : DynkinCoefficients c 2)
    (B : ℕ → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (B₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (base v : ℕ → Fin n → ℝ) (base₀ v₀ : Fin n → ℝ)
    (hB : Tendsto B atTop (𝓝 B₀)) (hb : Tendsto base atTop (𝓝 base₀))
    (hv : Tendsto v atTop (𝓝 v₀))
    (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hinside : ∀ t ∈ Icc (0 : ℝ) 1, dynkinProduct a B₀ base₀ (t • v₀) ∈ U) :
    ∃ Q : Set (Fin n → ℝ), IsCompact Q ∧ Q ⊆ U ∧
      ∀ᶠ k in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
        dynkinProduct a (B k) (base k) (t • v k) ∈ Q := by
  have hdata : Tendsto (fun k => (B k, base k, v k)) atTop (𝓝 (B₀, base₀, v₀)) :=
    hB.prodMk_nhds (hb.prodMk_nhds hv)
  have hlim : Tendsto (fun k => basedDynkinFlowMap a (B k) (base k) (v k)) atTop
      (𝓝 (basedDynkinFlowMap a B₀ base₀ v₀)) := by
    simpa only [Function.comp_def] using
      ((continuous_basedDynkinFlowMap a).tendsto (B₀, base₀, v₀)).comp hdata
  obtain ⟨Q, hQ, hQU, _, hevent⟩ := exists_compact_eventual_flow_image isCompact_Icc
    (basedDynkinFlowMap a B₀ base₀ v₀).continuous.continuousOn hU
    (by rintro _ ⟨t, ht, rfl⟩; exact hinside t ht)
    ((ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim) _ isCompact_Icc)
  exact ⟨Q, hQ, hQU, hevent.mono (fun k hk t ht => hk (mem_image_of_mem _ ht))⟩

end PolycyclicRecognition

end

end OAI
