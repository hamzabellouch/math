import OAI.Probability.FreeIsing.Factors.ContinuousRecovery
import OAI.Probability.FreeIsing.Martingales.ContinuousL2Limit

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousHorizonGluing

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

def glue (L : ℕ → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limUnder atTop (fun n => L n t ω)

theorem glue_isStronglyPredictable {F : Filtration ℝ≥0 mΩ}
    {L : ℕ → ℝ≥0 → Ω → ℝ} (hL : ∀ n, IsStronglyPredictable F (L n)) :
    IsStronglyPredictable F (glue L) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact StronglyMeasurable.limUnder hL

theorem ae_all_eq_on_Iic {f g : ℝ≥0 → Ω → ℝ} (T : ℝ≥0)
    (hf : ∀ᵐ ω ∂μ, ContinuousOn (fun t => f t ω) (Iic T))
    (hg : ∀ᵐ ω ∂μ, ContinuousOn (fun t => g t ω) (Iic T))
    (hfg : ∀ t ≤ T, f t =ᵐ[μ] g t) :
    ∀ᵐ ω ∂μ, ∀ t ≤ T, f t ω = g t ω := by
  let : Nonempty (Iic T) := ⟨⟨0, by simp⟩⟩
  have hf' : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T => f t ω) := by
    filter_upwards [hf] with ω hω
    exact continuousOn_iff_continuous_domRestrict.mp hω
  have hg' : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T => g t ω) := by
    filter_upwards [hg] with ω hω
    exact continuousOn_iff_continuous_domRestrict.mp hω
  have heq := ae_eq_of_continuous_of_evaluation_ae_eq hf' hg'
    (fun t : Iic T => hfg t t.property)
  filter_upwards [heq] with ω hω
  intro t ht
  exact congrFun hω ⟨t, ht⟩

theorem ae_all_glue_eq {L : ℕ → ℝ≥0 → Ω → ℝ}
    (hc : ∀ n, ∀ᵐ ω ∂μ, ContinuousOn (fun t => L n t ω) (Iic (n : ℝ≥0)))
    (hcompat : ∀ (n m : ℕ) (t : ℝ≥0), t ≤ (n : ℝ≥0) → t ≤ (m : ℝ≥0) →
      L n t =ᵐ[μ] L m t) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (t : ℝ≥0), t ≤ (n : ℝ≥0) → glue L t ω = L n t ω := by
  have heq (n m : ℕ) : ∀ᵐ ω ∂μ, ∀ t ≤ min (n : ℝ≥0) (m : ℝ≥0),
      L n t ω = L m t ω := by
    apply ae_all_eq_on_Iic
    · filter_upwards [hc n] with ω hω
      exact hω.mono (Iic_subset_Iic.mpr (min_le_left _ _))
    · filter_upwards [hc m] with ω hω
      exact hω.mono (Iic_subset_Iic.mpr (min_le_right _ _))
    · intro t ht
      exact hcompat n m t (ht.trans (min_le_left _ _)) (ht.trans (min_le_right _ _))
  have hall : ∀ᵐ ω ∂μ, ∀ (n m : ℕ) (t : ℝ≥0), t ≤ min (n : ℝ≥0) (m : ℝ≥0) →
      L n t ω = L m t ω := ae_all_iff.mpr (fun n => ae_all_iff.mpr (heq n))
  filter_upwards [hall] with ω hω
  intro n t ht
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact hω n m t (le_min ht (ht.trans (by exact_mod_cast hm)))

theorem ae_continuous_glue {L : ℕ → ℝ≥0 → Ω → ℝ}
    (hc : ∀ n, ∀ᵐ ω ∂μ, ContinuousOn (fun t => L n t ω) (Iic (n : ℝ≥0)))
    (hcompat : ∀ (n m : ℕ) (t : ℝ≥0), t ≤ (n : ℝ≥0) → t ≤ (m : ℝ≥0) →
      L n t =ᵐ[μ] L m t) :
    ∀ᵐ ω ∂μ, Continuous (fun t => glue L t ω) := by
  filter_upwards [ae_all_iff.mpr hc, ae_all_glue_eq hc hcompat] with ω hcω hω
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hlocal : ContinuousOn (fun s => glue L s ω) (Iic (n : ℝ≥0)) :=
    (hcω n).congr (fun s hs => hω n s hs)
  exact hlocal.continuousAt (Iic_mem_nhds hn)

theorem exists_global_predictable_continuous_version
    {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}
    (hlocal : ∀ n : ℕ, ∃ L : ℝ≥0 → Ω → ℝ,
      IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => L t ω) (Iic (n : ℝ≥0))) ∧
      ∀ t ≤ (n : ℝ≥0), L t =ᵐ[μ] X t) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => L t ω)) ∧
      ∀ t, L t =ᵐ[μ] X t := by
  choose L hpred hc heq using hlocal
  have hcompat (n m : ℕ) (t : ℝ≥0) (hn : t ≤ n) (hm : t ≤ m) :
      L n t =ᵐ[μ] L m t := (heq n t hn).trans (heq m t hm).symm
  refine ⟨glue L, glue_isStronglyPredictable hpred, ae_continuous_glue hc hcompat, ?_⟩
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hglue : glue L t =ᵐ[μ] L n t := by
    filter_upwards [ae_all_glue_eq hc hcompat] with ω hω
    exact hω n t hn
  exact hglue.trans (heq n t hn)

end Problem367.ContinuousHorizonGluing

namespace Problem367.MartingaleSquareMaximal

theorem exists_global_predictable_continuous_L2_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → ℝ}
    (hM : ∀ n, Martingale (M n) F μ)
    (h2 : ∀ n t, MemLp (M n t) 2 μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => M n t ω))
    (hC : ∀ N : ℕ, CauchySeq (fun n => (h2 n (N : ℝ≥0)).toLp (M n N))) :
    ∃ L : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F L ∧
      (∀ᵐ ω ∂μ, Continuous (fun t => L t ω)) ∧
      ∀ t, ∃ hL2 : MemLp (L t) 2 μ,
        Tendsto (fun n => (h2 n t).toLp (M n t)) atTop (𝓝 (hL2.toLp (L t))) := by
  have hlocal (N : ℕ) := exists_predictable_continuous_L2_limit hM h2 hc
    (N : ℝ≥0) (hC N)
  choose L hpred hcont hlim using hlocal
  have hcompat (n m : ℕ) (t : ℝ≥0) (hn : t ≤ n) (hm : t ≤ m) :
      L n t =ᵐ[μ] L m t := by
    obtain ⟨hn2, hnlim⟩ := hlim n t hn
    obtain ⟨hm2, hmlim⟩ := hlim m t hm
    have hclass := tendsto_nhds_unique hnlim hmlim
    filter_upwards [hn2.coeFn_toLp, hm2.coeFn_toLp] with ω hnω hmω
    rw [← hnω, ← hmω, hclass]
  refine ⟨ContinuousHorizonGluing.glue L,
    ContinuousHorizonGluing.glue_isStronglyPredictable hpred,
    ContinuousHorizonGluing.ae_continuous_glue hcont hcompat, ?_⟩
  intro t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨hn2, hnlim⟩ := hlim n t hn
  have heq : ContinuousHorizonGluing.glue L t =ᵐ[μ] L n t := by
    filter_upwards [ContinuousHorizonGluing.ae_all_glue_eq hcont hcompat] with ω hω
    exact hω n t hn
  have hL2 : MemLp (ContinuousHorizonGluing.glue L t) 2 μ := hn2.ae_eq heq.symm
  refine ⟨hL2, ?_⟩
  rw [hL2.toLp_congr hn2 heq]
  exact hnlim

end Problem367.MartingaleSquareMaximal

end

end OAI
