import OAI.Analysis.Pureness.Stabilization.Weights
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI
noncomputable section
open scoped NNReal ENNReal Topology
open Filter
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace Positive

def cut (ε : ℝ≥0) (a : Positive A) : Positive A :=
  ⟨cfcₙ (fun t : ℝ => max (t - ε) 0) a.1, cfcₙ_nonneg fun _ _ => le_max_right _ _⟩

theorem cut_le (ε : ℝ≥0) (a : Positive A) : cut ε a ≤ a := by
  change cfcₙ (fun t : ℝ => max (t - ε) 0) a.1 ≤ a.1
  nth_rw 2 [← cfcₙ_id' ℝ a.1]
  apply (cfcₙ_le_iff _ _ a.1 (hf0 := by simp) (ha := IsSelfAdjoint.of_nonneg a.2)).mpr
  intro t ht
  exact max_le (sub_le_self _ ε.2) (quasispectrum_nonneg_of_nonneg a.1 a.2 t ht)

theorem norm_sub_cut_le (ε : ℝ≥0) (a : Positive A) : ‖a.1 - (cut ε a).1‖ ≤ ε := by
  change ‖a.1 - cfcₙ (fun t : ℝ => max (t - ε) 0) a.1‖ ≤ ε
  have heq : a.1 - cfcₙ (fun t : ℝ => max (t - ε) 0) a.1 =
      cfcₙ (fun t : ℝ => t - max (t - ε) 0) a.1 := by
    rw [cfcₙ_sub (f := fun t : ℝ => t) (g := fun t : ℝ => max (t - ε) 0)
      (hf0 := rfl) (hg0 := by simp), cfcₙ_id' ℝ a.1]
  rw [heq]
  apply norm_cfcₙ_le
  intro t ht
  have ht0 := quasispectrum_nonneg_of_nonneg a.1 a.2 t ht
  rw [Real.norm_eq_abs, abs_le]
  by_cases h : t - ε ≤ 0
  · rw [max_eq_right h]
    constructor <;> linarith [ε.2]
  · rw [max_eq_left (le_of_not_ge h), sub_sub_cancel]
    exact ⟨neg_le_self ε.2, le_rfl⟩

theorem tendsto_cut (ε : ℕ → ℝ≥0) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (a : Positive A) : Tendsto (fun n => cut (ε n) a) atTop (𝓝 a) := by
  rw [tendsto_subtype_rng, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hε).2 δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  have h := norm_sub_cut_le (ε n) a
  rw [dist_eq_norm, norm_sub_rev]
  exact h.trans_lt (hN n hn)

end Positive

namespace ExtendedTrace

theorem le_of_forall_cut_le (τ : ExtendedTrace A) (a : Positive A) (r : ℝ≥0∞)
    (h : ∀ ε : ℝ≥0, 0 < ε → τ (Positive.cut ε a) ≤ r) : τ a ≤ r := by
  let ε : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  exact (τ.lowerSemicontinuous.isClosed_preimage r).mem_of_tendsto
    (Positive.tendsto_cut ε hε a) (Eventually.of_forall fun n => h (ε n) (by
      dsimp [ε]
      positivity))

theorem eq_iSup_cuts (τ : ExtendedTrace A) (a : Positive A) :
    τ a = ⨆ ε : ℝ≥0, ⨆ (_ : 0 < ε), τ (Positive.cut ε a) := by
  apply le_antisymm
  · apply τ.le_of_forall_cut_le a
    intro ε hε
    exact le_iSup_of_le ε (le_iSup_of_le hε le_rfl)
  · exact iSup_le fun ε => iSup_le fun _ => τ.monotone (Positive.cut_le ε a)
end ExtendedTrace

def CanonicalConverges {ι : Type*} (L : Filter ι) (u : ι → ExtendedTrace A)
    (τ : ExtendedTrace A) : Prop :=
  ∀ (a : Positive A) (ε : ℝ≥0), 0 < ε →
    Filter.limsup (fun i => u i (Positive.cut ε a)) L ≤ τ a ∧
      τ a ≤ Filter.liminf (fun i => u i a) L

theorem canonicalConverges_const {ι : Type*} (L : Filter ι) [L.NeBot]
    (τ : ExtendedTrace A) : CanonicalConverges L (fun _ => τ) τ := by
  intro a ε _
  simp only [Filter.limsup_const, Filter.liminf_const]
  exact ⟨τ.monotone (Positive.cut_le ε a), le_rfl⟩

theorem canonicalConverges_const_iff {ι : Type*} (L : Filter ι) [L.NeBot]
    (τ σ : ExtendedTrace A) : CanonicalConverges L (fun _ => τ) σ ↔ τ = σ := by
  constructor
  · intro h
    apply ExtendedTrace.ext
    intro a
    apply le_antisymm
    · apply τ.le_of_forall_cut_le a
      intro ε hε
      simpa only [Filter.limsup_const] using (h a ε hε).1
    · simpa only [Filter.liminf_const] using (h a 1 (by norm_num)).2
  · rintro rfl
    exact canonicalConverges_const L τ

end CuntzTrace

end

end OAI
