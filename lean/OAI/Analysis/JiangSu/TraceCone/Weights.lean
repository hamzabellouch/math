import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Model

namespace OAI


noncomputable section
open scoped ENNReal NNReal

namespace TraceCone
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace Positive
variable {A}

def sum {ι : Type*} (s : Finset ι) (a : ι → Positive A) : Positive A :=
  ⟨∑ i ∈ s, (a i).1, Finset.sum_nonneg fun i _ => (a i).2⟩
end Positive

namespace ExtendedTrace
variable {A}

@[simp] theorem zero_apply (a : Positive A) : (0 : ExtendedTrace A) a = 0 := rfl

theorem zero_of_le (τ : ExtendedTrace A) {a b : Positive A} (hab : a ≤ b)
    (hb : τ b = 0) : τ a = 0 := by
  exact le_antisymm ((τ.monotone hab).trans_eq hb) bot_le

theorem map_sum (τ : ExtendedTrace A) {ι : Type*} (s : Finset ι)
    (a : ι → Positive A) : τ (Positive.sum s a) = ∑ i ∈ s, τ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [Positive.sum, Positive.zero] using τ.map_zero
  | @insert i s hi ih =>
    have hs : Positive.sum (insert i s) a = Positive.add (a i) (Positive.sum s a) := by
      apply Subtype.ext
      simp [Positive.sum, Positive.add, hi]
    rw [hs, τ.map_add, ih, Finset.sum_insert hi]

theorem finite_positive_partition (τ : ExtendedTrace A) {ι : Type*}
    (s : Finset ι) (y : ι → A) (a b : Positive A)
    (ha : ∑ i ∈ s, star (y i) * y i = a.1)
    (hb : ∑ i ∈ s, y i * star (y i) = b.1) : τ a = τ b := by
  have ha' : Positive.sum s (fun i => Positive.starMul (y i)) = a := Subtype.ext ha
  have hb' : Positive.sum s (fun i => Positive.mulStar (y i)) = b := Subtype.ext hb
  rw [← ha', ← hb', τ.map_sum, τ.map_sum]
  exact Finset.sum_congr rfl fun i _ => τ.tracial (y i)

end ExtendedTrace
end TraceCone

end


noncomputable section
open scoped NNReal ENNReal Topology
open Filter

namespace TraceCone
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
  rw [dist_eq_norm, norm_sub_rev]
  exact (norm_sub_cut_le (ε n) a).trans_lt (hN n hn)

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

end TraceCone

end

end OAI
