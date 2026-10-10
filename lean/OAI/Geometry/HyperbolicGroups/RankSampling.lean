import Mathlib
import OAI.Geometry.HyperbolicGroups.SamplingStage
import OAI.Geometry.HyperbolicGroups.RankSelection

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

theorem eventually_exists_tables {J : Type*} [Fintype J]
    (T : J → ConditionalTest) (M : ℕ) {α β δ ε τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) :
    ∀ᶠ n in atTop, ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ GoodUpTo M α β δ (Sum.elim w d) ∧
      ∀ j, (T j).Satisfies w
        (ε/(1-ε) + (1-((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
          (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1))) := by
  have hs : Tendsto (fun N => ∑ j, (T j).rate N) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => (T j).rate_tendsto)
  have hr := (rankRate_tendsto M α β δ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hd' := ((SixTable.badPairs_rate_tendsto hd1 hτ0).add hr).const_mul ε
  have hh : Tendsto (fun N : ℕ => (∑ j, (T j).rate N) +
      ε*(60*(N:ℝ)^2*Real.exp (-τ^2*(N:ℝ)^(1-δ)/4) + rankRate M α β δ N)) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero,Function.comp_def] using hs.add hd'
  have he := (hh.comp alphabet_size_tendsto).eventually (gt_mem_nhds hε0)
  let K : ℕ := Finset.univ.sup (fun j => (T j).threshold)
  have hK := alphabet_size_tendsto.eventually (eventually_ge_atTop K)
  filter_upwards [he,hK] with n hn hN
  exact exists_tables_of_estimate T M n ha hb hd hsmall
    (fun j => (Finset.le_sup (f := fun j => (T j).threshold) (Finset.mem_univ j)).trans hN)
    hε0 hε1 hτ0 hτ2 hn

/-- Arbitrary finite conditional sampling data and the literal bounded-rank
producer are simultaneous on arbitrarily large original signed alphabets. -/
theorem eventually_exists_tables_precision {J : Type*} [Fintype J]
    (T : J → ConditionalTest) (M : ℕ) {α β δ ξ τ : ℝ}
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (hd1 : δ < 1)
    (hsmall : ∀ j, ((T j).k+1:ℝ)*(β+90*δ) ≤ 1/2)
    (hξ : 0 < ξ) (hτ0 : 0 < τ) (hτ2 : τ ≤ 2) :
    ∀ᶠ n in atTop, ∃ (w : TableModel.Entry (A := SymmetricAlphabet n) rowSupport → Bool)
      (d : (Fin 6 → SymmetricAlphabet n) → Bool),
      ¬SixTable.BadPairs δ τ d ∧ GoodUpTo M α β δ (Sum.elim w d) ∧
      ∀ j, (T j).Satisfies w ξ := by
  let ε : ℝ := min (ξ/4) (1/4)
  have he0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have he4 : ε ≤ 1/4 := min_le_right _ _
  have he1 : ε < 1 := lt_of_le_of_lt he4 (by norm_num)
  have hq : ε/(1-ε) ≤ ξ/2 := by
    have hε : ε ≤ ξ/4 := min_le_left _ _
    have hh : ε/(1-ε) ≤ 2*ε := by
      rw [div_le_iff₀ (by linarith : 0 < 1-ε)]
      nlinarith
    exact hh.trans (by linarith)
  have hd' : ∀ᶠ n in atTop, ∀ j : J,
      1 - ((Fintype.card (SymmetricAlphabet n)).descFactorial ((T j).k+1):ℝ)/
        (Fintype.card (SymmetricAlphabet n):ℝ)^((T j).k+1) < ξ/2 := by
    rw [Filter.eventually_all]
    intro j
    exact ((FiniteLaw.distinct_error_tendsto ((T j).k+1)).comp alphabet_size_tendsto).eventually
      (gt_mem_nhds (by positivity))
  filter_upwards [eventually_exists_tables T M ha hb hd hd1 hsmall he0 he1 hτ0 hτ2,hd'] with n hn hdn
  obtain ⟨w,d,hw,hR,ht⟩ := hn
  refine ⟨w,d,hw,hR,fun j => (T j).satisfies_mono (ht j) ?_⟩
  linarith [hdn j]

end Occurrences

/-- A genuine stage with a bounded-rank certificate for the same arrays. The
size cutoff is arbitrary and fixed before the alphabet is selected. -/
structure RankSamplingStage (m M : ℕ) (φ : ℝ) extends SamplingStage m φ where
  rank_good : Occurrences.GoodUpTo M φ (8*φ) φ (Sum.elim master six)

lemma exists_rankSamplingStage (m M : ℕ) {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1)
    (hsmall : (m+1:ℝ)*(98*φ) ≤ 1/2) : Nonempty (RankSamplingStage m M φ) := by
  let T (j : ConditionalData × Fin (m+1)) := j.1.test j.2.val
  have hest : ∀ j, ((T j).k+1:ℝ)*(8*φ+90*φ) ≤ 1/2 := by
    intro j
    have hk : ((T j).k+1:ℝ) ≤ m+1 := by
      dsimp [T,ConditionalData.test]
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ j.2.isLt)
    have hh := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 98*φ)
    nlinarith
  have hh := Occurrences.eventually_exists_tables_precision T M hφ.le (by linarith : 7*φ ≤ 8*φ)
    hφ.le hφ1 hest (stageError_pos m) (stageError_pos m)
    ((stageError_le_third m).trans (by norm_num : (1:ℝ)/3 ≤ 2))
  obtain ⟨n,hn,hw⟩ := (hh.and (eventually_ge_atTop m)).exists
  obtain ⟨w,d,hd,hR,ht⟩ := hn
  have ht' (p : ConditionalData) (k : ℕ) (hk : k ≤ m) :
      (p.test k).Satisfies w (stageError m) := ht (p,⟨k,Nat.lt_succ_of_le hk⟩)
  have he : Nonempty Field := Fintype.card_pos_iff.mp (by rw [card_fields]; decide)
  let e : Field := Classical.choice he
  have hne := (ht' (singletonData e) 0 (Nat.zero_le _)).choose
  exact ⟨⟨⟨n,hw,w,d,hne,hd,ht'⟩,hR⟩⟩

/-- Diagonalizing in the desired diagram size imposes no additional sampling
hypothesis, and does not change the defining presentation. -/
def actualRankSamplingStage (M : ℕ → ℕ) (m : ℕ) : RankSamplingStage m (M m) (samplingParameter m) :=
  Classical.choice (exists_rankSamplingStage m (M m) (samplingParameter_pos m)
    (samplingParameter_lt_one m) (samplingParameter_small m))

def rankSelectedStage (M : ℕ → ℕ) (m : ℕ) : SamplingStage m (samplingParameter m) :=
  (actualRankSamplingStage M m).toSamplingStage

lemma rankSelectedStage_good (M : ℕ → ℕ) (m : ℕ) :
    Occurrences.GoodUpTo (M m) (samplingParameter m) (8*samplingParameter m) (samplingParameter m)
      (Sum.elim (rankSelectedStage M m).master (rankSelectedStage M m).six) :=
  (actualRankSamplingStage M m).rank_good

end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
