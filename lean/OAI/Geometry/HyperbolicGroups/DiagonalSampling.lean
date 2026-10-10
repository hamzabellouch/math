import Mathlib
import OAI.Geometry.HyperbolicGroups.FiniteSampling

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

def stageError (m : ℕ) : ℝ := 1 / (m+4:ℝ)
lemma stageError_pos (m : ℕ) : 0 < stageError m := by unfold stageError; positivity
lemma stageError_le_third (m : ℕ) : stageError m ≤ 1/3 := by
  unfold stageError
  apply one_div_le_one_div_of_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) m]
lemma stageError_tendsto : Tendsto stageError atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => m+4) atTop atTop :=
    tendsto_atTop_mono (f := id) (fun m => Nat.le_add_right m 4) tendsto_id
  change Tendsto (fun m : ℕ => (1:ℝ) / ((m:ℝ)+4)) atTop (𝓝 0)
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp ht

/-- All finitely many requested tests and the actual six-letter array at one
stage. This is selected below, not an assumption about a desired action. -/
structure SamplingStage (m : ℕ) (δ : ℝ) where
  size : ℕ
  large : m ≤ size
  master : TableModel.Entry (A := SymmetricAlphabet size) rowSupport → Bool
  six : (Fin 6 → SymmetricAlphabet size) → Bool
  nonempty : Nonempty (StarModel.Matches rowSupport master)
  six_good : ¬SixTable.BadPairs δ (stageError m) six
  tests : ∀ p : ConditionalData, ∀ k : ℕ, k ≤ m → (p.test k).Satisfies master (stageError m)

lemma exists_samplingStage (m : ℕ) {φ : ℝ} (hφ : 0 < φ) (hφ1 : φ < 1)
    (hsmall : (m+1:ℝ)*(98*φ) ≤ 1/2) : Nonempty (SamplingStage m φ) := by
  let T (j : ConditionalData × Fin (m+1)) := j.1.test j.2.val
  have hest : ∀ j, ((T j).k+1:ℝ)*(8*φ+90*φ) ≤ 1/2 := by
    intro j
    have hk : ((T j).k+1:ℝ) ≤ m+1 := by
      dsimp [T,ConditionalData.test]
      exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ j.2.isLt)
    have hh := mul_le_mul_of_nonneg_right hk (by positivity : 0 ≤ 98*φ)
    nlinarith
  have hh := eventually_exists_tables_precision T hφ.le (by linarith : 7*φ ≤ 8*φ)
    hφ.le hφ1 hest (stageError_pos m) (stageError_pos m)
    ((stageError_le_third m).trans (by norm_num : (1:ℝ)/3 ≤ 2))
  obtain ⟨n,hn,hw⟩ := (hh.and (eventually_ge_atTop m)).exists
  obtain ⟨w,d,hd,ht⟩ := hn
  have ht' (p : ConditionalData) (k : ℕ) (hk : k ≤ m) :
      (p.test k).Satisfies w (stageError m) := ht (p,⟨k,Nat.lt_succ_of_le hk⟩)
  have he : Nonempty Field := Fintype.card_pos_iff.mp (by rw [card_fields]; decide)
  let e : Field := Classical.choice he
  have hne := (ht' (singletonData e) 0 (Nat.zero_le _)).choose
  exact ⟨⟨n,hw,w,d,hne,hd,ht'⟩⟩


end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
