import OAI.Analysis.MarkovType.CoefficientBlockPartition
import OAI.Analysis.MarkovType.CoefficientFunctional

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

def selectedBlockCuts (e : Fin m ↪o Fin n) (j : Fin (m + 1)) : ℕ :=
  if hj : j.val < m then
    if j.val = 0 then 0 else (e ⟨j.val, hj⟩).val
  else n

@[simp] theorem selectedBlockCuts_castSucc (e : Fin m ↪o Fin n) (j : Fin m) :
    selectedBlockCuts e j.castSucc = if j.val = 0 then 0 else (e j).val := by
  simp [selectedBlockCuts, j.is_lt]

@[simp] theorem selectedBlockCuts_last (e : Fin m ↪o Fin n) :
    selectedBlockCuts e (Fin.last m) = n := by
  simp [selectedBlockCuts]

theorem selectedBlockCuts_zero (e : Fin m ↪o Fin n) (hm : 0 < m) :
    selectedBlockCuts e 0 = 0 := by
  simp [selectedBlockCuts, hm]

theorem monotone_selectedBlockCuts (e : Fin m ↪o Fin n) :
    Monotone (selectedBlockCuts e) := by
  intro a b hab
  change a.val ≤ b.val at hab
  by_cases ha : a.val < m
  · by_cases ha0 : a.val = 0
    · have hz : selectedBlockCuts e a = 0 := by
        simp only [selectedBlockCuts, dite_eq_left ha, ite_eq_left ha0]
      rw [hz]
      exact Nat.zero_le _
    · by_cases hb : b.val < m
      · have hb0 : b.val ≠ 0 := by omega
        simp only [selectedBlockCuts, dite_eq_left ha, dite_eq_left hb,
          ite_eq_right ha0, ite_eq_right hb0]
        exact e.monotone
          (show (⟨a.val, ha⟩ : Fin m) ≤ ⟨b.val, hb⟩ from hab)
      · simp only [selectedBlockCuts, dite_eq_left ha, dite_eq_right hb, ite_eq_right ha0]
        exact (e ⟨a.val, ha⟩).is_lt.le
  · have hb : ¬ b.val < m := by omega
    simp only [selectedBlockCuts, dite_eq_right ha, dite_eq_right hb, le_refl]

theorem selected_mem_block (e : Fin m ↪o Fin n) (j : Fin m) :
    selectedBlockCuts e j.castSucc ≤ (e j).val ∧
      (e j).val < selectedBlockCuts e j.succ := by
  constructor
  · rw [selectedBlockCuts_castSucc]
    split
    · exact Nat.zero_le _
    · exact le_rfl
  · by_cases hj : j.val + 1 < m
    · have hj0 : j.val + 1 ≠ 0 := by omega
      have he : (e j).val < (e ⟨j.val + 1, hj⟩).val :=
        e.strictMono (show j < (⟨j.val + 1, hj⟩ : Fin m) from Nat.lt_succ_self _)
      simpa [selectedBlockCuts, hj, hj0] using he
    · simp [selectedBlockCuts, hj]

def selectedConsecutiveBlocks (e : Fin m ↪o Fin n) (x : Fin n → E) : Fin m → E :=
  consecutiveBlocks x (selectedBlockCuts e)

theorem sum_selectedConsecutiveBlocks (hm : 0 < m) (e : Fin m ↪o Fin n)
    (x : Fin n → E) :
    (∑ j, selectedConsecutiveBlocks e x j) = ∑ i, x i :=
  sum_consecutiveBlocks x (selectedBlockCuts e) (monotone_selectedBlockCuts e)
    (selectedBlockCuts_zero e hm) (selectedBlockCuts_last e)

theorem CoefficientBasic.selectedConsecutiveBlocks {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (e : Fin m ↪o Fin n) :
    CoefficientBasic K (selectedConsecutiveBlocks e x) :=
  hx.consecutiveBlocks (selectedBlockCuts e) (monotone_selectedBlockCuts e)
    (selectedBlockCuts_last e).le

theorem norm_selected_le_two_mul_block {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (e : Fin m ↪o Fin n) (j : Fin m) :
    ‖x (e j)‖ ≤ (2 * K) * ‖selectedConsecutiveBlocks e x j‖ := by
  classical
  let y : Fin n → E := fun i =>
    if selectedBlockCuts e j.castSucc ≤ i.val ∧ i.val < selectedBlockCuts e j.succ
      then x i else 0
  have hy : CoefficientBasic K y := by
    simpa only [ite_smul, one_smul, zero_smul] using
      hx.smul (fun i => if selectedBlockCuts e j.castSucc ≤ i.val ∧
        i.val < selectedBlockCuts e j.succ then (1 : ℝ) else 0)
  have h := hy.norm_entry_le (e j)
  simpa only [y, ite_eq_left (selected_mem_block e j), selectedConsecutiveBlocks,
    consecutiveBlocks] using h

end MarkovSuperreflexivity

end

end OAI
