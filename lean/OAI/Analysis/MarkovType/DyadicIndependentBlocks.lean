import OAI.Analysis.MarkovType.DyadicBlockCoordinates
import OAI.Analysis.MarkovType.FiniteDyadicMartingale

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dyadicIndependentBlocks {N : ℕ} (m : ℕ) (c : ℝ) (φ : DyadicAtom N → E) :
    DyadicAtom (m * N) → E
  | .inl _ => 0
  | .inr ⟨j, α⟩ => c • dyadicCoefficient φ (finProdFinEquiv.symm j).2
      (dyadicBlockPrefix j α)

@[simp] theorem dyadicIndependentBlocks_root {N : ℕ} (m : ℕ) (c : ℝ)
    (φ : DyadicAtom N → E) : dyadicRoot (dyadicIndependentBlocks m c φ) = 0 := rfl

theorem dyadicIndependentBlocks_increment {m N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (j : Fin (m * N)) (ω : DyadicWord (m * N)) :
    dyadicIncrement (dyadicIndependentBlocks m c φ) j ω =
      c • dyadicIncrement φ (finProdFinEquiv.symm j).2
        (dyadicBlockEquiv m N ω (finProdFinEquiv.symm j).1) := by
  simp only [dyadicIncrement, dyadicCoefficient, dyadicIndependentBlocks,
    dyadicBlockPrefix_prefix]
  have hbit : ω j = dyadicBlockEquiv m N ω (finProdFinEquiv.symm j).1
      (finProdFinEquiv.symm j).2 := by
    change ω j = ω (finProdFinEquiv (finProdFinEquiv.symm j))
    rw [Equiv.apply_symm_apply]
  rw [hbit]
  module

theorem dyadicIndependentBlocks_increment_pair {m N : ℕ} (c : ℝ)
    (φ : DyadicAtom N → E) (b : Fin m) (i : Fin N) (ω : DyadicWord (m * N)) :
    dyadicIncrement (dyadicIndependentBlocks m c φ) (finProdFinEquiv (b, i)) ω =
      c • dyadicIncrement φ i (dyadicBlockEquiv m N ω b) := by
  simpa only [Equiv.symm_apply_apply] using
    dyadicIndependentBlocks_increment c φ (finProdFinEquiv (b, i)) ω

theorem dyadicIndependentBlocks_increment_moment {m N : ℕ} (c p : ℝ)
    (φ : DyadicAtom N → E) (b : Fin m) (i : Fin N) :
    finiteMoment (dyadicLaw (m * N)).mass p
      (dyadicIncrement (dyadicIndependentBlocks m c φ) (finProdFinEquiv (b, i))) =
      |c| ^ p * finiteMoment (dyadicLaw N).mass p (dyadicIncrement φ i) := by
  change (dyadicLaw (m * N)).expect (fun ω =>
    ‖dyadicIncrement (dyadicIndependentBlocks m c φ) (finProdFinEquiv (b, i)) ω‖ ^ p) = _
  simp_rw [dyadicIndependentBlocks_increment_pair]
  rw [dyadicBlock_expect_coord b (fun ω => ‖c • dyadicIncrement φ i ω‖ ^ p)]
  simp only [FiniteLaw.expect, finiteMoment, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem dyadicIndependentBlocks_inputMoment {N : ℕ} (m : ℕ) (c : ℝ)
    (φ : DyadicAtom N → E) (hroot : dyadicRoot φ = 0) {p : ℝ} (hp : 0 < p) :
    finiteMoment dyadicInputWeight p (dyadicIndependentBlocks m c φ) =
      |c| ^ p * (m : ℝ) * finiteMoment dyadicInputWeight p φ := by
  rw [dyadicInputMoment, dyadicIndependentBlocks_root, norm_zero, Real.zero_rpow hp.ne',
    zero_add, dyadicInputMoment, hroot, norm_zero, Real.zero_rpow hp.ne', zero_add]
  rw [← (finProdFinEquiv : Fin m × Fin N ≃ Fin (m * N)).sum_comp
    (fun j => finiteMoment (dyadicLaw (m * N)).mass p
      (dyadicIncrement (dyadicIndependentBlocks m c φ) j))]
  rw [Fintype.sum_prod_type]
  simp_rw [dyadicIndependentBlocks_increment_moment]
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem dyadicIndependentBlocks_process {m N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (b : Fin m) (j : ℕ) (hj : j ≤ N)
    (ω : DyadicWord (m * N)) :
    dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val + j) ω =
      dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val) ω +
        c • dyadicProcess φ j (dyadicBlockEquiv m N ω b) := by
  induction j with
  | zero => simp only [dyadicProcess_zero, hroot, smul_zero, add_zero]
  | succ j ih =>
      have hjN : j < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have hjle : j ≤ N := Nat.le_of_lt hjN
      let i : Fin N := ⟨j, hjN⟩
      have hindex : N * b.val + j < m * N := by
        have h := (finProdFinEquiv (b, i)).is_lt
        change j + N * b.val < m * N at h
        simpa only [Nat.add_comm] using h
      have heq : (⟨N * b.val + j, hindex⟩ : Fin (m * N)) = finProdFinEquiv (b, i) := by
        apply Fin.ext
        change N * b.val + j = j + N * b.val
        omega
      rw [show N * b.val + (j + 1) = (N * b.val + j) + 1 by omega]
      simp only [dyadicProcess, dite_eq_left hindex, ih hjle, heq,
        dyadicIndependentBlocks_increment_pair, dite_eq_left hjN]
      change _ = _ + c • (_ + dyadicIncrement φ i _)
      module

theorem dyadicIndependentBlocks_boundary {m N : ℕ} (c : ℝ) (φ : DyadicAtom N → E)
    (hroot : dyadicRoot φ = 0) (b : Fin m) (ω : DyadicWord (m * N)) :
    c • dyadicSynthesis N φ (dyadicBlockEquiv m N ω b) =
      dyadicProcess (dyadicIndependentBlocks m c φ) (N * (b.val + 1)) ω -
        dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val) ω := by
  have h := dyadicIndependentBlocks_process c φ hroot b N (Nat.le_refl N) ω
  rw [Nat.mul_add, Nat.mul_one]
  change c • dyadicProcess φ N _ = _
  rw [h, add_sub_cancel_left]

theorem dyadicIndependentBlocks_copy_norm_le {m N : ℕ} (c : ℝ)
    (φ : DyadicAtom N → E) (hroot : dyadicRoot φ = 0) (ω : DyadicWord (m * N))
    {u : ℝ} (hbound : ∀ j : ℕ, j ≤ m * N →
      ‖dyadicProcess (dyadicIndependentBlocks m c φ) j ω‖ ≤ u) (b : Fin m) :
    ‖c • dyadicSynthesis N φ (dyadicBlockEquiv m N ω b)‖ ≤ 2 * u := by
  rw [dyadicIndependentBlocks_boundary c φ hroot]
  have hstart : N * b.val ≤ m * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left N (Nat.le_of_lt b.is_lt)
  have hend : N * (b.val + 1) ≤ m * N := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left N (Nat.succ_le_of_lt b.is_lt)
  calc
    _ ≤ ‖dyadicProcess (dyadicIndependentBlocks m c φ) (N * (b.val + 1)) ω‖ +
        ‖dyadicProcess (dyadicIndependentBlocks m c φ) (N * b.val) ω‖ := norm_sub_le _ _
    _ ≤ u + u := add_le_add (hbound _ hend) (hbound _ hstart)
    _ = 2 * u := by ring

def dyadicCopyScale (m : ℕ) (p : ℝ) : ℝ := ((m : ℝ) ^ (1 / p))⁻¹

theorem dyadicCopyScale_pos {m : ℕ} (hm : 0 < m) (p : ℝ) :
    0 < dyadicCopyScale m p := inv_pos.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _)

theorem dyadicCopyScale_moment {m : ℕ} (hm : 0 < m) {p : ℝ} (hp : 0 < p) :
    |dyadicCopyScale m p| ^ p * (m : ℝ) = 1 := by
  rw [abs_of_pos (dyadicCopyScale_pos hm p), dyadicCopyScale,
    Real.inv_rpow (Real.rpow_nonneg (Nat.cast_nonneg m) _) p, one_div,
    Real.rpow_inv_rpow (Nat.cast_nonneg m) hp.ne', inv_mul_cancel₀]
  exact_mod_cast hm.ne'

theorem dyadicIndependentBlocks_normalized {N m : ℕ} (hm : 0 < m)
    (φ : DyadicAtom N → E) (hroot : dyadicRoot φ = 0) {p : ℝ} (hp : 0 < p) :
    finiteMoment dyadicInputWeight p (dyadicIndependentBlocks m (dyadicCopyScale m p) φ) =
      finiteMoment dyadicInputWeight p φ := by
  rw [dyadicIndependentBlocks_inputMoment m _ φ hroot hp, dyadicCopyScale_moment hm hp,
    one_mul]

end MarkovSuperreflexivity

end

end OAI
