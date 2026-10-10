import OAI.Analysis.MarkovType.FiniteSelectionCompression
import OAI.Analysis.MarkovType.FiniteGeometricBands
import OAI.Analysis.MarkovType.FiniteMartingaleTransport
import OAI.Analysis.MarkovType.FiniteL2
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

variable {Ω E : Type*} [sectionFintypeΩ : Fintype Ω]
variable [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]

theorem sum_Icc_one_eq_sum_range_succ {V : Type*} [AddCommMonoid V]
    (f : ℕ → V) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ j ∈ Finset.range N, f (j + 1) := by
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.succ_eq_succ, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_comm 1]

omit sectionFintypeΩ in
theorem selectionCount_eq_card_filter_Icc [Fintype Ω] (N : ℕ) (B : ℕ → Ω → Prop) (ω : Ω) :
    selectionCount N B ω = ((Finset.Icc 1 N).filter (fun n => B n ω)).card := by
  have hcount : selectionCount N B ω =
      ((Finset.range (N + 1)).filter (selectionPredicate N B ω)).card := by
    exact Nat.count_eq_card_filter_range (selectionPredicate N B ω) (N + 1)
  have hsets : (Finset.range (N + 1)).filter (selectionPredicate N B ω) =
      (Finset.Icc 1 N).filter (fun n => B n ω) := by
    apply Finset.ext
    intro n
    constructor
    · intro hn
      have hselect : selectionPredicate N B ω n := (Finset.mem_filter.mp hn).2
      change 0 < n ∧ n ≤ N ∧ B n ω at hselect
      rcases hselect with ⟨hpos, hN, hB⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hN⟩, hB⟩
    · intro hn
      obtain ⟨hnIcc, hB⟩ := Finset.mem_filter.mp hn
      obtain ⟨hpos, hN⟩ := Finset.mem_Icc.mp hnIcc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hN), ?_⟩
      change 0 < n ∧ n ≤ N ∧ B n ω
      exact ⟨by omega, hN, hB⟩
  exact hcount.trans (congrArg Finset.card hsets)

theorem finiteUpperL2_band_bound {a r χ : ℝ} (ha : 0 < a)
    (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N k : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖))
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ 1) :
    finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N,
      if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0) ≤
      χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
  let B : ℕ → Ω → Prop := fun n ω => dyadicMagnitudeBand k (‖d n ω‖ ^ a)
  let J : ℕ := 2 ^ (k + 1) - 1
  have hB : ∀ n, 0 < n → n ≤ N → ∀ {ω η},
      (F.part (n - 1)).r ω η → (B n ω ↔ B n η) := by
    intro n hn hnN ω η hωη
    dsimp only [B]
    have hnorm : ‖d n ω‖ = ‖d n η‖ := hpred n hn hnN hωη
    rw [hnorm]
  have hcount (ω : Ω) : selectionCount N B ω ≤ J := by
    rw [selectionCount_eq_card_filter_Icc]
    have hc := dyadicMagnitudeBand_card_lt (Finset.Icc 1 N) (fun n => ‖d n ω‖ ^ a)
      (fun n _ => Real.rpow_nonneg (norm_nonneg _) a) (henergy ω) k
    change ((Finset.Icc 1 N).filter (fun n => dyadicMagnitudeBand k (‖d n ω‖ ^ a))).card
      ≤ 2 ^ (k + 1) - 1
    omega
  have hC : 0 ≤ ((1 / 2 : ℝ) ^ k) ^ (1 / a) :=
    Real.rpow_nonneg (pow_nonneg (by norm_num) k) _
  have hM := F.selectionProcess_isMartingaleUpTo μ N B d hB hadapt hzero J
  have hd : ∀ j, j ≤ J →
      finiteL2Norm μ (finiteDifference (selectionProcess N B d) j) ≤
        ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
    intro j hj
    apply finiteL2Norm_le_of_pointwise μ _ hC
    intro ω
    cases j with
    | zero => simpa only [finiteDifference_zero, selectionProcess_zero, norm_zero] using hC
    | succ j =>
      exact norm_finiteDifference_selectionProcess_le N B d hC
        (fun n hn hnN η hnB => norm_le_band_bound ha hnB) j ω
  have h := hUpper.apply μ (F.selectionFiltration N B hB)
    (selectionProcess N B d) J (((1 / 2 : ℝ) ^ k) ^ (1 / a)) hC hM hd
  have hterminal : selectionProcess N B d J = fun ω => ∑ n ∈ Finset.Icc 1 N,
      if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := by
    funext ω
    exact selectionProcess_eq_sum N B d J ω (hcount ω)
  have hJ : J + 1 = 2 ^ (k + 1) := by
    have hp : 0 < 2 ^ (k + 1) := pow_pos (by decide : (0 : ℕ) < 2) _
    dsimp only [J]
    omega
  rw [hterminal] at h
  have hJreal : (J + 1 : ℝ) = ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hJ
  rwa [hJreal] at h

def boundedEnergyConstant (a r χ : ℝ) : ℝ :=
  (χ * (2 : ℝ) ^ (1 / r)) / (1 - bandGeometricRatio a r)

theorem boundedEnergyConstant_nonneg {a r χ : ℝ}
    (ha : 0 < a) (har : a < r) (hχ : 0 ≤ χ) :
    0 ≤ boundedEnergyConstant a r χ :=
  div_nonneg (mul_nonneg hχ (Real.rpow_nonneg (by norm_num) _))
    (sub_nonneg.mpr (bandGeometricRatio_lt_one ha har).le)

omit sectionNormedSpaceℝE in
theorem finite_band_decomposition [NormedSpace ℝ E] {a : ℝ} (_ha : 0 < a)
    (d : ℕ → Ω → E) (N : ℕ)
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ 1) :
    ∃ K : ℕ, ∀ ω,
      (∑ n ∈ Finset.Icc 1 N, d n ω) =
        ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.Icc 1 N,
          if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := by
  classical
  let w : (Ω × ↥(Finset.Icc 1 N)) → ℝ := fun z => ‖d z.2.val z.1‖ ^ a
  have hw : ∀ z, w z ≤ 1 := by
    intro z
    exact (Finset.single_le_sum
      (fun n _ => Real.rpow_nonneg (norm_nonneg (d n z.1)) a) z.2.property).trans (henergy z.1)
  obtain ⟨K, hK⟩ := finite_dyadicMagnitudeBand_cutoff w hw
  refine ⟨K, ?_⟩
  intro ω
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : d n ω = 0
  · simp only [hd, ite_self, Finset.sum_const_zero]
  · have hwpos : 0 < w (ω, ⟨n, hn⟩) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hd) a
    obtain ⟨k, hkK, hband⟩ := hK (ω, ⟨n, hn⟩) hwpos
    have hk : k ∈ Finset.range (K + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hkK)
    change dyadicMagnitudeBand k (‖d n ω‖ ^ a) at hband
    symm
    calc
      _ = if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := by
        apply Finset.sum_eq_single k
        · intro l hl hlk
          apply ite_eq_right
          intro hlband
          exact hlk (dyadicMagnitudeBand_unique hlband hband)
        · intro hnot
          exact (hnot hk).elim
      _ = d n ω := ite_eq_left hband

theorem finiteUpperL2_bounded_energy {a r χ : ℝ} (ha : 0 < a) (har : a < r)
    (hχ : 0 ≤ χ) (hUpper : FiniteUpperL2 E r χ) (μ : FiniteLaw Ω)
    (F : FinitePartitionFiltration Ω) (d : ℕ → Ω → E) (N : ℕ)
    (hadapt : ∀ n, 0 < n → n ≤ N → F.AdaptedAt n (d n))
    (hzero : ∀ n, 0 < n → n ≤ N → HasZeroConditionalSum μ (F.part (n - 1)) (d n))
    (hpred : ∀ n, 0 < n → n ≤ N → F.AdaptedAt (n - 1) (fun ω => ‖d n ω‖))
    (henergy : ∀ ω, (∑ n ∈ Finset.Icc 1 N, ‖d n ω‖ ^ a) ≤ 1) :
    finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N, d n ω) ≤
      boundedEnergyConstant a r χ := by
  obtain ⟨K, hK⟩ := finite_band_decomposition ha d N henergy
  have heq : (fun ω => ∑ n ∈ Finset.Icc 1 N, d n ω) =
      fun ω => ∑ k ∈ Finset.range (K + 1), ∑ n ∈ Finset.Icc 1 N,
        if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0 := funext hK
  rw [heq]
  calc
    _ ≤ ∑ k ∈ Finset.range (K + 1),
        finiteL2Norm μ (fun ω => ∑ n ∈ Finset.Icc 1 N,
          if dyadicMagnitudeBand k (‖d n ω‖ ^ a) then d n ω else 0) :=
      finiteL2Norm_sum_le μ _ _
    _ ≤ ∑ k ∈ Finset.range (K + 1),
        χ * ((2 ^ (k + 1) : ℕ) : ℝ) ^ (1 / r) * ((1 / 2 : ℝ) ^ k) ^ (1 / a) := by
      apply Finset.sum_le_sum
      intro k hk
      exact finiteUpperL2_band_bound ha hUpper μ F d N k hadapt hzero hpred henergy
    _ ≤ boundedEnergyConstant a r χ := finite_band_bound ha har hχ (K + 1)

end MarkovSuperreflexivity

end

end OAI
