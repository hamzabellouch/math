import OAI.Analysis.MarkovType.AlternatingNorm
import OAI.Analysis.MarkovType.PrefixBlocks
import OAI.Analysis.MarkovType.PrefixIndicators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def endpointAlternating (M : ℕ) (ell V : ℝ) : C00 :=
  V • (basis 0 - basis (2 * M + 1)) + ell • shift 1 (alternating M)

def collapseTail (i : ℕ) : ℕ := if i = 0 then 0 else 1

theorem collapseTail_monotone : Monotone collapseTail := by
  intro i j hij
  unfold collapseTail
  split_ifs <;> omega

theorem mapDomain_collapseTail_endpointAlternating (M : ℕ) (ell V : ℝ) :
    Finsupp.mapDomain collapseTail (endpointAlternating M ell V) =
      V • (basis 0 - basis 1) := by
  classical
  let T := Finsupp.mapDomain.addMonoidHom collapseTail (M := ℝ)
  have houter : Finsupp.mapDomain collapseTail (basis 0 - basis (2 * M + 1)) =
      basis 0 - basis 1 := by
    change T (basis 0 - basis (2 * M + 1)) = _
    rw [map_sub]
    simp [T, basis, collapseTail]
  have hinner : Finsupp.mapDomain collapseTail (shift 1 (alternating M)) = 0 := by
    rw [shift_alternating]
    change T (∑ j ∈ Finset.range M,
      (basis (1 + 2 * j) - basis (1 + (2 * j + 1)))) = 0
    simp [map_sum, map_sub, T, basis, collapseTail]
  rw [endpointAlternating, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    Finsupp.mapDomain_smul, houter, hinner, smul_zero, add_zero]

theorem endpointAlternating_supportedBelow (M : ℕ) (ell V : ℝ) :
    SupportedBelow (endpointAlternating M ell V) (2 * M + 2) := by
  intro i hi
  have hi0 : i ≠ 0 := by omega
  have hilast : 2 * M + 1 ≠ i := by omega
  have hshift : shift 1 (alternating M) i = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, i = 1 + j := ⟨i - 1, by omega⟩
    rw [shift_apply_add, alternating_apply, ite_eq_right]
    omega
  simp [endpointAlternating, basis, hi0, hilast, hshift]

theorem prefixCut_shift_alternating_odd (M j : ℕ) :
    prefixCut (shift 1 (alternating M)) (2 * j + 1) = 0 := by
  rw [shift_alternating, prefixCut_finset_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [prefixCut_sub, prefixCut_basis, prefixCut_basis]
  have hiff : 1 + 2 * k < 2 * j + 1 ↔ 1 + (2 * k + 1) < 2 * j + 1 := by omega
  simp only [hiff, sub_self]

theorem prefixCut_shift_alternating_even (M j : ℕ) (hj : j < M) :
    prefixCut (shift 1 (alternating M)) (2 * j + 2) = 1 := by
  classical
  rw [shift_alternating, prefixCut_finset_sum]
  rw [Finset.sum_eq_single j]
  · simp only [prefixCut_sub, prefixCut_basis]
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    norm_num
  · intro k hk hkj
    rw [prefixCut_sub, prefixCut_basis, prefixCut_basis]
    have hiff : 1 + 2 * k < 2 * j + 2 ↔ 1 + (2 * k + 1) < 2 * j + 2 := by omega
    simp only [hiff, sub_self]
  · simp [Finset.mem_range, hj]

theorem prefixCut_endpointAlternating_odd (M j : ℕ) (ell V : ℝ) (hj : j ≤ M) :
    prefixCut (endpointAlternating M ell V) (2 * j + 1) = V := by
  rw [endpointAlternating, prefixCut_add, prefixCut_smul, prefixCut_sub,
    prefixCut_basis, prefixCut_basis, prefixCut_smul,
    prefixCut_shift_alternating_odd]
  rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  ring

theorem prefixCut_endpointAlternating_even (M j : ℕ) (ell V : ℝ) (hj : j < M) :
    prefixCut (endpointAlternating M ell V) (2 * j + 2) = V + ell := by
  rw [endpointAlternating, prefixCut_add, prefixCut_smul, prefixCut_sub,
    prefixCut_basis, prefixCut_basis, prefixCut_smul,
    prefixCut_shift_alternating_even M j hj]
  rw [ite_eq_left (by omega), ite_eq_right (by omega)]
  ring

theorem prefixCut_endpointAlternating_last (M : ℕ) (ell V : ℝ) :
    prefixCut (endpointAlternating M ell V) (2 * M + 2) = 0 := by
  rw [endpointAlternating, prefixCut_add, prefixCut_smul, prefixCut_sub,
    prefixCut_basis, prefixCut_basis, prefixCut_smul]
  have hinner : prefixCut (shift 1 (alternating M)) (2 * M + 2) = 0 := by
    rw [shift_alternating, prefixCut_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hjM := Finset.mem_range.mp hj
    simp only [prefixCut_sub, prefixCut_basis]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
    ring
  rw [ite_eq_left (by omega), ite_eq_left (by omega), hinner]
  ring

end C00

namespace OrderedNorm

theorem endpoint_error_le (N : OrderedNorm) (M : ℕ) (ell V : ℝ) :
    N (V • (C00.basis 0 - C00.basis (2 * M + 1))) ≤
      N (C00.endpointAlternating M ell V) := by
  have h := N.mapDomain_le C00.collapseTail C00.collapseTail_monotone
    (C00.endpointAlternating M ell V)
  rw [C00.mapDomain_collapseTail_endpointAlternating] at h
  simpa only [N.smul, N.basis_sub_basis_norm (show 0 < 2 * M + 1 by omega),
    N.basis_sub_basis_norm (show 0 < 1 by omega)] using h

theorem alternatingNorm_le_twice_endpoint (N : OrderedNorm) (M : ℕ)
    (ell V : ℝ) (hell : 0 ≤ ell) :
    ell * N.alternatingNorm M ≤ 2 * N (C00.endpointAlternating M ell V) := by
  let E := V • (C00.basis 0 - C00.basis (2 * M + 1))
  have heq : ell • C00.shift 1 (C00.alternating M) =
      C00.endpointAlternating M ell V + -E := by
    dsimp [C00.endpointAlternating, E]
    abel
  calc
    ell * N.alternatingNorm M = N (ell • C00.shift 1 (C00.alternating M)) := by
      rw [N.smul, abs_of_nonneg hell, N.shift_alternatingNorm]
    _ = N (C00.endpointAlternating M ell V + -E) := congrArg N heq
    _ ≤ N (C00.endpointAlternating M ell V) + N (-E) := N.add_le _ _
    _ ≤ 2 * N (C00.endpointAlternating M ell V) := by
      rw [N.neg]
      have hE := N.endpoint_error_le M ell V
      change N E ≤ N (C00.endpointAlternating M ell V) at hE
      linarith

theorem endpointAlternating_le_of_prefixes (N : OrderedNorm) (M : ℕ)
    (ell V : ℝ) (c : Fin (2 * M + 2 + 1) → ℕ) (hc : Monotone c)
    (h0 : c 0 = 0) (G : C00) (hG : C00.SupportedBelow G (c (Fin.last _)))
    (hprefix : ∀ j, prefixCut G (c j) =
      prefixCut (C00.endpointAlternating M ell V) j.val) :
    N (C00.endpointAlternating M ell V) ≤ N G := by
  have heq : C00.ofArray (fun j : Fin (2 * M + 2) =>
      prefixCut G (c j.succ) - prefixCut G (c j.castSucc)) =
      C00.endpointAlternating M ell V := by
    have hcoeff : (fun j : Fin (2 * M + 2) =>
        prefixCut G (c j.succ) - prefixCut G (c j.castSucc)) =
        (fun j : Fin (2 * M + 2) => C00.endpointAlternating M ell V j.val) := by
      funext j
      rw [hprefix j.succ, hprefix j.castSucc]
      simp only [Fin.val_succ, Fin.val_castSucc, prefixCut_succ, add_sub_cancel_left]
    rw [hcoeff]
    exact C00.ofArray_restrict _ _ (C00.endpointAlternating_supportedBelow M ell V)
  rw [← heq]
  exact N.prefixBlocks_le c hc h0 G hG

theorem alternatingNorm_six_le_of_prefixes (N : OrderedNorm) (M : ℕ)
    (ell V : ℝ) (hell : 0 ≤ ell)
    (c : Fin (2 * M + 2 + 1) → ℕ) (hc : Monotone c) (h0 : c 0 = 0)
    (G : C00) (hG : C00.SupportedBelow G (c (Fin.last _)))
    (hprefix : ∀ j, prefixCut G (c j) =
      prefixCut (C00.endpointAlternating M ell V) j.val) :
    ell * N.alternatingNorm (2 * M) ≤ 6 * N G := by
  have hQ := N.endpointAlternating_le_of_prefixes M ell V c hc h0 G hG hprefix
  have hinner := N.alternatingNorm_le_twice_endpoint M ell V hell
  have hdouble := mul_le_mul_of_nonneg_left (N.alternatingNorm_twice_le M) hell
  have hNG := N.nonneg G
  nlinarith

theorem alternatingNorm_six_le_of_levels (N : OrderedNorm) (M : ℕ)
    (ell U V : ℝ) (hell : 0 ≤ ell) (hgap : U - V = ell)
    (c : Fin (2 * M + 2 + 1) → ℕ) (hc : Monotone c) (h0 : c 0 = 0)
    (G : C00) (hG : C00.SupportedBelow G (c (Fin.last _)))
    (hlast : prefixCut G (c (Fin.last _)) = 0)
    (hV : ∀ (j : ℕ) (hj : j ≤ M),
      prefixCut G (c ⟨2 * j + 1, by omega⟩) = V)
    (hU : ∀ (j : ℕ) (hj : j < M),
      prefixCut G (c ⟨2 * j + 2, by omega⟩) = U) :
    ell * N.alternatingNorm (2 * M) ≤ 6 * N G := by
  apply N.alternatingNorm_six_le_of_prefixes M ell V hell c hc h0 G hG
  intro i
  by_cases hi0 : i.val = 0
  · have hieq : i = 0 := Fin.ext hi0
    subst i
    simp [h0]
  by_cases hilast : i.val = 2 * M + 2
  · have hieq : i = Fin.last (2 * M + 2) := Fin.ext hilast
    subst i
    simpa only [Fin.val_last, C00.prefixCut_endpointAlternating_last] using hlast
  have hi := i.isLt
  by_cases hparity : i.val % 2 = 0
  · let j := i.val / 2 - 1
    have hj : j < M := by dsimp [j]; omega
    have hij : i.val = 2 * j + 2 := by dsimp [j]; omega
    have hieq : i = ⟨2 * j + 2, by omega⟩ := Fin.ext hij
    rw [hieq, hU j hj, C00.prefixCut_endpointAlternating_even M j ell V hj]
    linarith
  · let j := i.val / 2
    have hj : j ≤ M := by dsimp [j]; omega
    have hij : i.val = 2 * j + 1 := by dsimp [j]; omega
    have hieq : i = ⟨2 * j + 1, by omega⟩ := Fin.ext hij
    rw [hieq, hV j hj, C00.prefixCut_endpointAlternating_odd M j ell V hj]

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
