import OAI.Analysis.MarkovType.SubdivisionInvariantBlocks
import OAI.Analysis.MarkovType.SubdivisionMergeConvex
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

theorem exists_natFraction_close {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hε : 0 < ε) :
    ∃ n j : ℕ, 0 < n ∧ j ≤ n ∧ |θ - (j : ℝ) / (n : ℝ)| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 : ℝ) / ε)
  have hnr : 0 < (n : ℝ) := (one_div_pos.mpr hε).trans hn
  have hn0 : 0 < n := by exact_mod_cast hnr
  let j : ℕ := ⌊(n : ℝ) * θ⌋₊
  have hjn : j ≤ n := by
    apply Nat.floor_le_of_le
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hθ1 hnr.le
  have hjlo : (j : ℝ) ≤ (n : ℝ) * θ :=
    Nat.floor_le (mul_nonneg hnr.le hθ0)
  have hjhi : (n : ℝ) * θ < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : (j : ℝ) / (n : ℝ) ≤ θ := by
    apply (div_le_iff₀ hnr).mpr
    simpa only [mul_comm] using hjlo
  have hgap : θ - (j : ℝ) / (n : ℝ) < 1 / (n : ℝ) := by
    apply (lt_div_iff₀ hnr).mpr
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hnr)]
    linarith
  have he : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnr).mpr
    have h := (div_lt_iff₀ hε).mp hn
    simpa only [mul_comm] using h
  exact ⟨n, j, hn0, hjn, by
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact hgap.trans he⟩

end MarkovSuperreflexivity.Subdivision

namespace MarkovSuperreflexivity.SpreadingModel

open Subdivision

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_sameSign_split (S : SpreadingModel Y) (left right : List ℝ)
    (s θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    S.averagedSeminorm (ofList (left ++ ([θ * s, (1 - θ) * s] ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([s] ++ right))) := by
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      |S.averagedSeminorm (ofList (left ++ ([θ * s, (1 - θ) * s] ++ right))) -
        S.averagedSeminorm (ofList (left ++ ([s] ++ right)))| < ε := by
    let δ : ℝ := ε / (2 * |s| + 1)
    have hden : 0 < 2 * |s| + 1 := by positivity
    have hδ : 0 < δ := div_pos hε hden
    obtain ⟨n, j, hn, hjn, hclose⟩ := exists_natFraction_close hθ0 hθ1 hδ
    let q : ℝ := (j : ℝ) / (n : ℝ)
    have hrat := S.averaged_split_natFraction left right hn hjn s
    have hlip := pair_context_lipschitz S.averagedSeminorm S.averaged_array_upper
      left right (θ * s) ((1 - θ) * s) (q * s) ((1 - q) * s)
    simp only [List.append_assoc] at hlip
    change S.averagedSeminorm (ofList (left ++ ([q * s, (1 - q) * s] ++ right))) = _
      at hrat
    rw [hrat] at hlip
    have he : |θ * s - q * s| + |(1 - θ) * s - (1 - q) * s| =
        2 * |θ - q| * |s| := by
      have h1 : θ * s - q * s = (θ - q) * s := by ring
      have h2 : (1 - θ) * s - (1 - q) * s = -((θ - q) * s) := by ring
      rw [h1, h2, abs_neg, abs_mul]
      ring
    rw [he] at hlip
    have hδε : δ * (2 * |s| + 1) = ε :=
      div_mul_cancel₀ ε (ne_of_gt hden)
    have heps : 2 * δ * |s| < ε := by nlinarith
    have hbound : 2 * |θ - q| * |s| ≤ 2 * δ * |s| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hclose.le (by norm_num)) (abs_nonneg s)
    exact hlip.trans_lt (hbound.trans_lt heps)
  by_contra hne
  have hpos : 0 <
      |S.averagedSeminorm (ofList (left ++ ([θ * s, (1 - θ) * s] ++ right))) -
        S.averagedSeminorm (ofList (left ++ ([s] ++ right)))| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  exact (lt_irrefl _) (hsmall _ hpos)

theorem averaged_merge_context (S : SpreadingModel Y) (left right : List ℝ)
    (a b : ℝ) :
    S.averagedSeminorm (ofList (left ++ ([a + b] ++ right))) ≤
      S.averagedSeminorm (ofList (left ++ ([a, b] ++ right))) := by
  simpa only [List.append_assoc] using
    merge_context_le S.averagedSeminorm S.averaged_array_upper left right
      (fun s θ h0 h1 => by
        simpa only [List.append_assoc] using S.averaged_sameSign_split left right s θ h0 h1)
      a b

end MarkovSuperreflexivity.SpreadingModel

end

end OAI
