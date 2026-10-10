import OAI.Probability.SLE.Mass.HilbertConvexTails
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace OAI

/-! The countable deterministic extraction in `mass:construction`.
A weighted Hilbert sum ensures the same finite convex coefficients work
for every member of the countable family of bounded test sequences. -/

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace SLEExactGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma geometric_half_mem_l2 : Memℓp (fun j : ℕ => (1/2 : ℝ)^j) 2 := by
  apply memℓp_gen
  have h := summable_geometric_of_abs_lt_one (show |(1/4 : ℝ)| < 1 by norm_num)
  convert h using 1
  funext j
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) j)]
  rw [pow_two,← mul_pow]
  norm_num

theorem exists_simultaneous_convex_tail_combinations (u : ℕ → ℕ → E)
    (hbound : ∀ j, ∃ B : ℝ, ∀ n, ‖u n j‖ ≤ B) :
    ∃ x : ℕ → E, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧
      (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Summable (fun n => ‖(∑ i ∈ s n, w n i • u (n+i) j) - x j‖)) ∧
      (∀ j, Tendsto (fun n => ∑ i ∈ s n, w n i • u (n+i) j) atTop (𝓝 (x j))) := by
  choose B hB using hbound
  let c : ℕ → ℝ := fun j => (1/2:ℝ)^j / max 1 (B j)
  have hc (j : ℕ) : 0 < c j := by
    apply div_pos (pow_pos (by norm_num) _)
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hsmall (n j : ℕ) : ‖c j • u n j‖ ≤ (1/2:ℝ)^j := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hc j)]
    dsimp only [c]
    have hd : 0 < max 1 (B j) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hh : ‖u n j‖ ≤ max 1 (B j) := (hB j n).trans (le_max_right _ _)
    calc
      (1/2:ℝ)^j / max 1 (B j) * ‖u n j‖ =
          (1/2:ℝ)^j * ‖u n j‖ / max 1 (B j) := by ring
      _ ≤ (1/2:ℝ)^j := (div_le_iff₀ hd).mpr (by gcongr)
  let g : lp (fun _ : ℕ => ℝ) 2 := ⟨_,geometric_half_mem_l2⟩
  let v : ℕ → lp (fun _ : ℕ => E) 2 := fun n =>
    ⟨fun j => c j • u n j,geometric_half_mem_l2.mono (hsmall n)⟩
  have hv (n : ℕ) : ‖v n‖ ≤ ‖g‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro j
    simpa only [g,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) j)] using hsmall n j
  obtain ⟨x,s,w,hw,hs,herror,hconv⟩ := exists_convex_tail_combinations v ‖g‖ hv
  let L (j : ℕ) : lp (fun _ : ℕ => E) 2 →L[ℝ] E :=
    (c j)⁻¹ • lp.evalCLM ℝ (fun _ : ℕ => E) 2 j
  have hL (j n : ℕ) : L j (v n) = u n j := by
    change (c j)⁻¹ • (c j • u n j) = _
    rw [smul_smul,inv_mul_cancel₀ (hc j).ne',one_smul]
  refine ⟨fun j => L j x,s,w,hw,hs,?_,?_⟩
  · intro j
    have hgeo : Summable (fun n : ℕ => ‖L j‖ * (1/2:ℝ)^n) :=
      (summable_geometric_of_abs_lt_one (show |(1/2:ℝ)| < 1 by norm_num)).mul_left _
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hgeo
    intro n
    have hnorm := (L j).le_opNorm ((∑ i ∈ s n, w n i • v (n+i))-x)
    simp only [map_sub,map_sum,map_smul,hL] at hnorm
    have hh : ‖(∑ i ∈ s n, w n i • v (n+i))-x‖ ≤ (1/2:ℝ)^n := by
      simpa only [dist_eq_norm] using (herror n).le
    exact hnorm.trans (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
  · intro j
    have hh := ((L j).continuous.tendsto x).comp hconv
    simpa only [Function.comp_def,map_sum,map_smul,hL] using hh

end SLEExactGauge

end

end OAI
