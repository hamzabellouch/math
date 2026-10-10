import OAI.Probability.BenjaminiSchramm.CriticalHalfspaceDecay
import Mathlib.Analysis.Subadditive

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology BigOperators

namespace Percolation.BenjaminiSchramm

theorem positive_crossing_exponent (P : ℕ → ℝ) (hP : ∀ n, 0 < P n)
    (hP1 : ∀ n, P n ≤ 1) (hP0 : P 0 = 1)
    (hmul : ∀ m n, P m*P n ≤ P (m+n)) :
    ∃ α : ℝ, 0 ≤ α ∧
      (∀ n : ℕ, P n ≤ Real.exp (-α*n)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(α+ε)*n) ≤ P n) ∧
      Tendsto (fun n : ℕ => -Real.log (P n)/n) atTop (𝓝 α) := by
  let u : ℕ → ℝ := fun n => -Real.log (P n)
  have hu : Subadditive u := by
    intro m n
    have h := Real.log_le_log (mul_pos (hP m) (hP n)) (hmul m n)
    rw [Real.log_mul (hP m).ne' (hP n).ne'] at h
    dsimp [u]
    linarith
  have hun (n : ℕ) : 0 ≤ u n := neg_nonneg.mpr (Real.log_nonpos (hP n).le (hP1 n))
  have hbdd : BddBelow (Set.range fun n : ℕ => u n/n) :=
    ⟨0,by rintro _ ⟨n,rfl⟩; exact div_nonneg (hun n) (Nat.cast_nonneg n)⟩
  let α := hu.lim
  have hlim : Tendsto (fun n : ℕ => u n/n) atTop (𝓝 α) := hu.tendsto_lim hbdd
  have hα : 0 ≤ α := ge_of_tendsto hlim (Filter.Eventually.of_forall
    (fun n => div_nonneg (hun n) (Nat.cast_nonneg n)))
  refine ⟨α,hα,?_,?_,hlim⟩
  · intro n
    by_cases hn : n = 0
    · simp only [hn,hP0,Nat.cast_zero,mul_zero,Real.exp_zero,le_refl]
    have hr := (le_div_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn) : (0 : ℝ) < n)).mp
      (hu.lim_le_div hbdd hn)
    have he := Real.exp_le_exp.mpr (show Real.log (P n) ≤ -α*n by dsimp [u] at hr; nlinarith)
    rwa [Real.exp_log (hP n)] at he
  · intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (lt_add_of_pos_right α hε)))
    let f : ℕ → ℝ := fun n => P n*Real.exp ((α+ε)*n)
    obtain ⟨i,hi,himin⟩ := Finset.exists_min_image (Finset.range (N+1)) f
      ⟨0,Finset.mem_range.mpr (Nat.succ_pos N)⟩
    let c := min 1 (f i)
    have hc : 0 < c := lt_min (by norm_num) (mul_pos (hP i) (Real.exp_pos _))
    refine ⟨c,hc,fun n => ?_⟩
    by_cases hn : n < N+1
    · have hcf : c ≤ f n := (min_le_right _ _).trans (himin n (Finset.mem_range.mpr hn))
      have hh := mul_le_mul_of_nonneg_right hcf (Real.exp_pos (-(α+ε)*n)).le
      have he : Real.exp ((α+ε)*n)*Real.exp (-(α+ε)*n) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
      dsimp [f] at hh
      rwa [mul_assoc,he,mul_one] at hh
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hr := (div_lt_iff₀ hnpos).mp (hN n (by omega))
      have hh : -(α+ε)*(n : ℝ) ≤ Real.log (P n) := by dsimp [u] at hr; linarith
      have he := Real.exp_le_exp.mpr hh
      rw [Real.exp_log (hP n)] at he
      exact (mul_le_of_le_one_left (Real.exp_nonneg _) (min_le_left _ _)).trans he

end Percolation.BenjaminiSchramm

end

end OAI
